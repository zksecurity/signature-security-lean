import Signatures.Runtime.BackendSchnorrRawLookup
import Signatures.Runtime.BackendSchnorrRawResetBudget
import Signatures.Runtime.SchnorrRawFork

/-! Native assembly of the retained-tape fork. The pass and selector are actual
backend programs/realizers, so their implementations and stored descriptions
remain part of the assembled controller. Both executions start at the pass's
entry point with the same configuration; only the supplied tape changes. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeFork

open BackendProgram

abbrev choiceTy : Ty CryptoAtom := .pair .bool .nat
abbrev stateTy : Ty CryptoAtom := NativeUniform.stateTy
abbrev passInput (config : Ty CryptoAtom) : Ty CryptoAtom := .pair stateTy config
abbrev passOutput (out : Ty CryptoAtom) : Ty CryptoAtom := .pair out stateTy
abbrev firstTy (config out : Ty CryptoAtom) : Ty CryptoAtom := .pair (passOutput out) config
abbrev selectedTy (config out : Ty CryptoAtom) : Ty CryptoAtom := .pair .nat (firstTy config out)
abbrev freshTy (config out : Ty CryptoAtom) : Ty CryptoAtom := .pair scalar (selectedTy config out)
abbrev carryTy (config out : Ty CryptoAtom) : Ty CryptoAtom := .pair .nat (.pair out config)
abbrev secondCarry (out : Ty CryptoAtom) : Ty CryptoAtom := .pair .nat out
abbrev secondTy (out : Ty CryptoAtom) : Ty CryptoAtom := .pair (passOutput out) (secondCarry out)

def view {A : Type} : Option A → Unit ⊕ A
  | none => .inl ()
  | some a => .inr a

def choice {q : Nat} : Option (Fin q) → Bool × Nat
  | none => (false, 0)
  | some i => (true, i.val)

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here

def startExpression (config : Ty CryptoAtom) : Expr CryptoOp [config] (.pair (passInput config) config) :=
  .pair (.pair (.pair .nil .nil) v0) v0

def firstSelectionExpression (config out : Ty CryptoAtom) :
    Expr CryptoOp [firstTy config out] (.pair out (firstTy config out)) :=
  .pair (.fst (.fst v0)) v0

def firstChoiceExpression (config out : Ty CryptoAtom) :
    Expr CryptoOp [.pair choiceTy (firstTy config out)] (.pair .bool (selectedTy config out)) :=
  .pair (.fst (.fst v0)) (.pair (.snd (.fst v0)) (.snd v0))

def freshExpression (config out : Ty CryptoAtom) :
    Expr CryptoOp [selectedTy config out] (.pair .unit (selectedTy config out)) :=
  .pair .unit v0

def lookupExpression (config out : Ty CryptoAtom) :
    Expr CryptoOp [freshTy config out] (.pair NativeLookup.inputTy (freshTy config out)) :=
  .pair (.pair (.fst (.snd v0)) (.fst (.snd (.fst (.snd (.snd v0)))))) v0

def collisionExpression (config out : Ty CryptoAtom) :
    Expr CryptoOp [.pair NativeLookup.outputTy (freshTy config out)] (.pair .bool (freshTy config out)) :=
  .pair (.branch (.fst (.fst v0))
    (.op .scalarEq (.pair (.snd (.fst v0)) (.fst (.snd v0)))) (.bool false)) (.snd v0)

def resetExpression (config out : Ty CryptoAtom) :
    Expr CryptoOp [freshTy config out] (.pair NativeReset.inputTy (carryTy config out)) :=
  .pair (.pair (.fst (.snd v0)) (.pair (.fst v0) (.snd (.fst (.snd (.snd v0))))))
    (.pair (.fst (.snd v0)) (.pair (.fst (.fst (.snd (.snd v0)))) (.snd (.snd (.snd v0)))))

def secondExpression (config out : Ty CryptoAtom) :
    Expr CryptoOp [.pair stateTy (carryTy config out)] (.pair (passInput config) (secondCarry out)) :=
  .pair (.pair (.fst v0) (.snd (.snd (.snd v0))))
    (.pair (.fst (.snd v0)) (.fst (.snd (.snd v0))))

def secondSelectionExpression (out : Ty CryptoAtom) :
    Expr CryptoOp [secondTy out] (.pair out (secondTy out)) :=
  .pair (.fst (.fst v0)) v0

def finishExpression (out : Ty CryptoAtom) :
    Expr CryptoOp [.pair choiceTy (secondTy out)] (.pair .bool (.pair out out)) :=
  .pair (.branch (.fst (.fst v0))
      (.op .natEq (.pair (.snd (.fst v0)) (.fst (.snd (.snd v0))))) (.bool false))
    (.pair (.snd (.snd (.snd v0))) (.fst (.fst (.snd v0))))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def compileLocal {input output : Ty CryptoAtom} (e : Expr CryptoOp [input] output) :
    Q.Realizer (rep.ty input) (rep.ty output)
      (fun x => e.denote (arithmetic F G₁ G₂ K M cost) (x, ())) :=
  Q.compose (NativeUniform.frame rep data input)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive e)

def chooseLocal {input output : Ty CryptoAtom} (e : Expr CryptoOp [input] (.pair .bool output)) :
    Q.Realizer (rep.ty input) (StepClass.HasSum.sum (rep.ty output) (rep.ty output))
      (fun x => let r := e.denote (arithmetic F G₁ G₂ K M cost) (x, ())
        if r.1 then .inl r.2 else .inr r.2) :=
  Q.compose (compileLocal rep data cost primitive e) (data.select (rep.ty output))

def reject (input out : Ty CryptoAtom) :
    Q.Realizer (rep.ty input) (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out)))
      (fun _ => .inl ()) :=
  Q.compose (data.unit (rep.ty input)) (QS.inl rep.data.unit (rep.ty (.pair out out)))

variable {iface : Interface (C := C) unifSpec} {config out : Ty CryptoAtom}
  {select : out.Value (cryptoBase F G₁ G₂ K M) → Bool × Nat}
  (selector : Q.Realizer (rep.ty out) (rep.ty choiceTy) select)
  (pass : Code Q unifSpec iface (rep.ty (passInput config)) (rep.ty (passOutput out)))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def replay : Code Q unifSpec iface (rep.ty (freshTy config out))
    (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) :=
  .seq (.atomic (compileLocal rep data cost primitive (resetExpression config out)))
    (.seq (.first (rep.ty (carryTy config out)) (NativeReset.code rep data cost primitive))
      (.seq (.atomic (compileLocal rep data cost primitive (secondExpression config out)))
        (.seq (.first (rep.ty (secondCarry out)) pass)
          (.seq (.atomic (compileLocal rep data cost primitive (secondSelectionExpression out)))
            (.seq (.first (rep.ty (secondTy out)) (.atomic selector))
              (.seq (.atomic (chooseLocal rep data cost primitive (finishExpression out)))
                (.branch (.atomic (QS.inr rep.data.unit (rep.ty (.pair out out))))
                  (.atomic (reject rep data (.pair out out) out)))))))))

def selected : Code Q unifSpec iface (rep.ty (selectedTy config out))
    (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) :=
  .seq (.atomic (compileLocal rep data cost primitive (freshExpression config out)))
    (.seq (.first (rep.ty (selectedTy config out)) sampler)
      (.seq (.atomic (compileLocal rep data cost primitive (lookupExpression config out)))
        (.seq (.first (rep.ty (freshTy config out)) (NativeLookup.code rep data cost primitive))
          (.seq (.atomic (chooseLocal rep data cost primitive (collisionExpression config out)))
            (.branch (.atomic (reject rep data (freshTy config out) out))
              (replay rep data cost primitive selector pass))))))

def code : Code Q unifSpec iface (rep.ty config)
    (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair out out))) :=
  .seq (.atomic (compileLocal rep data cost primitive (startExpression config)))
    (.seq (.first (rep.ty config) pass)
      (.seq (.atomic (compileLocal rep data cost primitive (firstSelectionExpression config out)))
        (.seq (.first (rep.ty (firstTy config out)) (.atomic selector))
          (.seq (.atomic (chooseLocal rep data cost primitive (firstChoiceExpression config out)))
            (.branch (selected rep data cost primitive selector pass sampler)
              (.atomic (reject rep data (selectedTy config out) out)))))))

theorem replay_denote (fresh : F) (slot : Nat)
    (first : out.Value (cryptoBase F G₁ G₂ K M)) (state : stateTy.Value (cryptoBase F G₁ G₂ K M))
    (input : config.Value (cryptoBase F G₁ G₂ K M)) :
    (replay rep data cost primitive selector pass).denote (fresh, slot, (first, state), input) = (do
      let second ← pass.denote (NativeReset.value (slot, fresh, state), input)
      pure (if (select second.1).1 ∧ (select second.1).2 = slot then
        .inr (first, second.1) else .inl ())) := by
  simp only [replay, NativeReset.code, Code.denote, pure_bind, bind_map_left]
  apply bind_congr
  intro second
  dsimp only [Expr.denote, resetExpression, secondExpression, secondSelectionExpression,
    finishExpression, Var.get, arithmetic]
  by_cases found : (select second.1).1 = true <;> by_cases same : (select second.1).2 = slot <;>
    simp [found, same]

theorem selected_denote (slot : Nat) (first : out.Value (cryptoBase F G₁ G₂ K M))
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M))
    (input : config.Value (cryptoBase F G₁ G₂ K M)) :
    (selected rep data cost primitive selector pass sampler).denote (slot, (first, state), input) = (do
      let fresh ← sampler.denote ()
      if (values (.inr ()) state.1)[slot]? = some fresh then pure (.inl ())
      else (replay rep data cost primitive selector pass).denote (fresh, slot, (first, state), input)) := by
  simp only [selected, NativeLookup.code, Code.denote, pure_bind, bind_map_left]
  apply bind_congr
  intro fresh
  dsimp only [Expr.denote, freshExpression, lookupExpression, collisionExpression, Var.get, arithmetic]
  rcases Option.eq_none_or_eq_some ((values (.inr ()) state.1)[slot]?) with hOld | ⟨old, hOld⟩
  · simp [NativeLookup.answer, hOld]
  · by_cases same : old = fresh <;> simp [NativeLookup.answer, hOld, same]

theorem denote (input : config.Value (cryptoBase F G₁ G₂ K M)) :
    (code rep data cost primitive selector pass sampler).denote input = (do
      let first ← pass.denote (([], []), input)
      if (select first.1).1 then
        let fresh ← sampler.denote ()
        if (values (.inr ()) first.2.1)[(select first.1).2]? = some fresh then pure (.inl ())
        else
          let second ← pass.denote (NativeReset.value ((select first.1).2, fresh, first.2), input)
          pure (if (select second.1).1 ∧ (select second.1).2 = (select first.1).2 then
            .inr (first.1, second.1) else .inl ())
      else pure (.inl ())) := by
  simp only [code, Code.denote, pure_bind, bind_map_left]
  apply bind_congr
  intro first
  dsimp only [Expr.denote, startExpression, firstSelectionExpression, firstChoiceExpression, Var.get]
  by_cases found : (select first.1).1 = true <;>
    simp only [found, ↓reduceIte]
  · rw [selected_denote]
    apply bind_congr
    intro fresh
    split
    · rfl
    · rw [replay_denote]
  · rfl

/-- The controller implements the named raw fork from the first-pass source law
and replay laws only at reached, selected restart states. It does not require a
pass implementation to accept malformed or unreachable tapes. -/
theorem source [SampleableType F] (qH : Nat)
    (main : OracleComp (Spec F) (out.Value (cryptoBase F G₁ G₂ K M)))
    (selectSource : out.Value (cryptoBase F G₁ G₂ K M) → Option (Fin (qH + 1)))
    (input : config.Value (cryptoBase F G₁ G₂ K M))
    (hselect : ∀ x, select x = choice (selectSource x))
    (hfirst : pass.denote (([], []), input) =
      (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample ((simulateQ oracle main).run {}))
    (hreplay : ∀ first ∈ support (simulateQ _root_.Schnorr.LazyROM.sample ((simulateQ oracle main).run {})),
      ∀ slot : Fin (qH + 1), selectSource first.1 = some slot → ∀ fresh : F,
        pass.denote (NativeUniform.encodeState (restart slot.val fresh first.2), input) =
          (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
            simulateQ _root_.Schnorr.LazyROM.sample
              ((simulateQ oracle main).run (restart slot.val fresh first.2)))
    (hsample : sampler.denote () = ($ᵗ F : ProbComp F)) :
    (code rep data cost primitive selector pass sampler).denote input =
      view <$> simulateQ _root_.Schnorr.LazyROM.sample (fork main qH selectSource) := by
  have sampled : simulateQ _root_.Schnorr.LazyROM.sample (liftComp ($ᵗ F) (Spec F)) =
      ($ᵗ F : ProbComp F) := by
    unfold _root_.Schnorr.LazyROM.sample
    rw [QueryImpl.simulateQ_add_liftComp_left]
    simp
  rw [denote, hfirst]
  simp only [fork, simulateQ_bind, map_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro first firstSupported
  rw [hselect]
  cases selected : selectSource first.1 with
  | none => simp [choice, view]
  | some slot =>
      simp only [choice, NativeUniform.encodeState, ↓reduceIte, simulateQ_bind,
        map_bind, hsample, sampled]
      apply bind_congr
      intro fresh
      by_cases collision : (values (.inr ()) first.2.saved)[slot.val]? = some fresh
      · simp [collision, view]
      · simp only [collision, ↓reduceIte]
        change (pass.denote (NativeUniform.encodeState (restart slot.val fresh first.2), input) >>= _) = _
        rw [hreplay first firstSupported slot selected fresh]
        simp only [StateT.run', bind_map_left, simulateQ_bind, map_bind]
        apply bind_congr
        intro second
        rw [hselect]
        cases secondSelected : selectSource second.1 with
        | none => simp [choice, view]
        | some index =>
            by_cases same : index = slot
            · simp [choice, view, same]
            · have different : index.val ≠ slot.val := fun h => same (Fin.ext h)
              simp [choice, view, same, different]

end Signatures.Runtime.Schnorr.RawTape.NativeFork

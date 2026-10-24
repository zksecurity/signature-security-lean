import Proofs.Runtime.BackendSchnorrROMPassSize

/-! Actual native selection for the general ROM pass. Verification precedes a
chronological live-cache scan and a checked query ordinal. Empty results reject;
the fold gives defined behavior on every list without inventing a default message.
Supported completed passes contain exactly one element. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram RawTape

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)

def verifyExpression {Γ} : Expr CryptoOp (cachePassOutput :: Γ) .bool :=
  .op .point₁Eq (.pair
    (.op .scale₁ (.pair (.snd (.snd (.fst (.fst v0)))) (.fst (.fst (.snd v0)))))
    (.op .add₁ (.pair (.fst (.snd (.fst (.fst v0))))
      (.op .scale₁ (.pair (.snd (.fst v0)) (.snd (.fst (.snd v0))))))))

def indexExpression {Γ} : Expr CryptoOp (cachePassOutput :: Γ) indexResult :=
  .letE (.snd (.snd (.snd v0)))
    (.letE (.pair (.fst (.fst (.fst v1))) (.fst (.snd (.fst (.fst v1)))))
      (liveIndex.weakenTail (cachePassOutput :: Γ)))

def guardExpression {Γ} (qH : Nat) : Expr CryptoOp (indexResult :: Γ) indexResult :=
  .branch (.fst v0)
    (.branch (.op .natLt (.pair (.snd v0) (.nat (qH + 1)))) v0 (.pair (.bool false) (.nat 0)))
    (.pair (.bool false) (.nat 0))

def oneExpression {Γ} (qH : Nat) : Expr CryptoOp (cachePassOutput :: Γ) indexResult :=
  .branch verifyExpression (.letE indexExpression (guardExpression qH)) (.pair (.bool false) (.nat 0))

def expression (qH : Nat) : Expr CryptoOp [NativePass.outputTy] indexResult :=
  .fold v0 (.pair (.bool false) (.nat 0)) (oneExpression qH)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def oneValue (qH : Nat) (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) : Bool × Nat :=
  selectValue p.2.1.1 p.2.1.2 p.1.1 p.1.2 p.2.2.2 qH

def value (qH : Nat) (results : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) : Bool × Nat :=
  results.foldl (fun _ p => oneValue qH p) (false, 0)

def source (qH : Nat) (results : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) : Option (Fin (qH + 1)) :=
  asIndex qH (value qH results)

theorem verifyExpression_denote (cost : PrimitiveCosts) {Γ}
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    verifyExpression.denote (arithmetic F G₁ G₂ K M cost) (p, env) =
      decide (p.1.1.2.2 • p.2.1.1 = p.1.1.2.1 + p.1.2 • p.2.1.2) := rfl

theorem indexExpression_denote (cost : PrimitiveCosts) {Γ}
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    indexExpression.denote (arithmetic F G₁ G₂ K M cost) (p, env) =
      (p.2.2.2.reverse.any (fun x => decide (x.1 = (p.1.1.1, p.1.1.2.1))),
        p.2.2.2.reverse.findIdx (fun x => decide (x.1 = (p.1.1.1, p.1.1.2.1)))) := by
  have h := liveIndex.weakenTail_denote (Δ := cachePassOutput :: Γ)
    (arithmetic F G₁ G₂ K M cost) ((p.1.1.1, p.1.1.2.1), p.2.2.2, ()) (p, env)
  simp only [Env.append] at h
  change (liveIndex.weakenTail (cachePassOutput :: Γ)).denote (arithmetic F G₁ G₂ K M cost)
    ((p.1.1.1, p.1.1.2.1), p.2.2.2, p, env) = _
  rw [h, liveIndex_denote]

theorem guardExpression_denote (cost : PrimitiveCosts) {Γ} (qH : Nat) (result : Bool × Nat)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    (guardExpression qH).denote (arithmetic F G₁ G₂ K M cost) (result, env) = guarded result qH := by
  rcases result with ⟨found, n⟩
  cases found <;> simp [guardExpression, Expr.denote, Var.get, arithmetic, guarded]

theorem oneExpression_denote (cost : PrimitiveCosts) {Γ} (qH : Nat)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    (oneExpression qH).denote (arithmetic F G₁ G₂ K M cost) (p, env) = oneValue qH p := by
  change (if (verifyExpression (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) (p, env) then
    (guardExpression (Γ := cachePassOutput :: Γ) qH).denote (arithmetic F G₁ G₂ K M cost)
      ((indexExpression (Γ := Γ)).denote (arithmetic F G₁ G₂ K M cost) (p, env), p, env) else (false, 0)) = _
  rw [verifyExpression_denote, guardExpression_denote, indexExpression_denote]
  simp only [oneValue, selectValue, decide_eq_true_eq]

theorem expression_denote (cost : PrimitiveCosts) (qH : Nat)
    (results : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (expression qH).denote (arithmetic F G₁ G₂ K M cost) (results, ()) = value qH results := by
  change results.foldl (fun acc p => (oneExpression (Γ := [indexResult, NativePass.outputTy]) qH).denote (arithmetic F G₁ G₂ K M cost)
    (p, acc, results, ())) (false, 0) = _
  have h : (fun acc p => (oneExpression (Γ := [indexResult, NativePass.outputTy]) qH).denote
      (arithmetic F G₁ G₂ K M cost) (p, acc, results, ())) =
      (fun (_ : Bool × Nat) p => oneValue qH p) := by
    funext acc p
    exact oneExpression_denote cost (Γ := [indexResult, NativePass.outputTy]) qH p (acc, results, ())
  rw [h]
  rfl

theorem oneValue_selectionRun (cost : PrimitiveCosts) (qH : Nat)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
    oneValue qH p = (selectionRun cost (p.1, p.2, []) qH).value := by
  unfold selectionRun
  rw [verifyObserved_run]
  dsimp only
  split
  · rename_i h
    have hv := of_decide_eq_true h
    rw [guardIndex_run]
    change oneValue qH p = guarded ((liveIndex.run (arithmetic F G₁ G₂ K M cost)
      ((p.1.1.1, p.1.1.2.1), p.2.2.2, ())).value) qH
    rw [Expr.run_value, liveIndex_denote]
    simp only [oneValue, selectValue, hv, ↓reduceIte]
  · rename_i h
    have hn : ¬ p.1.1.2.2 • p.2.1.1 = p.1.1.2.1 + p.1.2 • p.2.1.2 := by simpa using h
    simp only [oneValue, selectValue, hn, ↓reduceIte]

theorem source_singleton (cost : PrimitiveCosts) (qH : Nat)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
    source qH [p] = selectPass cost qH p := by
  simp only [source, value, List.foldl_cons, List.foldl_nil, selectPass, oneValue_selectionRun cost]

omit [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₂] [DecidableEq K] in
theorem oneValue_normalized (qH : Nat) (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) :
    oneValue qH p = NativeFork.choice (asIndex qH (oneValue qH p)) := by
  have hguard (result : Bool × Nat) : guarded result qH = NativeFork.choice (asIndex qH (guarded result qH)) := by
    rcases result with ⟨found, n⟩
    cases found <;> by_cases hn : n < qH + 1 <;> simp [guarded, asIndex, NativeFork.choice, hn]
  unfold oneValue selectValue
  split
  · exact hguard _
  · simp [asIndex, NativeFork.choice]

omit [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₂] [DecidableEq K] in
theorem value_source (qH : Nat) (results : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) :
    value qH results = NativeFork.choice (source qH results) := by
  have hfold (xs : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) (acc : Bool × Nat)
      (ha : acc = NativeFork.choice (asIndex qH acc)) :
      xs.foldl (fun _ p => oneValue qH p) acc =
        NativeFork.choice (asIndex qH (xs.foldl (fun _ p => oneValue qH p) acc)) := by
    induction xs generalizing acc with
    | nil => exact ha
    | cons p ps ih => exact ih _ (oneValue_normalized qH p)
  exact hfold results (false, 0) (by simp [asIndex, NativeFork.choice])

omit [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₂] [DecidableEq K] in
theorem value_index_le (qH : Nat) (results : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) :
    (value qH results).2 ≤ qH := by
  rw [value_source]
  cases source qH results with
  | none => simp [NativeFork.choice]
  | some i => exact Nat.le_of_lt_succ i.isLt

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def selector (qH : Nat) : Q.Realizer (rep.ty NativePass.outputTy) (rep.ty NativeFork.choiceTy) (value qH) :=
  (NativeComponents.localCode rep data cost primitive (expression qH)).castFunction
    (funext (expression_denote cost qH))

end Signatures.Runtime.Schnorr.ListROM.NativeSelection

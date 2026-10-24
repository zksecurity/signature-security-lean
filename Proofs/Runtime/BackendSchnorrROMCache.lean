import Proofs.Runtime.BackendSampledCache
import Proofs.Runtime.SchnorrROMListPass

/-! Native reduction routines for Schnorr's ordinary ROM pass. The scalar draw
is actual state-passing backend code, so retained-tape sampling can be installed
without changing either cache algorithm. The attacker is not compiled here.
The draw's complete stored code is counted once per hash routine and twice in
the signing routine. Runtime certification remains separate from these
semantic and stored-code bounds. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M S : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (store : C.Str S)
  (draw : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit store)
    (StepClass.HasProd.prod (rep.ty scalar) store))

def effect {a b : Ty CryptoAtom} (instr : SampledCache.Draw scalar a b) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store) :=
  match instr with | .sample => draw

def semantics : SemanticsM (cryptoBase F G₁ G₂ K M) (SampledCache.Draw scalar) (StateT S ProbComp) :=
  fun instr input saved => match instr with | .sample => draw.denote (input, saved)

def live : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env [hashKey, scalar, hashCache]) store)
    (StepClass.HasProd.prod (rep.ty (.pair scalar hashCache)) store) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw)
    (cacheGetExpr hashEq .sample)

def managed : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env [hashKey, scalar, hashCache, hashCache]) store)
    (StepClass.HasProd.prod (rep.ty (.pair scalar (.pair hashCache hashCache))) store) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw)
    (managedGet .sample)

def signing : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.env [message, point₁, point₁, hashCache]) store)
    (StepClass.HasProd.prod (rep.ty (.pair (.pair point₁ scalar) hashCache)) store) :=
  Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw)
    (signCached .sample)

private theorem compile_denote {Γ a} (body : Program CryptoOp (SampledCache.Draw scalar) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (saved : S) :
    (Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) body).denote
      (env, saved) = (body.denote (arithmetic F G₁ G₂ K M cost) (semantics rep store draw) env).run saved := by
  apply Language.compile_denote
  intro a b instr input state
  cases instr
  rfl

theorem live_denote (k : M × G₁) (fallback : F) (cache : List ((M × G₁) × F)) (saved : S) :
    (live rep data cost primitive store draw).denote ((k, fallback, cache, ()), saved) =
      match cacheMap cache k with
      | some c => pure ((c, cache), saved)
      | none => (fun p => ((p.1, (k, p.1) :: cache), p.2)) <$> draw.denote ((), saved) := by
  rw [live, compile_denote, cacheGetExpr_denote _ _ _ _ (hashEq_value cost), lookupValue_cacheMap]
  cases cacheMap cache k <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, StateT.run_map]
  rfl

/-- A live cache hit does not execute the supplied stateful draw, even in the
costed program. This includes retaining the draw's entire input context. -/
theorem live_hit_run
    (other : Code Q unifSpec iface (StepClass.HasProd.prod rep.data.unit store)
      (StepClass.HasProd.prod (rep.ty scalar) store))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (k : M × G₁) (fallback : F) (cache : List ((M × G₁) × F)) (saved : S) (c : F)
    (hit : cacheMap cache k = some c) :
    (live rep data cost primitive store draw).run control queryCost ((k, fallback, cache, ()), saved) =
      (live rep data cost primitive store other).run control queryCost ((k, fallback, cache, ()), saved) := by
  have hl : (lookupExpr (val := scalar) hashEq).denote (arithmetic F G₁ G₂ K M cost)
      (k, fallback, cache, ()) = (true, c) := by
    rw [← Expr.run_value, lookupExpr_value _ _ (hashEq_value cost), lookupValue_cacheMap, hit]
  simp only [live, cacheGetExpr, Language.compile, Language.withContext, Code.run,
    sequenceRun, retainRun, chargeRun, pure_bind, map_pure, hl, Expr.denote, Var.get, ite_true]

theorem managed_denote (k : M × G₁) (fallback : F)
    (managedCache liveCache : List ((M × G₁) × F)) (saved : S) :
    (managed rep data cost primitive store draw).denote ((k, fallback, managedCache, liveCache, ()), saved) =
      match cacheMap managedCache k with
      | some c => pure ((c, managedCache, liveCache), saved)
      | none => (fun p => ((p.1.1, (k, p.1.1) :: managedCache, p.1.2), p.2)) <$>
          (live rep data cost primitive store draw).denote ((k, fallback, liveCache, ()), saved) := by
  rw [managed, compile_denote, managedGet_denote, lookupValue_cacheMap]
  cases cacheMap managedCache k <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, StateT.run_map]
  rw [live, compile_denote]

/-- Signing uses two sequential private draws, preserves a prior programmed
entry on collision, and returns the state after both draws. -/
theorem signing_denote (msg : M) (g pk : G₁) (cache : List ((M × G₁) × F)) (saved : S) :
    (signing rep data cost primitive store draw).denote ((msg, g, pk, cache, ()), saved) = (do
      let first ← draw.denote ((), saved)
      let second ← draw.denote ((), first.2)
      let commitment := second.1 • g - first.1 • pk
      let updated := ((cacheProgram (val := scalar) hashEq).run (arithmetic F G₁ G₂ K M cost)
        ((msg, commitment), first.1, cache, ())).value
      pure (((commitment, second.1), updated), second.2)) := by
  rw [signing, compile_denote, signCached_denote]
  rfl

def liveDescription (sizes : DescriptionSize Q) (allowance : Nat) : Nat :=
  Language.descriptionBound allowance (fun op => sizes.localSize (primitive op)) (fun _ => 0)
    (cacheGetExpr (Cmd := SampledCache.Draw scalar) hashEq .sample)

def managedDescription (sizes : DescriptionSize Q) (allowance : Nat) : Nat :=
  Language.descriptionBound allowance (fun op => sizes.localSize (primitive op)) (fun _ => 0)
    (managedGet (Cmd := SampledCache.Draw scalar) .sample)

def signingDescription (sizes : DescriptionSize Q) (allowance : Nat) : Nat :=
  Language.descriptionBound allowance (fun op => sizes.localSize (primitive op)) (fun _ => 0)
    (signCached (Cmd := SampledCache.Draw scalar) .sample)

variable (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

private theorem compile_description {Γ a} (body : Program CryptoOp (SampledCache.Draw scalar) Γ a) :
    (Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive store (effect rep store draw) body).descriptionSize sizes ≤
      Language.descriptionBound allowance (fun op => sizes.localSize (primitive op))
        (fun _ => draw.descriptionSize sizes) body :=
  Language.compile_descriptionSize sizes allowance laws rep data (arithmetic F G₁ G₂ K M cost) primitive
    dataLaws (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) store (effect rep store draw)
    (fun _ => draw.descriptionSize sizes) (fun instr => by cases instr; exact le_rfl) body

theorem live_description :
    (live rep data cost primitive store draw).descriptionSize sizes ≤
      draw.descriptionSize sizes + liveDescription rep cost primitive sizes allowance := by
  apply (compile_description rep data cost primitive store draw sizes allowance laws dataLaws _).trans
  simp only [liveDescription, cacheGetExpr, Language.descriptionBound]
  omega

theorem managed_description :
    (managed rep data cost primitive store draw).descriptionSize sizes ≤
      draw.descriptionSize sizes + managedDescription rep cost primitive sizes allowance := by
  apply (compile_description rep data cost primitive store draw sizes allowance laws dataLaws _).trans
  simp only [managedDescription, managedGet, cacheGetExpr, Language.descriptionBound]
  omega

theorem signing_description :
    (signing rep data cost primitive store draw).descriptionSize sizes ≤
      2 * draw.descriptionSize sizes + signingDescription rep cost primitive sizes allowance := by
  apply (compile_description rep data cost primitive store draw sizes allowance laws dataLaws _).trans
  simp only [signingDescription, signCached, Language.descriptionBound]
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeCache

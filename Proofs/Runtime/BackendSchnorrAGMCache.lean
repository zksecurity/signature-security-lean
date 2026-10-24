import Proofs.Runtime.BackendSchnorrAGMFreshBudget
import Proofs.Runtime.BackendStructuredCache

/-! Native first-entry-preserving cache access for Schnorr AGM. The generic
cache compiler invokes a stateful fresh-entry sampler only on a miss; its store
holds the pre-challenge affine explanation and the bad-event flag. -/

open OracleComp OracleSpec PFunctor Schnorr.AGM

namespace Signatures.Runtime.SchnorrAGM.Native

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def cacheEffect {a b : Ty CryptoAtom} (draw : SampledCache.Draw entryTy a b) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty readStoreTy))
      (StepClass.HasProd.prod (rep.ty b) (rep.ty readStoreTy)) :=
  match draw with | .sample => freshSample rep data cost primitive sampler

def cacheAccess :
    Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [cacheKeyTy, entryTy, cacheTy]) (rep.ty readStoreTy))
      (StepClass.HasProd.prod (rep.ty (.pair entryTy cacheTy)) (rep.ty readStoreTy)) :=
  Language.compile rep data (StructuredCache.operations rep (comparison rep data cost primitive))
    (StructuredCache.implementation rep (comparison rep data cost primitive))
    (rep.ty readStoreTy) (cacheEffect rep data cost primitive sampler)
    (cacheGet .equal .sample)

theorem cacheAccess_denote (k : M × G₁) (default : EncodedEntry F)
    (xs : List ((M × G₁) × EncodedEntry F)) (saved : ReadStore F) :
    (cacheAccess rep data cost primitive sampler).denote ((k, default, xs, ()), saved) =
      match cacheMap xs k with
      | some e => pure ((e, xs), saved)
      | none => (fun c => let p := freshValue (c, saved)
          ((p.1, (k, p.1) :: xs), p.2)) <$> sampler.denote () := by
  let H : SemanticsM (cryptoBase F G₁ G₂ K M) (SampledCache.Draw entryTy)
      (StateT (ReadStore F) ProbComp) := fun draw input => match draw with
    | .sample => fun saved => (fun c => freshValue (c, saved)) <$> sampler.denote input
  have he : ∀ {a b} (draw : SampledCache.Draw entryTy a b) input saved,
      (cacheEffect rep data cost primitive sampler draw).denote (input, saved) = (H draw input).run saved := by
    intro a b draw input saved
    cases draw
    cases input
    exact freshSample_denote rep data cost primitive sampler saved
  have hl : (lookup (StructuredCache.Call.equal (key := cacheKeyTy)) (val := entryTy)).denote
      (StructuredCache.operations rep (comparison rep data cost primitive)) (k, default, xs, ()) =
        match cacheMap xs k with | none => (false, default) | some e => (true, e) := by
    rw [← Expr.run_value, lookup_correct _ _ (fun _ _ => rfl), lookupValue_cacheMap]
    cases cacheMap xs k <;> rfl
  rw [cacheAccess, Language.compile_denote _ _ _ _ _ _ H he]
  cases hx : cacheMap xs k <;>
    simp only [cacheGet, Program.denote, hl, hx, Expr.denote, Var.get,
      Bool.false_eq_true, ite_true, ite_false, StateT.run_pure,
      pure_bind, H, StateT.run_map, bind_pure_comp]
  change (fun p => ((p.1, (k, p.1) :: xs), p.2)) <$>
    ((fun c => freshValue (c, saved)) <$> sampler.denote ()) = _
  simp only [Functor.map_map]

/-- Restore the untouched metadata in the representation relation. This map is
used only to state correctness; the eventual read wrapper must implement routing. -/
def observeCache (s : State F G₁ M)
    (r : (EncodedEntry F × List ((M × G₁) × EncodedEntry F)) × ReadStore F) :
    F × EncodedState F G₁ M :=
  (r.1.1.1, r.1.2, s.representations.map encodeAffine, s.signed, s.malformed, r.2.2)

theorem cacheAccess_read [SampleableType F]
    (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (s : State F G₁ M) (k : M × G₁) (a : Affine F) (default : EncodedEntry F) :
    observeCache s <$>
        (cacheAccess rep data cost primitive sampler).denote
          ((k, default, (encodeState s).1, ()), (encodeAffine a, s.bad)) =
      (fun p => (p.1, encodeState p.2)) <$> (SchnorrAGM.read k a).run s := by
  rw [cacheAccess_denote]
  simp only [encodeState, cacheMap_encode]
  cases hx : cacheMap s.cache k with
  | none =>
      simp [hx, SchnorrAGM.read, StateT.run, hsample, bind_pure_comp, Functor.map_map,
        freshValue, observeCache, record, encodeMetadata, encodeEntry, encodeAffine]
      rfl
  | some e =>
      simp [hx, SchnorrAGM.read, StateT.run, observeCache, encodeMetadata, encodeEntry]

theorem cacheAccess_hit_run (other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (k : M × G₁) (default : EncodedEntry F) (xs : List ((M × G₁) × EncodedEntry F))
    (saved : ReadStore F) (e : EncodedEntry F) (hit : cacheMap xs k = some e) :
    (cacheAccess rep data cost primitive sampler).run control queryCost ((k, default, xs, ()), saved) =
      (cacheAccess rep data cost primitive other).run control queryCost ((k, default, xs, ()), saved) := by
  have hl : (lookup (StructuredCache.Call.equal (key := cacheKeyTy)) (val := entryTy)).denote
      (StructuredCache.operations rep (comparison rep data cost primitive)) (k, default, xs, ()) = (true, e) := by
    rw [← Expr.run_value, lookup_correct _ _ (fun _ _ => rfl), lookupValue_cacheMap, hit]
  simp only [cacheAccess, cacheGet, Language.compile, Language.withContext, Code.run,
    sequenceRun, retainRun, chargeRun, pure_bind, map_pure, hl, Expr.denote, Var.get, ite_true]

theorem cacheAccess_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (cacheAccess rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .messageEq + primitiveSize .point₁Eq +
        primitiveSize .add + primitiveSize .zero + primitiveSize .scalarEq + 450 * allowance + 40 := by
  have h := Language.compile_descriptionSize sizes allowance laws rep data
    (StructuredCache.operations rep (comparison rep data cost primitive))
    (StructuredCache.implementation rep (comparison rep data cost primitive)) dataLaws
    (fun _ => sizes.localSize (comparison rep data cost primitive)) (fun call => by cases call; exact le_rfl)
    (rep.ty readStoreTy) (cacheEffect rep data cost primitive sampler)
    (fun _ => (freshSample rep data cost primitive sampler).descriptionSize sizes)
    (fun draw => by cases draw; exact le_rfl) (cacheGet .equal .sample)
  have hc := comparison_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  have hf := freshSample_description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  refine h.trans ?_
  simp only [cacheGet, lookup, lookupBody, Language.descriptionBound,
    Expression.descriptionBound, Expression.variableDescription]
  omega

end Signatures.Runtime.SchnorrAGM.Native

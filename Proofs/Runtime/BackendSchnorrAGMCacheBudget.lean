import Proofs.Runtime.BackendSchnorrAGMCache

/-! Full native cost of the Schnorr cache core, derived from actual comparison,
sampling, field operations, list traversal and state-passing code. The explanation
is runtime data; neither its computation nor the outer read routing is hidden in
this bound. Those surrounding routines have separate obligations. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native

open BackendProgram

def cacheTime (overhead : Nat → Nat) (width cap messageTime pointTime fieldTime equalityTime sampleTime : Nat) : Nat :=
  let fee := overhead (32 * CacheCompiler.frameWidth (5 * width) cap)
  cap * (messageTime + pointTime + 391 * fee) + sampleTime +
    2 * fieldTime + equalityTime + 395 * fee

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem cacheAccess_bound (width cap messageTime pointTime fieldTime equalityTime sampleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ 5 * width → Q.size (rep.ty message) b ≤ 5 * width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ 5 * width → Q.size (rep.ty point₁) b ≤ 5 * width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (heq : ∀ a b : F, (primitiveBound .scalarEq).time (a, b) ≤ equalityTime)
    (hd : Bounds control queryCost sampler (fun _ => True)
      (fun c => Q.size (rep.ty scalar) c ≤ width) sampleTime) :
    Bounds control queryCost (cacheAccess rep data cost primitive sampler)
      (fun p => CacheCompiler.Input (Q := Q) rep (5 * width) cap p.1 ∧
        Q.size (rep.ty affineTy) p.2.1 ≤ width)
      (fun p => CacheCompiler.Output (Q := Q) rep (5 * width) (cap + 1) p.1 ∧
        Q.size (rep.ty affineTy) p.2.1 ≤ width)
      (cacheTime overhead width cap messageTime pointTime fieldTime equalityTime sampleTime) := by
  let cmp := comparison rep data cost primitive
  let P := StructuredCache.operations rep cmp
  let impl : {a b : Ty CryptoAtom} → (call : StructuredCache.Call cacheKeyTy a b) →
      Q.Realizer (rep.ty a) (rep.ty b) (P.execute call) := StructuredCache.implementation rep cmp
  have hwide : width ≤ 5 * width := by omega
  have hcomparison (x y : M × G₁)
      (hx : Q.size (rep.ty cacheKeyTy) x ≤ 5 * width)
      (hy : Q.size (rep.ty cacheKeyTy) y ≤ 5 * width) :
      Q.cost cmp (x, y) ≤ messageTime + pointTime + 134 * overhead (128 * (5 * width)) :=
    comparison_cost rep data cost primitive sizes laws dataLaws primitiveBound mono x y
      (5 * width) messageTime pointTime (hh.trans hwide) (hu.trans hwide)
      (fun b => (hb b).trans hwide) hx hy hm hg
  have hfresh := freshSample_bound rep data cost primitive sizes laws dataLaws primitiveBound mono
    sampler control queryCost routing width fieldTime equalityTime sampleTime hh hu hb hf hz hadd heq hd
  have hcache := CacheCompiler.cacheGet_bound rep data P impl sizes lists laws dataLaws
    (fun call => LocalBound.measured (impl call)) mono control queryCost routing
    (rep.ty readStoreTy) (cacheEffect rep data cost primitive sampler)
    StructuredCache.Call.equal SampledCache.Draw.sample (fun _ _ => rfl)
    (fun saved => Q.size (rep.ty affineTy) saved.1 ≤ width)
    (5 * width) cap (messageTime + pointTime + 134 * overhead (128 * (5 * width)))
    (sampleTime + 2 * fieldTime + equalityTime + 263 * overhead (128 * width))
    (hh.trans hwide) (hu.trans hwide) (fun b => (hb b).trans hwide)
    (fun saved hs => (readStore_size rep sizes saved width hh hb hs).trans (by omega))
    hcomparison hfresh
  intro input hi z hzrun
  obtain ⟨hout, ht⟩ := hcache input hi z hzrun
  have hsmall : overhead (128 * width) ≤ overhead (32 * CacheCompiler.frameWidth (5 * width) cap) := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hcompare : overhead (128 * (5 * width)) ≤ overhead (32 * CacheCompiler.frameWidth (5 * width) cap) := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  refine ⟨hout, ht.trans ?_⟩
  dsimp [cacheTime]
  nlinarith [Nat.mul_le_mul_left (134 * cap) hcompare]

end Signatures.Runtime.SchnorrAGM.Native

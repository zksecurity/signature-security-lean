import Signatures.Runtime.BackendLazyAGMReadAssembly

/-! Complete native good/bad extraction-read budgets. Only individual local
primitive and scalar-sampler costs are assumptions; the routing and cache
costs are derived from the implemented code. Pair draws use two scalar draws. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws primitiveBound sizes lists mono routing

theorem backendGoodRead_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (m : M) (cache : List (M × F))
    (width cap comparisonTime scalarTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : Q.size (rep.ty (cacheTy scalar)) cache ≤ width)
    (hc : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hn : cache.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ width → Q.size (rep.ty message) y ≤ width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (out : Run (F × List (M × F)))
    (hout : out ∈ support ((backendGoodRead rep data cost primitive sampling).run control queryCost (m, cache))) :
    CacheCompiler.Output (Q := Q) rep (key := message) (val := scalar) width (cap + 1) out.value ∧
      out.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth width cap)) +
        scalarTime + zeroTime + 192 * overhead (32 * CacheCompiler.frameWidth width cap) := by
  let fee := overhead (32 * CacheCompiler.frameWidth width cap)
  have h5 : width ≤ 5 * width := by omega
  have hframe : Q.size (rep.env [message, cacheTy scalar]) (m, cache, ()) ≤ 5 * width := by
    have hp := @sizes.prod_le
    dsimp only [LanguageRepresentation.env] at *
    grind only
  have ha := goodReadArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (m, cache, ()) (5 * width) zeroTime (hh.trans h5) (hu.trans h5) ((hf 0).trans h5) hframe hz
  have haFee : overhead (32 * (5 * width)) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hargs : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (readArgs (.op .zero .unit))) (m, cache, ()) ≤ zeroTime + 32 * fee := by omega
  rw [backendGoodRead] at hout
  have h := backendRead_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing sampling.scalar (.op .zero .unit) m cache
    width cap comparisonTime scalarTime (zeroTime + 32 * fee)
    hh hu hb hm hs (fun p hp => ⟨hc p hp, hf p.2⟩) hn (hf 0) he
    (by intro u _ z hz'; cases u; exact ⟨hf z.value, hd z hz'⟩) hargs out hout
  exact ⟨h.1, by dsimp only [fee] at h; omega⟩

theorem backendBadRead_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (m : M) (cache : List (M × (F × F)))
    (width cap comparisonTime scalarTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : Q.size (rep.ty (cacheTy (.pair scalar scalar))) cache ≤ width)
    (hc : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hn : cache.length ≤ cap)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (he : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound CryptoOp.messageEq).time (x, y) ≤ comparisonTime)
    (hd : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (out : Run ((F × F) × List (M × (F × F))))
    (hout : out ∈ support ((backendBadRead rep data cost primitive sampling).run control queryCost (m, cache))) :
    CacheCompiler.Output (Q := Q) rep (key := message) (val := .pair scalar scalar)
        (3 * width) (cap + 1) out.value ∧
      out.steps ≤ cap * (comparisonTime + 257 * overhead (32 * CacheCompiler.frameWidth (3 * width) cap)) +
        2 * scalarTime + 2 * zeroTime + 212 * overhead (32 * CacheCompiler.frameWidth (3 * width) cap) := by
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * width) cap)
  have h3 : width ≤ 3 * width := by omega
  have h5 : width ≤ 5 * width := by omega
  have hp (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at h
    omega
  have hframe : Q.size (rep.env [message, cacheTy (.pair scalar scalar)]) (m, cache, ()) ≤ 5 * width := by
    have hprod := @sizes.prod_le
    dsimp only [LanguageRepresentation.env] at *
    grind only
  have ha := badReadArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (m, cache, ()) (5 * width) zeroTime (hh.trans h5) (hu.trans h5) ((hf 0).trans h5) hframe hz
  have haFee : overhead (32 * (5 * width)) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hargs : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (readArgs (.pair (.op .zero .unit) (.op .zero .unit)))) (m, cache, ()) ≤ 2 * zeroTime + 40 * fee := by omega
  have component : Bounds control queryCost sampling.scalar (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) scalarTime := by
    intro u _ z hz'
    cases u
    exact ⟨hf z.value, hd z hz'⟩
  have hpSampler := PairSampling.bound rep.data data (rep.ty scalar) (rep.ty scalar)
    sampling.scalar sampling.scalar sizes laws dataLaws mono control queryCost routing
    width scalarTime scalarTime hh hu component component
  have hpFee : overhead (8 * width) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hdraw : Bounds control queryCost (pairSampler rep data sampling) (fun _ => True)
      (fun r => Q.size (rep.ty (.pair scalar scalar)) r ≤ 3 * width) (2 * scalarTime + 12 * fee) := by
    intro u hi z hz'
    have h := hpSampler u hi z hz'
    exact ⟨hp z.value, by omega⟩
  rw [backendBadRead] at hout
  have h := backendRead_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    control queryCost routing (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))
    m cache (3 * width) cap comparisonTime (2 * scalarTime + 12 * fee) (2 * zeroTime + 40 * fee)
    (hh.trans h3) (hu.trans h3) (fun b => (hb b).trans h3) (hm.trans h3) (hs.trans h3)
    (fun p hmem => ⟨(hc p hmem).trans h3, hp p.2⟩) hn (hp (0, 0)) he hdraw hargs out hout
  exact ⟨h.1, by dsimp only [fee] at h; omega⟩

end Signatures.Runtime.LazyAGM

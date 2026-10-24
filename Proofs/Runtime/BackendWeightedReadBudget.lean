import Proofs.Runtime.BackendWeightedRead

/-! Complete native read budgets derived from the primitive and scalar-sampler
contracts. These charge the executed zero fallback, all cache/state routing,
the actual structured comparison, and both scalar draws in the pair branch. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Read

open BackendProgram

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
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes laws dataLaws primitiveBound mono

omit [C.HasOption] sizes in
theorem zeroCode_cost (input : Ty CryptoAtom) (x : input.Value (cryptoBase F G₁ G₂ K M))
    (width zeroTime : Nat) (hu : Q.size rep.data.unit () ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width) (hx : Q.size (rep.ty input) x ≤ 3 * width)
    (hz : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (zeroCode rep data cost primitive input) x ≤ zeroTime + 2 * overhead (8 * width) := by
  rw [zeroCode, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := (LocalBound.compose laws (dataLaws.unitBound (rep.ty input)) (primitiveBound .zero)).cost_le x
  dsimp only [LocalBound.compose, DataCostLaws.unitBound, arithmetic] at h
  have huFee := mono (show Q.size (rep.ty input) x + Q.size rep.data.unit () ≤ 8 * width by omega)
  have hfFee := mono (show Q.size (rep.ty input) x + Q.size rep.data.unit () +
    Q.size (rep.ty scalar) (0 : F) ≤ 8 * width by omega)
  exact h.trans (by omega)

theorem pairZeroCode_cost (input : Ty CryptoAtom) (x : input.Value (cryptoBase F G₁ G₂ K M))
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width) (hx : Q.size (rep.ty input) x ≤ 3 * width)
    (hz : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (pairZeroCode rep data cost primitive input) x ≤ 2 * zeroTime + 5 * overhead (8 * width) := by
  have hz := zeroCode_cost rep data cost primitive laws dataLaws primitiveBound mono input x width zeroTime hu hf hx hz
  have hp := laws.pair (zeroCode rep data cost primitive input) (zeroCode rep data cost primitive input) x
  have hs := sizes.prod_le (rep.ty scalar) (rep.ty scalar) ((0 : F), (0 : F))
  dsimp only at hs
  change Q.size (rep.ty (.pair scalar scalar)) ((0 : F), (0 : F)) ≤ _ at hs
  have hfee : overhead (Q.size (rep.ty input) x +
      Q.size (rep.ty (.pair scalar scalar)) ((0 : F), (0 : F))) ≤ overhead (8 * width) := by
    apply mono
    omega
  change Q.cost (pairZeroCode rep data cost primitive input) x ≤ _ at hp
  simp only [LanguageRepresentation.ty] at hp hfee
  exact hp.trans (by omega)

def goodTime (overhead : Nat → Nat) (width cap comparisonTime scalarTime zeroTime : Nat) : Nat :=
  cap * (comparisonTime + 391 * overhead (32 * CacheCompiler.frameWidth width cap)) +
    scalarTime + zeroTime + 162 * overhead (32 * CacheCompiler.frameWidth width cap)

def badTime (overhead : Nat → Nat) (width cap comparisonTime scalarTime zeroTime : Nat) : Nat :=
  cap * (comparisonTime + 391 * overhead (32 * CacheCompiler.frameWidth (3 * width) cap)) +
    2 * scalarTime + 2 * zeroTime + 177 * overhead (32 * CacheCompiler.frameWidth (3 * width) cap)

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (index : Index) (lists : ListSizeLaws Q rep.data header)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include lists routing

theorem goodRead_bound (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (width cap topicTime indexTime natTime scalarTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (hk : Q.size (rep.ty index.ty) k ≤ width)
    (hc : Q.size (rep.ty (cacheTy index.ty scalar)) cache ≤ width)
    (he : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : cache.length ≤ cap) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ width → Q.size (rep.ty key) b ≤ width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (heq : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound → (primitiveBound .natEq).time (j, k) ≤ natTime)
    (hs : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (out : Run (F × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hout : out ∈ support ((goodRead rep data cost primitive sampling index).run control queryCost (k, cache))) :
    CacheCompiler.Output (Q := Q) rep (key := index.ty) (val := scalar) width (cap + 1) out.value ∧
      out.steps ≤ goodTime overhead width cap (topicTime + 2 * indexTime + natTime) scalarTime zeroTime := by
  have hp := sizes.prod_le (rep.ty index.ty) (rep.ty (cacheTy index.ty scalar)) (k, cache)
  have hx : Q.size (rep.ty (inputTy index.ty scalar)) (k, cache) ≤ 3 * width := by
    dsimp only at hp
    exact hp.trans (by omega)
  have hzero := zeroCode_cost rep data cost primitive laws dataLaws primitiveBound mono
    (inputTy index.ty scalar) (k, cache) width zeroTime hu (hf 0) hx hz
  have result := CacheRead.bound rep data (index.code rep data cost primitive)
    (zeroCode rep data cost primitive (inputTy index.ty scalar)) sampling.scalar
    sizes lists laws dataLaws mono control queryCost routing k cache width cap
    (topicTime + 2 * indexTime + natTime + 134 * overhead (128 * width))
    (zeroTime + 2 * overhead (8 * width)) scalarTime hh hu hb hk hc
    (fun p hp => ⟨he p hp, hf p.2⟩) hlen (hf 0)
    (fun x y hx hy => index.native_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
      x y width topicTime indexTime natTime hh hu hb hn hx hy ht hi heq)
    hzero (by intro u _ z hz; cases u; exact ⟨hf z.value, hs z hz⟩) out hout
  have hm : overhead (128 * width) ≤ overhead (32 * CacheCompiler.frameWidth width cap) := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hm' : overhead (8 * width) ≤ overhead (32 * CacheCompiler.frameWidth width cap) :=
    (mono (show 8 * width ≤ 128 * width by omega)).trans hm
  refine ⟨result.1, result.2.trans ?_⟩
  dsimp [goodTime]
  nlinarith [Nat.mul_le_mul_left (134 * cap) hm]

theorem badRead_bound (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F)))
    (width cap topicTime indexTime natTime scalarTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ index.bound, Q.size rep.data.nat j ≤ width)
    (hk : Q.size (rep.ty index.ty) k ≤ width)
    (hc : Q.size (rep.ty (cacheTy index.ty (.pair scalar scalar))) cache ≤ width)
    (he : ∀ p ∈ cache, Q.size (rep.ty index.ty) p.1 ≤ width)
    (hlen : cache.length ≤ cap) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ 3 * width → Q.size (rep.ty key) b ≤ 3 * width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (heq : ∀ j k : Nat, j ≤ index.bound → k ≤ index.bound → (primitiveBound .natEq).time (j, k) ≤ natTime)
    (hs : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound .zero).time () ≤ zeroTime)
    (out : Run ((F × F) × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))))
    (hout : out ∈ support ((badRead rep data cost primitive sampling index).run control queryCost (k, cache))) :
    CacheCompiler.Output (Q := Q) rep (key := index.ty) (val := .pair scalar scalar)
      (3 * width) (cap + 1) out.value ∧
      out.steps ≤ badTime overhead width cap (topicTime + 2 * indexTime + natTime) scalarTime zeroTime := by
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * width) cap)
  have hw : width ≤ 3 * width := by omega
  have hp (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    exact h.trans (by omega)
  have hx : Q.size (rep.ty (inputTy index.ty (.pair scalar scalar))) (k, cache) ≤ 3 * (3 * width) := by
    have h := sizes.prod_le (rep.ty index.ty) (rep.ty (cacheTy index.ty (.pair scalar scalar))) (k, cache)
    dsimp only at h
    exact h.trans (by omega)
  have hzero := pairZeroCode_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
    (inputTy index.ty (.pair scalar scalar)) (k, cache) (3 * width) zeroTime
    (hh.trans hw) (hu.trans hw) ((hf 0).trans hw) hx hz
  have component : Bounds control queryCost sampling.scalar (fun _ => True)
      (fun f => Q.size (rep.ty scalar) f ≤ width) scalarTime := by
    intro u _ z hz
    cases u
    exact ⟨hf z.value, hs z hz⟩
  have hpair := PairSampling.bound rep.data data (rep.ty scalar) (rep.ty scalar)
    sampling.scalar sampling.scalar sizes laws dataLaws mono control queryCost routing
    width scalarTime scalarTime hh hu component component
  have hm : overhead (128 * (3 * width)) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hm' : overhead (8 * (3 * width)) ≤ fee :=
    (mono (show 8 * (3 * width) ≤ 128 * (3 * width) by omega)).trans hm
  have hm'' : overhead (8 * width) ≤ fee := (mono (by omega)).trans hm'
  have hd : Bounds control queryCost (PrivateCache.pairSampler rep data sampling) (fun _ => True)
      (fun p => Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width) (2 * scalarTime + 12 * fee) := by
    intro u _ z hz
    have h := hpair u True.intro z hz
    exact ⟨hp z.value, by omega⟩
  have result := CacheRead.bound rep data (index.code rep data cost primitive)
    (pairZeroCode rep data cost primitive (inputTy index.ty (.pair scalar scalar)))
    (PrivateCache.pairSampler rep data sampling) sizes lists laws dataLaws mono control queryCost routing
    k cache (3 * width) cap (topicTime + 2 * indexTime + natTime + 134 * overhead (128 * (3 * width)))
    (2 * zeroTime + 5 * overhead (8 * (3 * width))) (2 * scalarTime + 12 * fee)
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (hk.trans hw) (hc.trans hw)
    (fun p hmem => ⟨(he p hmem).trans hw, hp p.2⟩) hlen (hp (0, 0))
    (fun x y hx hy => index.native_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
      x y (3 * width) topicTime indexTime natTime (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw)
      (fun j hj => (hn j hj).trans hw) hx hy ht hi heq) hzero hd out hout
  refine ⟨result.1, result.2.trans ?_⟩
  dsimp [badTime, fee] at *
  nlinarith [Nat.mul_le_mul_left (134 * cap) hm]

end Signatures.Runtime.WeightedAGM.Read

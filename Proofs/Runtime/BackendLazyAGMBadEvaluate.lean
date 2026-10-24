import Proofs.Runtime.BackendLazyAGMBadBody
import Proofs.Runtime.BackendLazyAGMEvaluateBudget
import Proofs.Runtime.BackendLengthCost

/-! Complete runtime certificate for the native bad-branch row evaluator.
Its budget is derived from individual primitive, sampler, and loop-control
contracts and the sizes of the actual input rows and private cache. -/

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

theorem backendEvaluateBad_bound (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F) (cache : List (M × (F × F)))
    (width rowCap initialCacheCap natEqTime natSubTime natAddTime messageEqTime
      scalarTime zeroTime addTime mulTime tickTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ rowCap + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hr : ∀ row ∈ rows, Q.size (rep.ty evalRowTy) row ≤ width)
    (hd : Q.size (rep.ty evalRowTy) default ≤ width) (hl : rows.length ≤ rowCap)
    (hc : cache.length ≤ initialCacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hne : ∀ k ≤ rowCap, (primitiveBound CryptoOp.natEq).time (k, 0) ≤ natEqTime)
    (hns : ∀ k ≤ rowCap, (primitiveBound CryptoOp.natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ rowCap, (primitiveBound CryptoOp.natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : M,
      Q.size (rep.ty message) x ≤ 3 * evaluationWidth (3 * width) rowCap (initialCacheCap + rowCap) →
      Q.size (rep.ty message) y ≤ 3 * evaluationWidth (3 * width) rowCap (initialCacheCap + rowCap) →
        (primitiveBound CryptoOp.messageEq).time (x, y) ≤ messageEqTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hm : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ rowCap, ∀ encoded ≤ 7 * evaluationWidth (3 * width) rowCap (initialCacheCap + rowCap),
      control.loop n encoded ≤ tickTime)
    (out : Run ((F × F) × List (M × (F × F))))
    (hout : out ∈ support ((backendEvaluateBad rep data cost primitive sampling).run
      control queryCost ((rows, default, ()), cache))) :
    let capacity := initialCacheCap + rowCap
    let W := evaluationWidth (3 * width) rowCap capacity
    let fee := overhead (32 * CacheCompiler.frameWidth (3 * W) capacity)
    (Q.size (rep.ty (.pair scalar scalar)) out.value.1 ≤ W ∧ Q.size (rep.ty (cacheTy (.pair scalar scalar))) out.value.2 ≤ W) ∧
      out.steps ≤ rowCap * (rowCap * (natEqTime + natSubTime + 257 * fee) +
        capacity * (messageEqTime + 257 * fee) + 2 * natAddTime + 2 * addTime + 2 * mulTime +
        2 * scalarTime + 2 * zeroTime + 600 * fee + tickTime) + 2 * zeroTime + tickTime + 128 * fee := by
  let capacity := initialCacheCap + rowCap
  let W := evaluationWidth (3 * width) rowCap capacity
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * W) capacity)
  let bodyTime := rowCap * (natEqTime + natSubTime + 257 * fee) +
    capacity * (messageEqTime + 257 * fee) + natAddTime + 2 * addTime + 2 * mulTime + 2 * scalarTime + 2 * zeroTime + 564 * fee
  let inv := EvaluationRemaining (R := F × F) (fun m => Q.size (rep.ty message) m ≤ width) rowCap capacity
  have hw : width ≤ W := by dsimp [W, evaluationWidth]; nlinarith
  have h3 : width ≤ 3 * width := by omega
  have hpair (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at h
    omega
  have hsmall : overhead (128 * W) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hlengthFee : overhead (128 * ((4 * rowCap + 16) * (3 * width))) ≤ fee := by
    apply (mono ?_).trans hsmall
    dsimp [W, evaluationWidth, capacity]
    nlinarith
  have htail : Q.size (rep.env [evalRowTy]) (default, ()) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty evalRowTy) rep.data.unit (default, ())
    change Q.size (rep.env [evalRowTy]) (default, ()) ≤ _ at h
    dsimp only at h
    omega
  have henv : Q.size (rep.env [.list evalRowTy, evalRowTy]) (rows, default, ()) ≤ W := by
    have h := evaluationFrame_size rep sizes lists (value := .pair scalar scalar) 0 ((0, 0) : F × F) rows default (3 * width) rowCap capacity
      (hh.trans h3) (hu.trans h3) ((hn 0 (by omega)).trans h3) (hpair (0, 0))
      (fun r h => (hr r h).trans h3) hl (hd.trans h3)
    exact (sizes.snd_le (rep.ty (evalStateTy (.pair scalar scalar))) (rep.env [.list evalRowTy, evalRowTy])
      ((0, ((0, 0) : F × F)), rows, default, ())).trans h
  have hcount : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (listLength (cell := evalRowTy) (Γ := [evalRowTy]) CryptoOp.natAdd)) (rows, default, ()) ≤
        rowCap * (natAddTime + 17 * fee) + 32 * fee := by
    have h := LengthCompiler.length_cost_bound rep data (arithmetic F G₁ G₂ M M cost) primitive
      laws dataLaws primitiveBound sizes lists mono (cell := evalRowTy) (Γ := [evalRowTy])
      CryptoOp.natAdd (fun _ _ => rfl) rows (default, ()) (3 * width) rowCap natAddTime
      (hh.trans h3) (hu.trans h3) htail (fun r h => (hr r h).trans h3) hl
      (fun k h => (hn k h).trans h3) hna
    have hmul := Nat.mul_le_mul_left rowCap (show natAddTime + 17 * overhead (128 * ((4 * rowCap + 16) * (3 * width))) ≤
      natAddTime + 17 * fee by omega)
    omega
  have hinit : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (.pair (.nat 0) (.pair (.op .zero .unit) (.op .zero .unit)) : Expr CryptoOp [.list evalRowTy, evalRowTy] (evalStateTy (.pair scalar scalar))))
        (rows, default, ()) ≤ 2 * zeroTime + 32 * overhead (128 * W) := by
    apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
      laws dataLaws primitiveBound _ _).trans
    have hzSize := (hf 0).trans hw
    have hnSize := (hn 0 (by omega)).trans hw
    have huSize := hu.trans hw
    have hhSize := hh.trans hw
    have hprod := @sizes.prod_le
    have hfee : ∀ k ≤ 128 * W, overhead k ≤ overhead (128 * W) := fun _ hk => mono hk
    dsimp only [Expression.compileBound, LocalBound.pair, LocalBound.compose,
      DataCostLaws.natBound, DataCostLaws.unitBound, Expr.denote, arithmetic,
      LanguageRepresentation.ty] at *
    grind only
  have hsize : ∀ remaining ≤ rowCap, ∀ p, inv remaining p →
      Q.size (rep.ty (evalStateTy (.pair scalar scalar))) p.1 ≤ W ∧ Q.size (rep.ty (cacheTy (.pair scalar scalar))) p.2 ≤ W := by
    intro remaining _ p hp
    obtain ⟨⟨n, acc⟩, saved⟩ := p
    obtain ⟨hncap, hccap, hkeys⟩ := hp
    dsimp only at hncap hccap hkeys ⊢
    have hnSize := hn n (by omega)
    have haSize := hpair acc
    have hstatePair := sizes.prod_le rep.data.nat (rep.ty (.pair scalar scalar)) (n, acc)
    dsimp only at hstatePair
    refine ⟨hstatePair.trans ?_, ?_⟩
    · dsimp [W, evaluationWidth]
      nlinarith
    · exact evaluationCache_size rep sizes lists (value := .pair scalar scalar) saved (3 * width) rowCap capacity (hh.trans h3)
        (fun p hp => ⟨(hkeys p hp).trans h3, hpair p.2⟩) (by omega)
  have hbody : ∀ remaining < rowCap, ∀ acc saved, inv (remaining + 1) (acc, saved) →
      ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
        (rep.ty (cacheTy (.pair scalar scalar))) (readEffect rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit)))
        (evalBody badCombine)).run control queryCost ((acc, rows, default, ()), saved)),
        inv remaining z.value ∧ z.steps ≤ bodyTime := by
    intro remaining _ acc saved hi z hz'
    exact badBody_budget rep data cost primitive laws dataLaws primitiveBound sizes lists mono control queryCost routing
      sampling acc.1 remaining acc.2 rows default saved width rowCap capacity
      natEqTime natSubTime natAddTime messageEqTime scalarTime zeroTime addTime mulTime
      hh hu hb hn hf hr hd hl hi hne hns hna he hsample hz ha hm z hz'
  have hbnd := backendEvaluate_bound rep data cost primitive laws dataLaws primitiveBound sizes mono
    control queryCost routing (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit)) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine rows default cache inv
    W rowCap (rowCap * (natAddTime + 17 * fee) + 32 * fee) (2 * zeroTime + 32 * overhead (128 * W))
    bodyTime tickTime (hh.trans hw) henv (fun k h => (hn k (by omega)).trans hw) hl
    (by exact ⟨by dsimp; omega, by dsimp [capacity]; omega, hk⟩) hsize hcount hinit hbody htick out
    (by simpa only [backendEvaluateBad] using hout)
  refine ⟨hbnd.1, ?_⟩
  have hmul := Nat.mul_le_mul_left rowCap (show bodyTime + 19 * overhead (128 * W) + tickTime ≤
    bodyTime + 19 * fee + tickTime by omega)
  dsimp only [bodyTime] at hbnd hmul
  change out.steps ≤ rowCap * (rowCap * (natEqTime + natSubTime + 257 * fee) +
    capacity * (messageEqTime + 257 * fee) + 2 * natAddTime + 2 * addTime + 2 * mulTime + 2 * scalarTime + 2 * zeroTime +
      600 * fee + tickTime) + 2 * zeroTime + tickTime + 128 * fee
  have htime := hbnd.2
  nlinarith only [htime, hsmall, hmul]

end Signatures.Runtime.LazyAGM

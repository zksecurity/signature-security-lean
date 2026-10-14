import Signatures.Runtime.BackendWeightedBody
import Signatures.Runtime.BackendWeightedSelect
import Signatures.Runtime.BackendWeightedUpdate
import Signatures.Runtime.BackendWeightedReadBudget
import Signatures.Runtime.BackendWeightedEvaluateSize
import Signatures.Runtime.BackendWeightedEvaluateState

/-! Closed good-branch iteration budget. The only time assumptions concern
individual primitives and scalar sampling. Selection, cache access, arithmetic,
retained contexts, and all compiler routing are composed for the actual code. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram Read
open LazyAGM (EvaluationRemaining)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws primitiveBound sizes lists mono routing

theorem goodBody_budget (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)
    (n remaining : Nat) (acc : F) (rows : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (default : index.ty.Value (cryptoBase F G₁ G₂ K M) × F) (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (width rowCap cacheCap natEqTime natSubTime natAddTime topicTime indexTime
      scalarTime zeroTime addTime mulTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ rowCap + index.bound + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hr : ∀ row ∈ rows, Q.size (rep.ty (evalRowTy index.ty)) row ≤ width)
    (hd : Q.size (rep.ty (evalRowTy index.ty)) default ≤ width) (hl : rows.length ≤ rowCap)
    (hi : EvaluationRemaining (fun m => Q.size (rep.ty index.ty) m ≤ width)
      rowCap cacheCap (remaining + 1) ((n, acc), cache))
    (hne : ∀ j k, j ≤ rowCap + index.bound → k ≤ rowCap + index.bound →
      (primitiveBound CryptoOp.natEq).time (j, k) ≤ natEqTime)
    (hns : ∀ k ≤ rowCap, (primitiveBound CryptoOp.natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ rowCap, (primitiveBound CryptoOp.natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : K,
      Q.size (rep.ty key) x ≤ evaluationWidth width rowCap cacheCap →
      Q.size (rep.ty key) y ≤ evaluationWidth width rowCap cacheCap →
        (primitiveBound CryptoOp.keyEq).time (x, y) ≤ topicTime)
    (hindex : ∀ j : Fin (index.bound + 1), (primitiveBound (.finVal index.bound)).time j ≤ indexTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hm : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ mulTime)
    (out : Run ((Nat × F) × List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (cacheTy index.ty scalar)) (readEffect rep (goodRead rep data cost primitive sampling index))
      (evalBody goodCombine)).run control queryCost (((n, acc), rows, default, ()), cache))) :
    let fee := overhead (32 * CacheCompiler.frameWidth (evaluationWidth width rowCap cacheCap) cacheCap)
    EvaluationRemaining (fun m => Q.size (rep.ty index.ty) m ≤ width) rowCap cacheCap remaining out.value ∧
      out.steps ≤ rowCap * (natEqTime + natSubTime + 257 * fee) +
        cacheCap * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + natAddTime + addTime + mulTime +
        scalarTime + zeroTime + 480 * fee := by
  let W := evaluationWidth width rowCap cacheCap
  let fee := overhead (32 * CacheCompiler.frameWidth W cacheCap)
  have hw : width ≤ W := by dsimp [W, evaluationWidth]; nlinarith
  have hfee : overhead (256 * W) ≤ fee := by
    apply mono
    dsimp [CacheCompiler.frameWidth]
    nlinarith
  have hsmall : overhead (128 * W) ≤ fee := (mono (by omega)).trans hfee
  obtain ⟨hcounter, hcapacity, hkeys⟩ := hi
  dsimp only at hcounter hcapacity hkeys
  have hncap : n ≤ rowCap := by omega
  have hc : cache.length ≤ cacheCap := by omega
  have hframe := evaluationFrame_size rep sizes lists (value := scalar) n acc rows default width rowCap cacheCap
    hh hu (hn n (by omega)) (hf acc) hr hl hd
  have hcache := evaluationCache_size rep sizes lists (value := scalar) cache width rowCap cacheCap hh
    (fun p hp => ⟨hkeys p hp, hf p.2⟩) hc
  let row := (rows[n]?).getD default
  have hrow : Q.size (rep.ty (evalRowTy index.ty)) row ≤ width := evaluationSelected_size rep rows default n width hr hd
  have hkey : Q.size (rep.ty index.ty) row.1 ≤ width :=
    (evaluationRow_key_size rep sizes row).trans hrow
  have hrowsKeys : ∀ r ∈ rows, Q.size (rep.ty index.ty) r.1 ≤ width :=
    fun r h => (evaluationRow_key_size rep sizes r).trans (hr r h)
  have hdefaultKey := (evaluationRow_key_size rep sizes default).trans hd
  have hselect := selectRow_time_bound rep data cost primitive laws dataLaws primitiveBound sizes mono (value := scalar)
    n acc rows default W rowCap natEqTime natSubTime (hh.trans hw) (hu.trans hw) hframe
    (fun b => (hb b).trans hw) (fun k hk => (hn k (by omega)).trans hw) (hd.trans hw)
    (fun r h => (hr r h).trans hw) hl
    (by
      intro xs hlen hmem
      have h := evaluationRows_size rep lists xs width rowCap hh (fun r hx => hr r (hmem r hx)) hlen
      exact h.trans (by dsimp [W, evaluationWidth]; nlinarith))
    (fun k hk => hne k 0 (by omega) (by omega)) (fun k hk => hns k (by omega))
  have hselectCost := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost)
    primitive laws dataLaws primitiveBound (selectRow (value := scalar)) _).trans hselect
  have hread : ∀ z ∈ support ((goodRead rep data cost primitive sampling index).run control queryCost (row.1, cache)),
      (Q.size (rep.ty scalar) z.value.1 ≤ W ∧ Q.size (rep.ty (cacheTy index.ty scalar)) z.value.2 ≤ W) ∧
      z.steps ≤ cacheCap * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + scalarTime + zeroTime + 192 * fee := by
    intro z hz'
    have hbnd := goodRead_bound rep data cost primitive sizes laws dataLaws primitiveBound mono
      sampling index lists control queryCost routing row.1 cache W cacheCap topicTime indexTime natEqTime scalarTime zeroTime
      (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw)
      (fun j hj => (hn j (by omega)).trans hw) (hkey.trans hw) hcache
      (fun p hp => (hkeys p hp).trans hw) hc (fun f => (hf f).trans hw) he hindex
      (fun j k hj hk => hne j k (by omega) (by omega)) hsample hz z hz'
    have hstate := backendRead_state rep (goodRead rep data cost primitive sampling index)
      (goodRead_denote rep data cost primitive sampling index) control queryCost
      (fun m => Q.size (rep.ty index.ty) m ≤ width) row.1 cache hkey hkeys z hz'
    have hs := evaluationCache_size rep sizes lists (value := scalar) z.value.2 width rowCap cacheCap hh
      (fun p hp => ⟨hstate.2 p hp, hf p.2⟩) (by omega)
    refine ⟨⟨(hf z.value.1).trans hw, hs⟩, ?_⟩
    have ht := hbnd.2
    dsimp only [Read.goodTime] at ht
    dsimp only [fee]
    omega
  have hupdate (answer : F) :
      Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (evalUpdate goodCombine))
        (answer, row, (n, acc), rows, default, ()) ≤ natAddTime + addTime + mulTime + 128 * overhead (128 * W) := by
    apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
      laws dataLaws primitiveBound _ _).trans
    exact goodUpdate_time_bound rep data cost primitive laws dataLaws primitiveBound sizes mono
      answer acc row n rows default W natAddTime addTime mulTime (hh.trans hw)
      (evaluationUpdateFrame_size rep sizes lists (value := scalar) n answer acc row rows default width rowCap cacheCap
        hh hu (hn n (by omega)) (hf acc) (hf answer) hrow hr hl hd)
      ((hn 1 (by omega)).trans hw) ((hn (n + 1) (by omega)).trans hw)
      (fun f => (hf f).trans hw) (hna n hncap) ha hm
  have hresult (answer : F) : Q.size (rep.ty (evalStateTy scalar))
      ((evalUpdate goodCombine).denote (arithmetic F G₁ G₂ K M cost)
        (answer, row, (n, acc), rows, default, ())) ≤ W := by
    rw [evalUpdate_denote cost]
    have hp := sizes.prod_le rep.data.nat (rep.ty scalar)
      (n + 1, goodCombine.denote (arithmetic F G₁ G₂ K M cost) (answer, row.2, acc, ()))
    have hn' := hn (n + 1) (by omega)
    have hf' := hf (goodCombine.denote (arithmetic F G₁ G₂ K M cost) (answer, row.2, acc, ()))
    change Q.size (rep.ty (evalStateTy scalar)) _ ≤ _ at hp
    dsimp only at hp
    exact hp.trans (by dsimp [W, evaluationWidth]; nlinarith)
  have hbnd := evalBody_bound rep data cost primitive laws dataLaws primitiveBound sizes mono
    control queryCost routing (goodRead rep data cost primitive sampling index) goodCombine n acc rows default cache
    W (rowCap * (natEqTime + natSubTime + 257 * overhead (128 * W)) + 96 * overhead (128 * W))
    (cacheCap * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + scalarTime + zeroTime + 192 * fee)
    (natAddTime + addTime + mulTime + 128 * overhead (128 * W))
    (hh.trans hw) hframe hcache (by rw [selectRow_denote cost]; exact hrow.trans hw) hselectCost
    (by simpa only [selectRow_denote cost] using hread)
    (by intro answer _; rw [selectRow_denote cost]; exact hupdate answer)
    (by intro answer _; rw [selectRow_denote cost]; exact hresult answer) out hout
  have hinv := evalBody_remaining rep data cost primitive (goodRead rep data cost primitive sampling index)
    (goodRead_denote rep data cost primitive sampling index) goodCombine control queryCost
    (fun m => Q.size (rep.ty index.ty) m ≤ width) rowCap cacheCap remaining n acc rows default cache
    hrowsKeys hdefaultKey ⟨hcounter, hcapacity, hkeys⟩ out hout
  refine ⟨hinv, ?_⟩
  have hmul := Nat.mul_le_mul_left rowCap (show natEqTime + natSubTime + 257 * overhead (128 * W) ≤
    natEqTime + natSubTime + 257 * fee by omega)
  change out.steps ≤ rowCap * (natEqTime + natSubTime + 257 * fee) +
    cacheCap * (topicTime + 2 * indexTime + natEqTime + 391 * fee) + natAddTime + addTime + mulTime + scalarTime + zeroTime + 480 * fee
  omega

end Signatures.Runtime.WeightedAGM.Evaluate

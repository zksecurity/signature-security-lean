import Signatures.Runtime.BackendLazyAGMBadEvaluate
import Signatures.Runtime.BackendLazyAGMTokensAssembly
import Signatures.Runtime.BackendLazyAGMTokensSize
import Signatures.Runtime.BackendLazyAGMExtractionState

/-! Complete native bad-branch chronological transcript evaluation budget.
Coefficient preparation, evaluation, argument copying, and retained contexts
are composed from their implemented code and individual primitive contracts. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

def badTokenTime (overhead : Nat → Nat) (width tokenCap coeffCap cacheCap
    natEqTime natSubTime natAddTime messageEqTime scalarTime zeroTime addTime mulTime tickTime : Nat) : Nat :=
  let capacity := cacheCap + tokenCap
  let W := evaluationWidth (9 * width) tokenCap capacity
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * W) capacity)
  TokenCompiler.rowsTime overhead (3 * width) tokenCap coeffCap natEqTime natSubTime natAddTime zeroTime +
    (tokenCap * (tokenCap * (natEqTime + natSubTime + 257 * fee) +
      capacity * (messageEqTime + 257 * fee) + 2 * natAddTime + 2 * addTime + 2 * mulTime +
      2 * scalarTime + 2 * zeroTime + 600 * fee + tickTime) + 2 * zeroTime + tickTime + 128 * fee) +
    64 * overhead (512 * tokenFrameWidth width tokenCap coeffCap cacheCap)

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

theorem badTokens_budget (sampling : MachineCompiler.SamplingImplementation Q iface rep)
    (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F) (cache : List (M × (F × F)))
    (width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime messageEqTime
      scalarTime zeroTime addTime mulTime tickTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ k ≤ tokenCap + 1, Q.size rep.data.nat k ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : ∀ token ∈ tr, Q.size (rep.ty (AGM.tokenTy message)) token ≤ width)
    (hd : Q.size (rep.ty evalRowTy) default ≤ width)
    (hnt : tr.length ≤ tokenCap) (hnc : coeff.length ≤ coeffCap)
    (hc : cache.length ≤ cacheCap) (hk : ∀ p ∈ cache, Q.size (rep.ty message) p.1 ≤ width)
    (hne : ∀ k ≤ tokenCap, (primitiveBound CryptoOp.natEq).time (k, 0) ≤ natEqTime)
    (hns : ∀ k ≤ tokenCap, (primitiveBound CryptoOp.natSub).time (k, 1) ≤ natSubTime)
    (hna : ∀ k ≤ tokenCap, (primitiveBound CryptoOp.natAdd).time (k, 1) ≤ natAddTime)
    (he : ∀ x y : M,
      Q.size (rep.ty message) x ≤ 3 * evaluationWidth (9 * width) tokenCap (cacheCap + tokenCap) →
      Q.size (rep.ty message) y ≤ 3 * evaluationWidth (9 * width) tokenCap (cacheCap + tokenCap) →
        (primitiveBound CryptoOp.messageEq).time (x, y) ≤ messageEqTime)
    (hsample : ∀ z ∈ support (sampling.scalar.run control queryCost ()), z.steps ≤ scalarTime)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hm : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ mulTime)
    (htick : ∀ n ≤ tokenCap, ∀ encoded ≤ 7 * evaluationWidth (9 * width) tokenCap (cacheCap + tokenCap),
      control.loop n encoded ≤ tickTime)
    (out : Run ((F × F) × List (M × (F × F))))
    (hout : out ∈ support ((backendEvaluateTokens rep data cost primitive (pairSampler rep data sampling)
      (.pair (.op .zero .unit) (.op .zero .unit)) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine).run control queryCost ((tr, coeff, default, ()), cache))) :
    (Q.size (rep.ty (.pair scalar scalar)) out.value.1 ≤ tokenFrameWidth width tokenCap coeffCap cacheCap ∧
      Q.size (rep.ty (cacheTy (.pair scalar scalar))) out.value.2 ≤ tokenFrameWidth width tokenCap coeffCap cacheCap ∧
      out.value.2.length ≤ cacheCap + tokenCap ∧ ∀ entry ∈ out.value.2, Q.size (rep.ty message) entry.1 ≤ width) ∧
      out.steps ≤ badTokenTime overhead width tokenCap coeffCap cacheCap natEqTime natSubTime natAddTime
        messageEqTime scalarTime zeroTime addTime mulTime tickTime := by
  let rows := ((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]).denote
    (arithmetic F G₁ G₂ M M cost) (tr, coeff, default, ())
  let W := tokenFrameWidth width tokenCap coeffCap cacheCap
  let E := evaluationWidth (9 * width) tokenCap (cacheCap + tokenCap)
  let fee := overhead (32 * CacheCompiler.frameWidth (3 * E) (cacheCap + tokenCap))
  let evalTime := tokenCap * (tokenCap * (natEqTime + natSubTime + 257 * fee) +
    (cacheCap + tokenCap) * (messageEqTime + 257 * fee) + 2 * natAddTime + 2 * addTime + 2 * mulTime +
    2 * scalarTime + 2 * zeroTime + 600 * fee + tickTime) + 2 * zeroTime + tickTime + 128 * fee
  have h3 : width ≤ 3 * width := by omega
  have hw : width ≤ W := by dsimp [W, tokenFrameWidth, evaluationWidth]; nlinarith
  have hE : E ≤ W := by dsimp [E, W, tokenFrameWidth, evaluationWidth]; nlinarith
  have hrows := tokenRows_entries rep sizes cost tr coeff default width hh hf ht
  have hrowCap : rows.length ≤ tokenCap := by
    have hlen : rows.length = tr.length := hrows.1
    exact hlen.trans_le hnt
  have htail : Q.size (rep.env [evalRowTy]) (default, ()) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty evalRowTy) rep.data.unit (default, ())
    change Q.size (rep.env [evalRowTy]) (default, ()) ≤ _ at h
    dsimp only at h
    omega
  have hprep := TokenCompiler.rows_cost_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    (dataTy := message) (Γ := [evalRowTy]) tr coeff (default, ()) (3 * width) tokenCap coeffCap natEqTime natSubTime natAddTime zeroTime
    (hh.trans h3) (hu.trans h3) htail (fun b => (hb b).trans h3) (fun n hn' => (hn n hn').trans h3)
    (fun f => (hf f).trans h3) (fun p hp => (ht p hp).trans h3) hnt hnc hne hns hna hz
  have hrowsSize : Q.size (rep.ty (.list evalRowTy)) rows ≤ W := by
    have h := TokenCompiler.rows_output_size rep cost sizes lists (dataTy := message) (Γ := [evalRowTy])
      tr coeff (default, ()) width tokenCap hh hf ht hnt
    exact h.trans (by dsimp [W, tokenFrameWidth, evaluationWidth]; nlinarith)
  have hpair (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 3 * width := by
    have hp := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at hp
    omega
  have hcacheSize := tokenCache_size rep sizes lists (value := .pair scalar scalar) cache width tokenCap coeffCap cacheCap hh hk
    hpair hc
  have hbase : 3 * (3 * width) = 9 * width := by omega
  have heval : ∀ z ∈ support ((backendEvaluate rep data cost primitive (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))
      (.pair (.op .zero .unit) (.op .zero .unit)) badCombine).run control queryCost ((rows, default, ()), cache)),
      (Q.size (rep.ty (.pair scalar scalar)) z.value.1 ≤ W ∧ Q.size (rep.ty (cacheTy (.pair scalar scalar))) z.value.2 ≤ W) ∧ z.steps ≤ evalTime := by
    intro z hz'
    have h := backendEvaluateBad_bound rep data cost primitive laws dataLaws primitiveBound sizes lists mono
      control queryCost routing sampling rows default cache (3 * width) tokenCap cacheCap natEqTime natSubTime natAddTime
      messageEqTime scalarTime zeroTime addTime mulTime tickTime (hh.trans h3) (hu.trans h3)
      (fun b => (hb b).trans h3) (fun n hn' => (hn n hn').trans h3) (fun f => (hf f).trans h3)
      (fun row hr => (hrows.2 row hr).1) (hd.trans h3) hrowCap hc (fun p hp => (hk p hp).trans h3)
      hne hns hna (by simpa only [hbase] using he) hsample hz ha hm
      (by simpa only [hbase] using htick) z (by rw [backendEvaluateBad]; exact hz')
    simp only [hbase] at h
    exact ⟨⟨h.1.1.trans hE, h.1.2.trans hE⟩, h.2⟩
  have hbnd := evaluateTokens_bound rep data cost primitive laws dataLaws primitiveBound sizes mono control queryCost routing
    (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit)) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine tr coeff default cache W
    (TokenCompiler.rowsTime overhead (3 * width) tokenCap coeffCap natEqTime natSubTime natAddTime zeroTime) evalTime
    (hh.trans hw) (hu.trans hw) (tokenInput_size rep sizes lists tr coeff default width tokenCap coeffCap cacheCap hh hu hf ht hd hnt hnc)
    hcacheSize hrowsSize hprep heval out hout
  have hstate := evaluateTokens_state rep data cost primitive control queryCost (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))
    (pairSampler_denote rep data sampling ()) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine (fun _ _ => rfl)
    (fun answer coeff acc => badCombine_denote (G₁ := G₁) (G₂ := G₂) (M := M) cost answer acc coeff)
    (fun m => Q.size (rep.ty message) m ≤ width) tr coeff default cache
    (fun p hp => (sizes.fst_le (rep.ty message) (rep.ty point₁) p).trans (ht p hp)) hk out hout
  exact ⟨⟨hbnd.1.1, hbnd.1.2, by omega, hstate.2⟩, hbnd.2⟩

end Signatures.Runtime.LazyAGM

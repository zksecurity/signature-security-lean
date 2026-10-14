import Signatures.Runtime.BackendWeightedReplyCost
import Signatures.Runtime.BackendWeightedReplySize
import Signatures.Runtime.BackendCallerRouting

/-! Composition of the actual weighted reply with its private read/evaluator.
The component certificate is for the value computation alone. This theorem
derives the extra cost of retaining the original request, configuration, cache
and transcript, constructing arguments, and computing and recording the reply.
Specialized budgets discharge the component and response obligations. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Reply

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
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

/-- Includes both the returned cache and the retained pre-reply store. -/
def replyWidth (width valueWidth : Nat) : Nat := 32 * width + valueWidth

include laws dataLaws primitiveBound sizes lists mono routing

theorem backendReply_bound {indexTy messageTy value config : Ty CryptoAtom}
    (signing : Bool)
    (valueCode : Code Q unifSpec iface
      (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value)))
    (response : Expr CryptoOp [value, config] point₁)
    (request : (requestTy indexTy messageTy signing).Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy indexTy messageTy value config).Value (cryptoBase F G₁ G₂ K M))
    (width valueWidth valueTime resultTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hm : Q.size (rep.ty (requestTy indexTy messageTy signing)) request ≤ width)
    (hs : Q.size (rep.ty (storeTy indexTy messageTy value config)) saved ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hv : ∀ z ∈ support (valueCode.run control queryCost (request, saved.2.1)),
      Q.size (rep.ty (cacheResultTy indexTy value)) z.value ≤ valueWidth ∧ z.steps ≤ valueTime)
    (hr : ∀ env, Q.size (rep.env [cacheResultTy indexTy value,
      requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) env ≤ replyWidth width valueWidth →
      Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
        (replyResult signing response)) env ≤ resultTime)
    (out : Run (G₁ × (storeTy indexTy messageTy value config).Value (cryptoBase F G₁ G₂ K M)))
    (hout : out ∈ support ((backendReply rep data cost primitive signing valueCode response).run
      control queryCost (request, saved))) :
    Q.size (rep.ty (.pair point₁ (storeTy indexTy messageTy value config))) out.value ≤
        16 * replyWidth width valueWidth ∧
      out.steps ≤ valueTime + resultTime + 32 * overhead (64 * replyWidth width valueWidth) := by
  let W := replyWidth width valueWidth
  let fee := overhead (64 * W)
  let env : Env (cryptoBase F G₁ G₂ K M)
      [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config] := (request, saved, ())
  let args := (cacheArgs (value := value) signing).denote (arithmetic F G₁ G₂ K M cost) env
  have hw : width ≤ W := by dsimp [W, replyWidth]; omega
  have h5 : width ≤ 5 * width := by omega
  have henv : Q.size (rep.env [requestTy indexTy messageTy signing,
      storeTy indexTy messageTy value config]) env ≤ 5 * width :=
    replyFrame_size rep sizes signing (request, saved) width hh hu hm hs
  have hargs : Q.size (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value))) args ≤
      15 * width := by
    have h := cacheArgs_size rep sizes cost signing env (5 * width) (hh.trans h5) henv
    exact h.trans (by omega)
  have hinput : Q.size (rep.ty (.pair (requestTy indexTy messageTy signing)
      (storeTy indexTy messageTy value config))) (request, saved) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty (requestTy indexTy messageTy signing))
      (rep.ty (storeTy indexTy messageTy value config)) (request, saved)
    dsimp only at h
    exact h.trans (by omega)
  have hpacked : Q.size (StepClass.HasProd.prod
      (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
      (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config])) (args, env) ≤ W := by
    have h := sizes.prod_le
      (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
      (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) (args, env)
    dsimp only at h
    dsimp only [W, replyWidth]
    omega
  rw [backendReply] at hout
  simp only [Code.run, sequenceRun, retainRun, mem_support_bind_iff, support_map,
    Set.mem_image, support_pure, Set.mem_singleton_iff, exists_eq_left] at hout
  obtain ⟨_, ⟨_, ⟨_, ⟨cached, hcached, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hout
  have hc := hv cached hcached
  have hcachedSize : Q.size (rep.env [cacheResultTy indexTy value,
      requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) (cached.value, env) ≤ W := by
    have h := sizes.prod_le (rep.ty (cacheResultTy indexTy value))
      (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) (cached.value, env)
    change Q.size (rep.env [cacheResultTy indexTy value,
      requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) (cached.value, env) ≤ _ at h
    dsimp only at h
    dsimp only [W, replyWidth]
    omega
  have hfinal := replyResult_size rep sizes lists cost signing response (cached.value, env) W
    (hh.trans hw) hcachedSize (fun g => (hg g).trans hw)
  have hfinalCost := hr (cached.value, env) hcachedSize
  have hfee : ∀ n ≤ 64 * W, overhead n ≤ fee := fun _ hn => mono hn
  have hframeCost : Q.cost (replyFrame (value := value) (config := config) rep data signing)
      (request, saved) ≤ 5 * fee := by
    have hprod := @sizes.prod_le
    have hfst := @sizes.fst_le
    have hsnd := @sizes.snd_le
    have hlocal := (LocalBound.pair laws
      (LocalBound.fst laws (rep.ty (requestTy indexTy messageTy signing)) (rep.ty (storeTy indexTy messageTy value config)))
      (LocalBound.pair laws
        (LocalBound.snd laws (rep.ty (requestTy indexTy messageTy signing)) (rep.ty (storeTy indexTy messageTy value config)))
        (dataLaws.unitBound (rep.ty (.pair (requestTy indexTy messageTy signing)
          (storeTy indexTy messageTy value config)))))).cost_le (request, saved)
    change Q.cost (replyFrame rep data signing) (request, saved) ≤ _ at hlocal
    apply hlocal.trans
    dsimp only [LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound,
      LanguageRepresentation.env, LanguageRepresentation.ty, env] at *
    grind only
  have ha : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (cacheArgs (value := value) signing)) env ≤ 16 * fee := by
    apply (cacheArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
      signing env (5 * width) (hh.trans h5) henv).trans
    exact Nat.mul_le_mul_left 16 (hfee _ (by dsimp [W, replyWidth]; omega))
  have hprepareCost : Q.cost (QP.pair
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (cacheArgs signing))
      (Q.identity (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]))) env ≤
      18 * fee := by
    have hp := laws.pair
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (cacheArgs (value := value) signing))
      (Q.identity (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config])) env
    have hid := laws.identity (rep.env [requestTy indexTy messageTy signing,
      storeTy indexTy messageTy value config]) env
    have henvW : Q.size (rep.env [requestTy indexTy messageTy signing,
        storeTy indexTy messageTy value config]) env ≤ W := by dsimp [W, replyWidth]; omega
    dsimp only [id_eq] at hp
    have hf := hfee _ (show Q.size (rep.env [requestTy indexTy messageTy signing,
        storeTy indexTy messageTy value config]) env +
      Q.size (StepClass.HasProd.prod
        (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
        (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config])) (args, env) ≤ 64 * W by omega)
    have hi := hfee _ (show Q.size (rep.env [requestTy indexTy messageTy signing,
      storeTy indexTy messageTy value config]) env ≤ 64 * W by omega)
    exact hp.trans (by dsimp only [args] at hf; omega)
  have hcall := routing.localCall
  have hseq := routing.sequence
  have hretain := routing.retain
  refine ⟨hfinal, ?_⟩
  dsimp only [Run.steps, Run.value, env, args, fee, W, replyWidth, requestTy, id_eq,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.WeightedAGM.Reply

import Proofs.Runtime.BackendWeightedReplyCost
import Proofs.Runtime.BackendCallerRouting

/-! The signing-value prefix executes both the term generator and the fallback
generator before the private-cache evaluator. Its runtime includes the retained
cache at both local calls and both sequence edges. -/

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
  {header : Nat} (sizes : SizeLaws Q header)
  (mono : Monotone overhead) (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws sizes mono routing

theorem signValue_bound {indexTy messageTy value : Ty CryptoAtom}
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy))
    (evaluate : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list (Terms.termTy indexTy), Terms.termTy indexTy])
        (rep.ty (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value)))
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (width outputWidth termsTime defaultTime evaluateTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hm : Q.size (rep.ty messageTy) m ≤ width)
    (hc : Q.size (rep.ty (cacheTy indexTy value)) cache ≤ width)
    (ht : Q.size (rep.ty (.list (Terms.termTy indexTy)))
      (terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())) ≤ width)
    (hd : Q.size (rep.ty (Terms.termTy indexTy))
      (default.denote (arithmetic F G₁ G₂ K M cost) (m, ())) ≤ width)
    (htime : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive terms)
      (m, ()) ≤ termsTime)
    (hdtime : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive default)
      (m, ()) ≤ defaultTime)
    (he : ∀ z ∈ support (evaluate.run control queryCost
      ((terms.denote (arithmetic F G₁ G₂ K M cost) (m, ()),
        default.denote (arithmetic F G₁ G₂ K M cost) (m, ()), ()), cache)),
      Q.size (rep.ty (cacheResultTy indexTy value)) z.value ≤ outputWidth ∧ z.steps ≤ evaluateTime)
    (out : Run (value.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((signValue rep data cost primitive terms default evaluate).run
      control queryCost (m, cache))) :
    Q.size (rep.ty (cacheResultTy indexTy value)) out.value ≤ outputWidth ∧
      out.steps ≤ termsTime + defaultTime + evaluateTime + 16 * overhead (64 * width) := by
  let fee := overhead (64 * width)
  let env : Env (cryptoBase F G₁ G₂ K M) [messageTy] := (m, ())
  let rows := terms.denote (arithmetic F G₁ G₂ K M cost) env
  let fallback := default.denote (arithmetic F G₁ G₂ K M cost) env
  have hfee : ∀ n ≤ 64 * width, overhead n ≤ fee := fun _ hn => mono hn
  have hprod := @sizes.prod_le
  have hframe : Q.cost (messageFrame rep data) m ≤ 3 * fee := by
    have h := (LocalBound.pair laws (LocalBound.identity laws (rep.ty messageTy))
      (dataLaws.unitBound (rep.ty messageTy))).cost_le m
    change Q.cost (messageFrame rep data) m ≤ _ at h
    apply h.trans
    dsimp only [LocalBound.pair, LocalBound.identity, DataCostLaws.unitBound, id_eq,
      LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hargs : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive
      (signArgs terms default)) env ≤ termsTime + defaultTime + 3 * fee := by
    have htail := laws.pair
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive default)
      (data.unit (rep.env [messageTy])) env
    have hhead := laws.pair
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive terms)
      (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive (.cons default .nil)) env
    have hunit := dataLaws.unit (rep.env [messageTy]) env
    change Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive
      (signArgs terms default)) env ≤ _ at hhead
    apply hhead.trans
    dsimp only [Expression.arguments, Args.denote, LanguageRepresentation.env, env] at *
    grind only
  rw [signValue] at hout
  simp only [Code.run, sequenceRun, retainRun, map_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, exists_eq_left] at hout
  obtain ⟨_, ⟨evaluated, hevaluated, rfl⟩, rfl⟩ := hout
  have hb := he evaluated hevaluated
  have hcall := routing.localCall
  have hseq := routing.sequence
  have hretain := routing.retain
  refine ⟨hb.1, ?_⟩
  dsimp only [Run.steps, Run.value, signArgs, Args.denote, env, rows, fallback, fee,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.WeightedAGM.Reply

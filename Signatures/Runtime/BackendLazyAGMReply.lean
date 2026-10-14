import Signatures.Runtime.BackendLazyAGMCache
import Signatures.Runtime.LazyAGMReply

/-! Actual common-backend hash/sign routines for both lazy BLS AGM solvers.
Local routing and reply arithmetic are compiled expressions; the only sampled
values come from the checked finite-cache implementation. The complete state
is passed explicitly and updated by the routine, including reverse reply logs.
These semantic statements do not assert the unfinished whole-solver budget.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
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
  {value config : Ty CryptoAtom}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
  (fallback : Expr CryptoOp [message, storeTy value config] value)
  (response : Expr CryptoOp [value, config] point₁)

def replyFrame : Q.Realizer (rep.ty (.pair message (storeTy value config)))
    (rep.env [message, storeTy value config]) (fun p => (p.1, p.2, ())) :=
  QP.pair (QP.fst _ _) (QP.pair (QP.snd _ _) (data.unit _))

@[irreducible] def replyBody (signing : Bool) :
    Code Q unifSpec iface (rep.env [message, storeTy value config])
      (rep.ty (.pair point₁ (storeTy value config))) :=
  .seq (.atomic (QP.pair
      (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (cacheArgs fallback))
      (Q.identity (rep.env [message, storeTy value config]))))
    (.seq (SampledCache.code rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.env [message, storeTy value config]) sampler .messageEq)
      (.atomic (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
        (replyResult signing response))))

@[irreducible] def backendReply (signing : Bool) :
    Code Q unifSpec iface (rep.ty (.pair message (storeTy value config)))
      (rep.ty (.pair point₁ (storeTy value config))) :=
  .seq (.atomic (replyFrame rep data)) (replyBody rep data cost primitive sampler fallback response signing)

variable [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))]
  (hsample : sampler.denote () = ($ᵗ (value.Value (cryptoBase F G₁ G₂ M M)) : ProbComp _))

include hsample in
omit [SampleableType F] in
theorem replyBody_denote (signing : Bool) (m : M)
    (cfg : config.Value (cryptoBase F G₁ G₂ M M))
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (tr : Model.LazyAGM.Transcript M M G₁) :
    (replyBody rep data cost primitive sampler fallback response signing).denote (m, (cfg, cache, tr), ()) =
      (fun p => let r := response.denote (arithmetic F G₁ G₂ M M cost) (p.1, cfg, ())
        (r, cfg, p.2, record signing m r tr)) <$>
          ((BLS.LazyAGM.Reduction.privateListOracle (M := M)
            (R := value.Value (cryptoBase F G₁ G₂ M M))) (.inr m)).run cache := by
  rw [replyBody]
  simp only [Code.denote, pure_bind]
  rw [cacheArgs_denote]
  rw [SampledCache.uniform rep data (arithmetic F G₁ G₂ M M cost) primitive
    (rep.env [message, storeTy value config]) CryptoOp.messageEq sampler hsample (fun _ _ => rfl)]
  simp only [bind_pure_comp, Functor.map_map]
  congr 1
  funext p
  exact replyResult_denote cost signing response m cfg cache p.2 tr p.1

include hsample in
omit [SampleableType F] in
theorem backendReply_denote (signing : Bool) (m : M)
    (cfg : config.Value (cryptoBase F G₁ G₂ M M))
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (tr : Model.LazyAGM.Transcript M M G₁) :
    (backendReply rep data cost primitive sampler fallback response signing).denote (m, cfg, cache, tr) =
      (fun p => let r := response.denote (arithmetic F G₁ G₂ M M cost) (p.1, cfg, ())
        (r, cfg, p.2, record signing m r tr)) <$>
          ((BLS.LazyAGM.Reduction.privateListOracle (M := M)
            (R := value.Value (cryptoBase F G₁ G₂ M M))) (.inr m)).run cache := by
  rw [backendReply]
  simp only [Code.denote, pure_bind]
  exact replyBody_denote rep data cost primitive sampler fallback response hsample signing m cfg cache tr

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
@[irreducible] def backendGoodReply
    (samplingCode : MachineCompiler.SamplingImplementation Q iface rep) (signing : Bool) :
    Code Q unifSpec iface (rep.ty (.pair message (storeTy scalar goodConfigTy)))
      (rep.ty (.pair point₁ (storeTy scalar goodConfigTy))) :=
  backendReply rep data cost primitive samplingCode.scalar (.op .zero .unit) (goodResponse signing) signing

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
@[irreducible] def backendBadReply
    (samplingCode : MachineCompiler.SamplingImplementation Q iface rep) (signing : Bool) :
    Code Q unifSpec iface (rep.ty (.pair message (storeTy (.pair scalar scalar) badConfigTy)))
      (rep.ty (.pair point₁ (storeTy (.pair scalar scalar) badConfigTy))) :=
  backendReply rep data cost primitive (pairSampler rep data samplingCode)
    (.pair (.op .zero .unit) (.op .zero .unit)) (badResponse signing) signing

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
theorem backendGoodReply_denote (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (signing : Bool) (m : M) (g X : G₁) (cache : List (M × F))
    (tr : Model.LazyAGM.Transcript M M G₁) :
    (backendGoodReply rep data cost primitive samplingCode signing).denote (m, (g, X), cache, tr) =
      (fun p => let r := if signing then p.1 • X else p.1 • g
        (r, (g, X), p.2, record signing m r tr)) <$>
          ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F)) (.inr m)).run cache := by
  rw [backendGoodReply, backendReply_denote rep data cost primitive _ _ _ (samplingCode.scalar_denote ())]
  congr 1
  funext p
  rw [goodResponse_denote]

omit [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))] in
theorem backendBadReply_denote (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (signing : Bool) (m : M) (g X : G₁) (kappa : F) (cache : List (M × (F × F)))
    (tr : Model.LazyAGM.Transcript M M G₁) :
    (backendBadReply rep data cost primitive samplingCode signing).denote (m, (kappa, g, X), cache, tr) =
      (fun p => let point := p.1.1 • X + p.1.2 • g
        let r := if signing then kappa • point else point
        (r, (kappa, g, X), p.2, record signing m r tr)) <$>
          ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F)) (.inr m)).run cache := by
  rw [backendBadReply, backendReply_denote rep data cost primitive _ _ _ (pairSampler_denote rep data samplingCode ())]
  congr 1
  funext p
  rw [badResponse_denote]

end Signatures.Runtime.LazyAGM

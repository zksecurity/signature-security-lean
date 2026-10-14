import Signatures.Runtime.WeightedReply
import Signatures.Runtime.BackendWeightedEvaluate

/-! Actual weighted hash/sign reply programs. Signing constructs the source term
list and a fallback term, then runs the existing private-cache evaluator. Hashing
uses one private read. Both update exactly one reverse reply log after computing
the delivered group element, while preserving challenge configuration. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM

@[reducible] def Index.messageTy : Index → Ty CryptoAtom
  | .oops _ => Weights.oopsMessage
  | .proximity ell => Weights.proximityTupleMessage ell

def Index.terms : (index : Index) → Expr CryptoOp [index.messageTy] (.list (Terms.termTy index.ty))
  | .oops d => Terms.oops d
  | .proximity ell => Terms.proximity ell

def Index.defaultTerm : (index : Index) → Expr CryptoOp [index.messageTy] (Terms.termTy index.ty)
  | .oops d => Reply.oopsDefault d
  | .proximity ell => Reply.proximityDefault ell

namespace Reply

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

variable {indexTy messageTy value config : Ty CryptoAtom}

def messageFrame : Q.Realizer (rep.ty messageTy) (rep.env [messageTy]) (fun m => (m, ())) :=
  QP.pair (Q.identity _) (data.unit _)

def signValue (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy))
    (evaluate : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list (Terms.termTy indexTy), Terms.termTy indexTy])
        (rep.ty (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value))) :
    Code Q unifSpec iface (rep.ty (.pair messageTy (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value)) :=
  .seq (.first (rep.ty (cacheTy indexTy value)) (.atomic (messageFrame rep data)))
    (.seq (.first (rep.ty (cacheTy indexTy value))
      (.atomic (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive (signArgs terms default))))
      evaluate)

theorem signValue_denote
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy))
    (evaluate : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list (Terms.termTy indexTy), Terms.termTy indexTy])
        (rep.ty (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value)))
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))) :
    (signValue rep data cost primitive terms default evaluate).denote (m, cache) =
      evaluate.denote ((terms.denote (arithmetic F G₁ G₂ K M cost) (m, ()),
        default.denote (arithmetic F G₁ G₂ K M cost) (m, ()), ()), cache) := by
  simp only [signValue, Code.denote, map_pure, pure_bind]
  rfl

def replyFrame (signing : Bool) :
    Q.Realizer (rep.ty (.pair (requestTy indexTy messageTy signing) (storeTy indexTy messageTy value config)))
      (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config])
      (fun p => (p.1, p.2, ())) :=
  QP.pair (QP.fst _ _) (QP.pair (QP.snd _ _) (data.unit _))

@[irreducible] def backendReply (signing : Bool)
    (valueCode : Code Q unifSpec iface
      (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value)))
    (response : Expr CryptoOp [value, config] point₁) :
    Code Q unifSpec iface (rep.ty (.pair (requestTy indexTy messageTy signing) (storeTy indexTy messageTy value config)))
      (rep.ty (.pair point₁ (storeTy indexTy messageTy value config))) :=
  .seq (.atomic (replyFrame rep data signing))
    (.seq (.atomic (QP.pair
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (cacheArgs signing))
      (Q.identity (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]))))
      (.seq (.first (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]) valueCode)
        (.atomic (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (replyResult signing response)))))

theorem backendReply_denote (signing : Bool)
    (valueCode : Code Q unifSpec iface
      (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value)))
    (response : Expr CryptoOp [value, config] point₁)
    (request : (requestTy indexTy messageTy signing).Value (cryptoBase F G₁ G₂ K M))
    (cfg : config.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) :
    (backendReply rep data cost primitive signing valueCode response).denote (request, cfg, cache, tr) =
      (fun p => let reply := response.denote (arithmetic F G₁ G₂ K M cost) (p.1, cfg, ())
        (reply, cfg, p.2, record (requestTag signing request) reply tr)) <$>
          valueCode.denote (request, cache) := by
  rw [backendReply]
  simp only [Code.denote, pure_bind, cacheArgs, Expr.denote, LazyAGM.ReplySyntax.v0,
    LazyAGM.ReplySyntax.v1, Var.get, bind_pure_comp, Functor.map_map]
  congr 1
  funext p
  exact replyResult_denote cost signing response request cfg cache p.2 tr p.1

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

def goodSignValue : Code Q unifSpec iface (rep.ty (.pair index.messageTy (cacheTy index.ty scalar)))
    (rep.ty (cacheResultTy index.ty scalar)) :=
  signValue rep data cost primitive index.terms index.defaultTerm
    (Evaluate.backendGood rep data cost primitive sampling index)

def badSignValue : Code Q unifSpec iface (rep.ty (.pair index.messageTy (cacheTy index.ty (.pair scalar scalar))))
    (rep.ty (cacheResultTy index.ty (.pair scalar scalar))) :=
  signValue rep data cost primitive index.terms index.defaultTerm
    (Evaluate.backendBad rep data cost primitive sampling index)

theorem goodSignValue_source (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (goodSignValue rep data cost primitive sampling index).denote (m, cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
        (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F))
        (Model.LazyAGM.evalTerms (index.terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())))).run cache := by
  rw [goodSignValue, signValue_denote, Evaluate.backendGood_source]

theorem badSignValue_source (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) :
    (badSignValue rep data cost primitive sampling index).denote (m, cache) =
      (simulateQ (BLS.LazyAGM.Reduction.privateListOracle
        (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F))
        (Model.LazyAGM.evalTerms (index.terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())))).run cache := by
  rw [badSignValue, signValue_denote, Evaluate.backendBad_source]

def goodHash : Code Q unifSpec iface
    (rep.ty (.pair index.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)))
    (rep.ty (.pair point₁ (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))) :=
  backendReply rep data cost primitive false (Read.goodRead rep data cost primitive sampling index)
    (LazyAGM.goodResponse false)

def goodSign : Code Q unifSpec iface
    (rep.ty (.pair index.messageTy (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)))
    (rep.ty (.pair point₁ (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))) :=
  backendReply rep data cost primitive true (goodSignValue rep data cost primitive sampling index)
    (LazyAGM.goodResponse true)

def badHash : Code Q unifSpec iface
    (rep.ty (.pair index.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)))
    (rep.ty (.pair point₁ (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))) :=
  backendReply rep data cost primitive false (Read.badRead rep data cost primitive sampling index)
    (LazyAGM.badResponse false)

def badSign : Code Q unifSpec iface
    (rep.ty (.pair index.messageTy (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)))
    (rep.ty (.pair point₁ (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))) :=
  backendReply rep data cost primitive true (badSignValue rep data cost primitive sampling index)
    (LazyAGM.badResponse true)

end Reply
end Signatures.Runtime.WeightedAGM

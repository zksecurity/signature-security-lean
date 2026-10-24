import Proofs.Runtime.LazyAGMReply
import Proofs.Runtime.WeightedTerms

/-! Local syntax for weighted replies. Hash indices and signing messages have
independent types. The store retains a fixed challenge, a finite private cache,
and separate reverse-order reply logs. Private reads never create reply tokens. -/

namespace Signatures.Runtime.WeightedAGM.Reply

abbrev transcriptTy (indexTy messageTy : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair (.list (.pair indexTy point₁)) (.list (.pair messageTy point₁))

abbrev cacheTy (indexTy value : Ty CryptoAtom) : Ty CryptoAtom := .list (.pair indexTy value)
abbrev cacheResultTy (indexTy value : Ty CryptoAtom) : Ty CryptoAtom := .pair value (cacheTy indexTy value)
abbrev storeTy (indexTy messageTy value config : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair config (.pair (cacheTy indexTy value) (transcriptTy indexTy messageTy))

abbrev requestTy (indexTy messageTy : Ty CryptoAtom) : Bool → Ty CryptoAtom
  | false => indexTy
  | true => messageTy

def record {ι M G : Type} (request : ι ⊕ M) (reply : G)
    (tr : Model.LazyAGM.Transcript ι M G) : Model.LazyAGM.Transcript ι M G :=
  match request with
  | .inl i => ((i, reply) :: tr.1, tr.2)
  | .inr m => (tr.1, (m, reply) :: tr.2)

/-- Proof-only chronological view. Executable extraction pays for its reversals. -/
def chronological {ι M G : Type} (tr : Model.LazyAGM.Transcript ι M G) :
    Model.LazyAGM.Transcript ι M G := (tr.1.reverse, tr.2.reverse)

theorem chronological_record {ι M G : Type} (request : ι ⊕ M) (reply : G)
    (tr : Model.LazyAGM.Transcript ι M G) :
    chronological (record request reply tr) =
      match request with
      | .inl i => ((chronological tr).1 ++ [(i, reply)], (chronological tr).2)
      | .inr m => ((chronological tr).1, (chronological tr).2 ++ [(m, reply)]) := by
  cases request <;> simp [chronological, record]

open LazyAGM.ReplySyntax

variable {indexTy messageTy value config : Ty CryptoAtom}

def cacheArgs (signing : Bool) :
    Expr CryptoOp [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]
      (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)) :=
  .pair v0 (.fst (.snd v1))

def replyResult (signing : Bool) (response : Expr CryptoOp [value, config] point₁) :
    Expr CryptoOp [cacheResultTy indexTy value, requestTy indexTy messageTy signing,
      storeTy indexTy messageTy value config] (.pair point₁ (storeTy indexTy messageTy value config)) :=
  .letE (.fst v2) (.letE (.fst v1)
    (.letE (response.weakenTail [cacheResultTy indexTy value, requestTy indexTy messageTy signing,
        storeTy indexTy messageTy value config])
      (.pair v0 (.pair v2 (.pair (.snd v3)
        (match signing with
        | true => .pair (.fst (.snd (.snd v5))) (.cons (.pair v4 v0) (.snd (.snd (.snd v5))))
        | false => .pair (.cons (.pair v4 v0) (.fst (.snd (.snd v5)))) (.snd (.snd (.snd v5)))))))))

/-- Arguments to the existing evaluator, including an executed fallback term. -/
def signArgs (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy)) :
    Args CryptoOp [messageTy] [.list (Terms.termTy indexTy), Terms.termTy indexTy] :=
  .cons terms (.cons default .nil)

def oopsDefault (d : Nat) : Expr CryptoOp [Weights.oopsMessage] (Terms.termTy (Weights.oopsKey d)) :=
  .pair (.pair (.snd v0) (.op (.finZero d) .unit)) (.op .zero .unit)

def proximityDefault (ell : Nat) :
    Expr CryptoOp [Weights.proximityTupleMessage ell] (Terms.termTy (Weights.proximityKey ell)) :=
  .pair (.pair (.op (.finZero ell) .unit) (.snd v0)) (.op .zero .unit)

open BackendProgram in
theorem cacheArgs_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) (signing : Bool) :
    Expression.descriptionBound allowance primitiveSize
      (cacheArgs (indexTy := indexTy) (messageTy := messageTy) (value := value) (config := config) signing) =
      9 * allowance := by
  simp only [cacheArgs, v0, v1, Expression.descriptionBound, Expression.variableDescription]
  omega

open BackendProgram in
theorem replyResult_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (signing : Bool) (response : Expr CryptoOp [value, config] point₁) :
    Expression.descriptionBound allowance primitiveSize
      (replyResult (indexTy := indexTy) (messageTy := messageTy) signing response) =
      Expression.descriptionBound allowance primitiveSize response + 88 * allowance := by
  cases signing <;>
    simp only [replyResult, v0, v1, v2, v3, v4, v5, Expression.descriptionBound,
      Expression.variableDescription, Expression.descriptionBound_weakenTail] <;> omega

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

def requestTag (signing : Bool) : (requestTy indexTy messageTy signing).Value (cryptoBase F G₁ G₂ K M) →
    indexTy.Value (cryptoBase F G₁ G₂ K M) ⊕ messageTy.Value (cryptoBase F G₁ G₂ K M) :=
  match signing with | false => Sum.inl | true => Sum.inr

theorem replyResult_denote (cost : PrimitiveCosts) (signing : Bool)
    (response : Expr CryptoOp [value, config] point₁)
    (request : (requestTy indexTy messageTy signing).Value (cryptoBase F G₁ G₂ K M))
    (cfg : config.Value (cryptoBase F G₁ G₂ K M))
    (cache nextCache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (r : value.Value (cryptoBase F G₁ G₂ K M)) :
    (replyResult signing response).denote (arithmetic F G₁ G₂ K M cost)
      ((r, nextCache), request, (cfg, cache, tr), ()) =
      let reply := response.denote (arithmetic F G₁ G₂ K M cost) (r, cfg, ())
      (reply, cfg, nextCache, record (requestTag signing request) reply tr) := by
  have hr := response.weakenTail_denote
    (Δ := [cacheResultTy indexTy value, requestTy indexTy messageTy signing,
      storeTy indexTy messageTy value config])
    (arithmetic F G₁ G₂ K M cost) (r, cfg, ())
    ((r, nextCache), request, (cfg, cache, tr), ())
  simp only [Env.append] at hr
  cases signing <;>
    simp [replyResult, Expr.denote, v0, v1, v2, v3, v4, v5, Var.get, hr, requestTag, record]

end Signatures.Runtime.WeightedAGM.Reply

import Proofs.Runtime.Arithmetic
import Proofs.Runtime.Weakening
import Proofs.Runtime.BackendWeakeningSize
import Signatures.Model.LazyAGM

/-! First-order local syntax for lazy BLS AGM replies. The persistent store
contains the public challenge configuration, a private finite cache, and two
reverse-order explicit-reply logs. The caller never receives that store.
Only a delivered reply is recorded; cache access itself creates no token.
-/

namespace Signatures.Runtime.LazyAGM

abbrev transcriptTy : Ty CryptoAtom :=
  .pair (.list (.pair message point₁)) (.list (.pair message point₁))

abbrev cacheTy (value : Ty CryptoAtom) : Ty CryptoAtom := .list (.pair message value)
abbrev cacheResultTy (value : Ty CryptoAtom) : Ty CryptoAtom := .pair value (cacheTy value)
abbrev storeTy (value config : Ty CryptoAtom) : Ty CryptoAtom :=
  .pair config (.pair (cacheTy value) transcriptTy)

abbrev goodConfigTy : Ty CryptoAtom := .pair point₁ point₁
abbrev badConfigTy : Ty CryptoAtom := .pair scalar (.pair point₁ point₁)

def record {M G : Type} (signing : Bool) (m : M) (r : G)
    (tr : Model.LazyAGM.Transcript M M G) : Model.LazyAGM.Transcript M M G :=
  if signing then (tr.1, (m, r) :: tr.2) else ((m, r) :: tr.1, tr.2)

/-- Proof-only view. Executable reversal, when needed for coefficient matching,
must be implemented and charged in the extractor. -/
def chronological {M G : Type} (tr : Model.LazyAGM.Transcript M M G) :
    Model.LazyAGM.Transcript M M G := (tr.1.reverse, tr.2.reverse)

theorem chronological_record {M G : Type} (signing : Bool) (m : M) (r : G)
    (tr : Model.LazyAGM.Transcript M M G) :
    chronological (record signing m r tr) =
      if signing then ((chronological tr).1, (chronological tr).2 ++ [(m, r)])
      else ((chronological tr).1 ++ [(m, r)], (chronological tr).2) := by
  cases signing <;> simp [chronological, record]

namespace ReplySyntax

def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d := .var (.there (.there (.there .here)))
def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))

end ReplySyntax

open ReplySyntax

variable {value config : Ty CryptoAtom}

def cacheArgs (fallback : Expr CryptoOp [message, storeTy value config] value) :
    Args CryptoOp [message, storeTy value config] [message, value, cacheTy value] :=
  .cons v0 (.cons fallback (.cons (.fst (.snd v1)) .nil))

def replyResult (signing : Bool) (response : Expr CryptoOp [value, config] point₁) :
    Expr CryptoOp [cacheResultTy value, message, storeTy value config]
      (.pair point₁ (storeTy value config)) :=
  .letE (.fst v2) (.letE (.fst v1)
    (.letE (response.weakenTail [cacheResultTy value, message, storeTy value config])
      (.pair v0 (.pair v2 (.pair (.snd v3)
        (match signing with
        | true => .pair (.fst (.snd (.snd v5))) (.cons (.pair v4 v0) (.snd (.snd (.snd v5))))
        | false => .pair (.cons (.pair v4 v0) (.fst (.snd (.snd v5)))) (.snd (.snd (.snd v5)))))))))

def goodResponse (signing : Bool) : Expr CryptoOp [scalar, goodConfigTy] point₁ :=
  match signing with
  | true => .op .scale₁ (.pair v0 (.snd v1))
  | false => .op .scale₁ (.pair v0 (.fst v1))

def badResponse (signing : Bool) : Expr CryptoOp [.pair scalar scalar, badConfigTy] point₁ :=
  .letE (.op .add₁
    (.pair (.op .scale₁ (.pair (.fst v0) (.snd (.snd v1))))
      (.op .scale₁ (.pair (.snd v0) (.fst (.snd v1))))))
    (match signing with
    | true => .op .scale₁ (.pair (.fst v2) v0)
    | false => v0)

open BackendProgram in
theorem cacheArgs_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (fallback : Expr CryptoOp [message, storeTy value config] value) :
    Expression.argumentsDescription allowance primitiveSize (cacheArgs fallback) =
      Expression.descriptionBound allowance primitiveSize fallback + 12 * allowance := by
  simp only [cacheArgs, v0, v1, Expression.argumentsDescription,
    Expression.descriptionBound, Expression.variableDescription]
  omega

open BackendProgram in
theorem replyResult_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (signing : Bool) (response : Expr CryptoOp [value, config] point₁) :
    Expression.descriptionBound allowance primitiveSize (replyResult signing response) =
      Expression.descriptionBound allowance primitiveSize response + 88 * allowance := by
  cases signing <;>
    simp only [replyResult,
      v0, v1, v2, v3, v4, v5, Expression.descriptionBound, Expression.variableDescription,
      Expression.descriptionBound_weakenTail] <;> omega

open BackendProgram in
theorem goodResponse_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) (signing : Bool) :
    Expression.descriptionBound allowance primitiveSize (goodResponse signing) =
      primitiveSize CryptoOp.scale₁ + 8 * allowance := by
  cases signing <;>
    simp only [goodResponse,
      v0, v1, Expression.descriptionBound, Expression.variableDescription] <;> omega

open BackendProgram in
theorem badResponse_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) (signing : Bool) :
    Expression.descriptionBound allowance primitiveSize (badResponse signing) =
      (if signing then 3 else 2) * primitiveSize CryptoOp.scale₁ + primitiveSize CryptoOp.add₁ +
        (if signing then 39 else 30) * allowance := by
  cases signing <;>
    simp only [badResponse, Bool.false_eq_true, ite_false, ite_true,
      v0, v1, v2, Expression.descriptionBound, Expression.variableDescription] <;> omega

variable {F G₁ G₂ M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq M]

theorem cacheArgs_denote (cost : PrimitiveCosts)
    (fallback : Expr CryptoOp [message, storeTy value config] value)
    (m : M) (cfg : config.Value (cryptoBase F G₁ G₂ M M))
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (tr : Model.LazyAGM.Transcript M M G₁) :
    (cacheArgs fallback).denote (arithmetic F G₁ G₂ M M cost) (m, (cfg, cache, tr), ()) =
      (m, fallback.denote (arithmetic F G₁ G₂ M M cost) (m, (cfg, cache, tr), ()), cache, ()) := rfl

theorem replyResult_denote (cost : PrimitiveCosts) (signing : Bool)
    (response : Expr CryptoOp [value, config] point₁)
    (m : M) (cfg : config.Value (cryptoBase F G₁ G₂ M M))
    (cache nextCache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (tr : Model.LazyAGM.Transcript M M G₁) (r : value.Value (cryptoBase F G₁ G₂ M M)) :
    (replyResult signing response).denote (arithmetic F G₁ G₂ M M cost)
      ((r, nextCache), m, (cfg, cache, tr), ()) =
      let reply := response.denote (arithmetic F G₁ G₂ M M cost) (r, cfg, ())
      (reply, cfg, nextCache, record signing m reply tr) := by
  have hr := response.weakenTail_denote (Δ := [cacheResultTy value, message, storeTy value config])
    (arithmetic F G₁ G₂ M M cost) (r, cfg, ())
    ((r, nextCache), m, (cfg, cache, tr), ())
  simp only [Env.append] at hr
  cases signing <;>
    simp [replyResult, Expr.denote, v0, v1, v2, v3, v4, v5, Var.get, hr, record]

theorem goodResponse_denote (cost : PrimitiveCosts) (signing : Bool) (rho : F) (g X : G₁) :
    (goodResponse signing).denote (arithmetic F G₁ G₂ M M cost) (rho, (g, X), ()) =
      if signing then rho • X else rho • g := by
  cases signing <;> rfl

theorem badResponse_denote (cost : PrimitiveCosts) (signing : Bool) (masks : F × F)
    (g X : G₁) (kappa : F) :
    (badResponse signing).denote (arithmetic F G₁ G₂ M M cost) (masks, (kappa, g, X), ()) =
      if signing then kappa • (masks.1 • X + masks.2 • g) else masks.1 • X + masks.2 • g := by
  cases signing <;> rfl

end Signatures.Runtime.LazyAGM

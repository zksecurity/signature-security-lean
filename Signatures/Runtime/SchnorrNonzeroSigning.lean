import Signatures.Runtime.SchnorrCache
import Signatures.Schnorr.Spec.NonzeroNonce

/-! The nonzero signing simulator in the reduction's arithmetic syntax.
Two field draws and one nonzero draw are separate effects. The finite repair
branch changes commitment and response together before programming the cache.
This syntax describes only the reduction, not the attacker's local code. -/

open OracleComp

namespace Signatures.Runtime.Schnorr.NonzeroSigning

abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d := .var (.there (.there (.there .here)))
abbrev v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
abbrev v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))
abbrev v8 {a b c d e f g h i Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: h :: i :: Γ) i :=
  .var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))

abbrev Input := [message, point₁, point₁, hashCache]
abbrev Sampled := scalar :: scalar :: scalar :: Input
abbrev Committed := point₁ :: Sampled
abbrev Repaired := .pair point₁ scalar :: Committed

/-- Input is the ordinary commitment, response, replacement nonce and generator. -/
def repair : Expr CryptoOp [point₁, scalar, scalar, point₁] (.pair point₁ scalar) :=
  .branch (.op .point₁Eq (.pair v0 (.op .zero₁ .unit)))
    (.pair (.op .scale₁ (.pair v2 v3)) (.op .add (.pair v1 v2)))
    (.pair v0 v1)

def commitArgs : Args CryptoOp Sampled [scalar, scalar, point₁, point₁] :=
  .cons v1 (.cons v2 (.cons v4 (.cons v5 .nil)))

def repairArgs : Args CryptoOp Committed [point₁, scalar, scalar, point₁] :=
  .cons v0 (.cons v2 (.cons v1 (.cons v5 .nil)))

def programArgs : Args CryptoOp Repaired [hashKey, scalar, hashCache] :=
  .cons (.pair v5 (.fst v0)) (.cons v4 (.cons v8 .nil))

variable {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

def body (fieldDraw nonzeroDraw : Cmd .unit scalar) :
    Program CryptoOp Cmd Input (.pair (.pair point₁ scalar) hashCache) :=
  .bind (.query fieldDraw .unit) (.bind (.query fieldDraw .unit)
    (.bind (.query nonzeroDraw .unit)
      (.bind (.call (.ret simulatedCommit) commitArgs)
        (.bind (.call (.ret repair) repairArgs)
          (.bind (.call (.ret (cacheProgram hashEq)) programArgs)
            (.ret (.pair v1 v0)))))))

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem repair_denote (cost : PrimitiveCosts) (R : G₁) (z a : F) (g : G₁) :
    repair.denote (arithmetic F G₁ G₂ K M cost) (R, z, a, g, ()) =
      if R = 0 then (a • g, z + a) else (R, z) := by
  by_cases h : R = 0 <;> simp [repair, Expr.denote, Var.get, arithmetic, h]

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Sequential draw order and the cache update are exact, including collisions. -/
theorem body_denote (cost : PrimitiveCosts)
    (H : SemanticsM (cryptoBase F G₁ G₂ K M) Cmd m) (fieldDraw nonzeroDraw : Cmd .unit scalar)
    (msg : M) (g pk : G₁) (cache : List ((M × G₁) × F)) :
    (body fieldDraw nonzeroDraw).denote (arithmetic F G₁ G₂ K M cost) H (msg, g, pk, cache, ()) = (do
      let c ← H fieldDraw ()
      let z ← H fieldDraw ()
      let a ← H nonzeroDraw ()
      let R := z • g - c • pk
      let repaired := if R = 0 then (a • g, z + a) else (R, z)
      pure (repaired, (cacheProgram hashEq).denote (arithmetic F G₁ G₂ K M cost)
        ((msg, repaired.1), c, cache, ()))) := by
  simp only [body, Program.denote, commitArgs, repairArgs, programArgs, Args.denote,
    Expr.denote, Var.get, pure_bind, simulatedCommit, arithmetic]
  congr 1
  funext c
  congr 1
  funext z
  congr 1
  funext a
  by_cases h : z • g - c • pk = 0 <;>
    simp only [repair, Expr.denote, Var.get, h, decide_true, decide_false,
      Bool.false_eq_true, ite_true, ite_false]

end Signatures.Runtime.Schnorr.NonzeroSigning

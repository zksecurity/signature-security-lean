import Signatures.Runtime.Arithmetic

/-! Executable first-order arithmetic for Coron's hash/sign replies and co-CDH extraction.
These are the exact algebraic expressions in `BLS.CoCDH.coronOracleLazy` and
`coronReductionProgram`, with all variable access, branches, constructors, and primitive
instructions charged by the runtime interpreter. Cache lookup and scalar/coin draws are
separate implemented components, not free operations inside these expressions. -/

namespace Signatures.Runtime.Coron

def hashReply : Expr CryptoOp [scalar, point₁, point₁, .nat] point₁ :=
  .op .add₁ (.pair
    (.op .scale₁ (.pair (.var .here) (.var (.there .here))))
    (.branch (.op .natEq (.pair (.var (.there (.there (.there .here)))) (.nat 0)))
      (.var (.there (.there .here))) (.op .zero₁ .unit)))

def signReply : Expr CryptoOp [scalar, point₁, .nat] point₁ :=
  .branch (.op .natEq (.pair (.var (.there (.there .here))) (.nat 0)))
    (.op .zero₁ .unit) (.op .scale₁ (.pair (.var .here) (.var (.there .here))))

def extract : Expr CryptoOp [point₁, scalar, point₁] point₁ :=
  .op .sub₁ (.pair (.var .here)
    (.op .scale₁ (.pair (.var (.there .here)) (.var (.there (.there .here))))))

variable {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

theorem hashReply_value (cost : PrimitiveCosts) (rho : F) (g h : G₁) (coin : Nat) :
    (hashReply.run (arithmetic F G₁ G₂ M M cost) (rho, g, h, coin, ())).value =
      rho • g + if coin = 0 then h else 0 := by
  by_cases hc : coin = 0 <;>
    simp [hashReply, Expr.run, Var.get, arithmetic, hc]

theorem signReply_value (cost : PrimitiveCosts) (rho : F) (X : G₁) (coin : Nat) :
    (signReply.run (arithmetic F G₁ G₂ M M cost) (rho, X, coin, ())).value =
      if coin = 0 then 0 else rho • X := by
  by_cases hc : coin = 0 <;>
    simp [signReply, Expr.run, Var.get, arithmetic, hc]

theorem extract_value (cost : PrimitiveCosts) (sigma : G₁) (rho : F) (X : G₁) :
    (extract.run (arithmetic F G₁ G₂ M M cost) (sigma, rho, X, ())).value = sigma - rho • X := rfl

theorem hashReply_steps (cost : PrimitiveCosts) (rho : F) (g h : G₁) (coin : Nat) :
    (hashReply.run (arithmetic F G₁ G₂ M M cost) (rho, g, h, coin, ())).steps ≤
      cost.scalar₁ + cost.natOp + 2 * cost.group + 18 := by
  by_cases hc : coin = 0 <;>
    simp [hashReply, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, hc] <;> omega

theorem signReply_steps (cost : PrimitiveCosts) (rho : F) (X : G₁) (coin : Nat) :
    (signReply.run (arithmetic F G₁ G₂ M M cost) (rho, X, coin, ())).steps ≤
      cost.natOp + cost.group + cost.scalar₁ + 12 := by
  by_cases hc : coin = 0 <;>
    simp [signReply, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price, hc] <;> omega

theorem extract_steps (cost : PrimitiveCosts) (sigma : G₁) (rho : F) (X : G₁) :
    (extract.run (arithmetic F G₁ G₂ M M cost) (sigma, rho, X, ())).steps =
      cost.scalar₁ + cost.group + 10 := by
  simp [extract, Expr.run, Var.get, Var.depth, arithmetic, CryptoOp.price]
  omega

end Signatures.Runtime.Coron

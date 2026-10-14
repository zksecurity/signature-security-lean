import Signatures.Runtime.BackendCoronStateInvariant

/-! The actual final-extraction argument code, with costs derived from its
compiled instructions. The named decomposition is definitionally the existing
machine routine, including the final lazy hash and scalar-cache scan. -/

open PFunctor

namespace Signatures.Runtime.Coron.FinishCompiler

open BackendProgram

abbrev Forgery := Ty.pair message point₁
abbrev StartEnv := [Forgery]
abbrev HashEnv := point₁ :: StartEnv
abbrev ReadEnv (qS : Nat) := machineStore qS :: HashEnv
abbrev LookupResult := Ty.pair .bool scalar
abbrev LookupEnv (qS : Nat) := LookupResult :: ReadEnv qS

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d := .var (.there (.there (.there .here)))

def hashArgs : Args CryptoOp StartEnv [message] := .cons (.fst v0) .nil

def lookupArgs (qS : Nat) : Args CryptoOp (ReadEnv qS) [message, scalar, .list (.pair message scalar)] :=
  .cons (.fst v2) (.cons (.op .zero .unit) (.cons (.fst (.snd v0)) .nil))

def extractArgs (qS : Nat) : Args CryptoOp (LookupEnv qS) [point₁, scalar, point₁] :=
  .cons (.snd v3) (.cons (.snd v0) (.cons (.fst (.snd (.fst v1))) .nil))

def body (qS : Nat) : Program CryptoOp (Machine.Effect (machineStore qS)) StartEnv point₁ :=
  .bind (.call (machineReply qS false) hashArgs)
    (.bind (.query .read .unit)
      (.bind (.call (.ret (lookup (val := scalar) CryptoOp.messageEq)) (lookupArgs qS))
        (.call (.ret extract) (extractArgs qS))))

theorem machineFinish_eq (qS : Nat) : machineFinish qS = body qS := rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

theorem hashArgs_denote (env : Env (cryptoBase F G₁ G₂ M M) StartEnv) :
    hashArgs.denote (arithmetic F G₁ G₂ M M cost) env = (env.1.1, ()) := rfl

theorem lookupArgs_denote (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS)) :
    (lookupArgs qS).denote (arithmetic F G₁ G₂ M M cost) env = (env.2.2.1.1, 0, env.1.2.1, ()) := rfl

theorem extractArgs_denote (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (LookupEnv qS)) :
    (extractArgs qS).denote (arithmetic F G₁ G₂ M M cost) env =
      (env.2.2.2.1.2, env.1.2, env.2.1.1.2.1, ()) := rfl

include localLaws dataLaws primitiveBound sizes mono

theorem hashArgs_cost (env : Env (cryptoBase F G₁ G₂ M M) StartEnv)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env StartEnv) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive hashArgs) env ≤
      16 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
    dataLaws primitiveBound hashArgs env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [hashArgs, v0, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env, StartEnv, Forgery,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

theorem lookupArgs_cost (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS))
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env (ReadEnv qS)) env ≤ width)
    (ht : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (lookupArgs qS)) env ≤
      zeroTime + 32 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
    dataLaws primitiveBound (lookupArgs qS) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [lookupArgs, v0, v2, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env, ReadEnv, HashEnv, StartEnv, Forgery,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

theorem extractArgs_cost (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (LookupEnv qS))
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env (LookupEnv qS)) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (extractArgs qS)) env ≤
      64 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
    dataLaws primitiveBound (extractArgs qS) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [extractArgs, v0, v1, v3, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    LookupEnv, LookupResult, ReadEnv, HashEnv, StartEnv, Forgery, Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

end Signatures.Runtime.Coron.FinishCompiler

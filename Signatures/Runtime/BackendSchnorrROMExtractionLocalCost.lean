import Signatures.Runtime.BackendSchnorrROMExtraction

/-! Local costs of the actual extraction guard and field arithmetic. The
retained environment is charged in every compiled projection and branch. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeExtraction

open BackendProgram

abbrev bodyTypes (Γ : List (Ty CryptoAtom)) : List (Ty CryptoAtom) :=
  cachePassOutput :: resultTy :: cachePassOutput :: Γ

def guardBody {Γ} : Expr CryptoOp (bodyTypes Γ) .bool :=
  guardExpression (.var (.there (.there .here))) (.var .here)

def candidateBody {Γ} : Expr CryptoOp (bodyTypes Γ) scalar :=
  candidateExpression (.var (.there (.there .here))) (.var .here)

def body {Γ} : Expr CryptoOp (bodyTypes Γ) resultTy :=
  oneExpression (.var (.there (.there .here))) (.var .here)

def oneWith {Γ} (guard : Expr CryptoOp Γ .bool) (candidate : Expr CryptoOp Γ scalar) :
    Expr CryptoOp Γ resultTy :=
  .branch guard (.pair (.bool true) candidate) (.pair (.bool false) (.op .zero .unit))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes mono

theorem guardBody_time {Γ}
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (acc : Bool × F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width pointTime scalarTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env (bodyTypes Γ)) (second, acc, first, env) ≤ width)
    (hp : (primitiveBound .point₁Eq).time (first.1.1.2.1, second.1.1.2.1) ≤ pointTime)
    (hc : (primitiveBound .scalarEq).time (first.1.2, second.1.2) ≤ scalarTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (guardBody (Γ := Γ))).time (second, acc, first, env) ≤
      pointTime + scalarTime + 512 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases hr : first.1.1.2.1 = second.1.1.2.1 <;> by_cases he : first.1.2 = second.1.2 <;>
    dsimp only [guardBody, guardExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.selectBound, DataCostLaws.boolBound,
      DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic, Sum.elim,
      LanguageRepresentation.ty, LanguageRepresentation.env, bodyTypes, id, Function.comp_def] at * <;>
    simp only [hr, he, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at * <;>
    grind only

theorem candidateBody_time {Γ}
    (first second : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (acc : Bool × F)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width subTime divTime : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env (bodyTypes Γ)) (second, acc, first, env) ≤ width)
    (hz : Q.size (rep.ty scalar) (first.1.1.2.2 - second.1.1.2.2) ≤ width)
    (hc : Q.size (rep.ty scalar) (first.1.2 - second.1.2) ≤ width)
    (ho : Q.size (rep.ty scalar) ((first.1.1.2.2 - second.1.1.2.2) / (first.1.2 - second.1.2)) ≤ width)
    (htz : (primitiveBound .sub).time (first.1.1.2.2, second.1.1.2.2) ≤ subTime)
    (htc : (primitiveBound .sub).time (first.1.2, second.1.2) ≤ subTime)
    (htd : (primitiveBound .div).time (first.1.1.2.2 - second.1.1.2.2, first.1.2 - second.1.2) ≤ divTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (candidateBody (Γ := Γ))).time (second, acc, first, env) ≤
      2 * subTime + divTime + 256 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [candidateBody, candidateExpression, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env,
    bodyTypes, id, Function.comp_def] at *
  grind only

theorem oneWith_time {Γ} (guard : Expr CryptoOp Γ .bool) (candidate : Expr CryptoOp Γ scalar)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width guardTime candidateTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env Γ) env ≤ width)
    (ho : Q.size (rep.ty scalar) (candidate.denote (arithmetic F G₁ G₂ K M cost) env) ≤ width)
    (hg : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound guard).time env ≤ guardTime)
    (hc : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound candidate).time env ≤ candidateTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (oneWith guard candidate)).time env ≤ guardTime + candidateTime + zeroTime + 256 * overhead (512 * width) := by
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 512 * width, overhead n ≤ overhead (512 * width) := fun _ hn => mono hn
  by_cases hg' : guard.denote (arithmetic F G₁ G₂ K M cost) env = true <;>
    dsimp only [oneWith, Expression.compileBound, LocalBound.compose, LocalBound.pair,
      LocalBound.identity, LocalBound.castFunction, LocalBound.elim, DataCostLaws.selectBound,
      DataCostLaws.boolBound, DataCostLaws.unitBound, Expr.denote, arithmetic,
      LanguageRepresentation.ty, id, Function.comp_def, Sum.elim] at * <;>
    simp only [hg', ↓reduceIte] at * <;> grind only

end Signatures.Runtime.Schnorr.ListROM.NativeExtraction

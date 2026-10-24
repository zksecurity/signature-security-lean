import Proofs.Runtime.BackendSchnorrROMLiveIndexBudget

/-! Structural costs around native replay selection. Component lemmas charge
the actual compiled verifier, guard, lookup preparation and branch composition. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)

def indexExpressionWith {Γ}
    (search : Expr CryptoOp ([hashKey, hashCache, cachePassOutput] ++ Γ) indexResult) :
    Expr CryptoOp (cachePassOutput :: Γ) indexResult :=
  .letE (.snd (.snd (.snd v0)))
    (.letE (.pair (.fst (.fst (.fst v1))) (.fst (.snd (.fst (.fst v1))))) search)

def oneExpressionWith {Γ}
    (verify : Expr CryptoOp (cachePassOutput :: Γ) .bool)
    (index : Expr CryptoOp (cachePassOutput :: Γ) indexResult)
    (guard : Expr CryptoOp (indexResult :: cachePassOutput :: Γ) indexResult) :
    Expr CryptoOp (cachePassOutput :: Γ) indexResult :=
  .branch verify (.letE index guard) (.pair (.bool false) (.nat 0))

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

theorem verifyExpression_time {Γ : List (Ty CryptoAtom)}
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width scaleTime addTime pointTime : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env (cachePassOutput :: Γ)) (p, env) ≤ width)
    (hs₁ : Q.size (rep.ty point₁) (p.1.1.2.2 • p.2.1.1) ≤ width)
    (hs₂ : Q.size (rep.ty point₁) (p.1.2 • p.2.1.2) ≤ width)
    (ha : Q.size (rep.ty point₁) (p.1.1.2.1 + p.1.2 • p.2.1.2) ≤ width)
    (hc₁ : (primitiveBound .scale₁).time (p.1.1.2.2, p.2.1.1) ≤ scaleTime)
    (hc₂ : (primitiveBound .scale₁).time (p.1.2, p.2.1.2) ≤ scaleTime)
    (hac : (primitiveBound .add₁).time (p.1.1.2.1, p.1.2 • p.2.1.2) ≤ addTime)
    (heq : (primitiveBound .point₁Eq).time (p.1.1.2.2 • p.2.1.1, p.1.1.2.1 + p.1.2 • p.2.1.2) ≤ pointTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (verifyExpression (Γ := Γ))).time (p, env) ≤
      2 * scaleTime + addTime + pointTime + 512 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [verifyExpression, Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.pair, LocalBound.fst, LocalBound.snd, Expr.denote, Var.get, arithmetic,
    LanguageRepresentation.ty, LanguageRepresentation.env, Function.comp_def] at *
  grind only

theorem guardExpression_time {Γ : List (Ty CryptoAtom)} (qH : Nat) (result : Bool × Nat)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (width comparisonTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size rep.data.nat 0 ≤ width)
    (hq : Q.size rep.data.nat (qH + 1) ≤ width)
    (hi : Q.size (rep.env (indexResult :: Γ)) (result, env) ≤ width)
    (hc : (primitiveBound .natLt).time (result.2, qH + 1) ≤ comparisonTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (guardExpression (Γ := Γ) qH)).time (result, env) ≤
      comparisonTime + 128 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  by_cases hf : result.1 = true <;> by_cases hn : result.2 < qH + 1 <;>
    dsimp only [guardExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.elim, LocalBound.castFunction, DataCostLaws.selectBound, DataCostLaws.unitBound,
      DataCostLaws.boolBound, DataCostLaws.natBound, Expr.denote, Var.get, arithmetic,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def, Sum.elim] at * <;>
    simp only [hf, hn, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at * <;>
    grind only

theorem indexExpressionWith_time {Γ : List (Ty CryptoAtom)}
    (search : Expr CryptoOp ([hashKey, hashCache, cachePassOutput] ++ Γ) indexResult)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width searchTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env (cachePassOutput :: Γ)) (p, env) ≤ width)
    (ho : Q.size (rep.ty indexResult) (search.denote (arithmetic F G₁ G₂ K M cost)
      ((p.1.1.1, p.1.1.2.1), p.2.2.2, p, env)) ≤ width)
    (hc : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      search).time ((p.1.1.1, p.1.1.2.1), p.2.2.2, p, env) ≤ searchTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (indexExpressionWith search)).time (p, env) ≤ searchTime + 128 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [indexExpressionWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, id, Function.comp_def] at *
  simp only [List.cons_append, List.nil_append, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  dsimp only [List.append, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

theorem oneExpressionWith_time {Γ : List (Ty CryptoAtom)}
    (verify : Expr CryptoOp (cachePassOutput :: Γ) .bool)
    (index : Expr CryptoOp (cachePassOutput :: Γ) indexResult)
    (guard : Expr CryptoOp (indexResult :: cachePassOutput :: Γ) indexResult)
    (p : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width verifyTime searchTime guardTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hz : Q.size rep.data.nat 0 ≤ width)
    (hi : Q.size (rep.env (cachePassOutput :: Γ)) (p, env) ≤ width)
    (hindex : Q.size (rep.ty indexResult) (index.denote (arithmetic F G₁ G₂ K M cost) (p, env)) ≤ width)
    (hguard : Q.size (rep.ty indexResult) (guard.denote (arithmetic F G₁ G₂ K M cost)
      (index.denote (arithmetic F G₁ G₂ K M cost) (p, env), p, env)) ≤ width)
    (hv : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      verify).time (p, env) ≤ verifyTime)
    (hs : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      index).time (p, env) ≤ searchTime)
    (hg : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      guard).time (index.denote (arithmetic F G₁ G₂ K M cost) (p, env), p, env) ≤ guardTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (oneExpressionWith verify index guard)).time (p, env) ≤
      verifyTime + searchTime + guardTime + 128 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases hf : verify.denote (arithmetic F G₁ G₂ K M cost) (p, env) = true <;>
    dsimp only [oneExpressionWith, Expression.compileBound, LocalBound.compose, LocalBound.pair,
      LocalBound.identity, LocalBound.elim, LocalBound.castFunction, DataCostLaws.selectBound,
      DataCostLaws.unitBound, DataCostLaws.boolBound, DataCostLaws.natBound,
      Expr.denote, Var.get, id, Function.comp_def, Sum.elim,
      LanguageRepresentation.env, LanguageRepresentation.ty] at * <;>
    simp only [hf, ↓reduceIte] at * <;> grind only

end Signatures.Runtime.Schnorr.ListROM.NativeSelection

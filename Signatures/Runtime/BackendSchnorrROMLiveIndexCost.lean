import Signatures.Runtime.BackendSchnorrROMSelection
import Signatures.Runtime.BackendReverseCost
import Signatures.Runtime.BackendSchnorrROMComparison

/-! Actual compiled chronological live-index costs. The scan counter is bounded
by encountered cache length, with a reservation for the remaining cells. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d := .var (.there (.there (.there .here)))

def indexBodyWith {Γ} (comparison : Expr CryptoOp ([hashKey, hashKey, .pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ) .bool) :
    Expr CryptoOp ([.pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ) indexResult :=
  .branch (.fst v1) v1
    (.letE v2 (.letE (.fst v1)
      (.branch comparison (.pair (.bool true) (.snd v3))
        (.pair (.bool false) (.op .natAdd (.pair (.snd v3) (.nat 1)))))))

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes mono

private theorem indexBodyWith_time {Γ : List (Ty CryptoAtom)}
    (comparison : Expr CryptoOp ([hashKey, hashKey, .pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ) .bool)
    (cell : (M × G₁) × F) (acc : Bool × Nat) (key : M × G₁)
    (xs : List ((M × G₁) × F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width comparisonTime incrementTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hnext : Q.size rep.data.nat (acc.2 + 1) ≤ width)
    (hi : Q.size (rep.env ([.pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ))
      (cell, acc, key, xs, env) ≤ width)
    (hc : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      comparison).time (cell.1, key, cell, acc, key, xs, env) ≤ comparisonTime)
    (hadd : (primitiveBound .natAdd).time (acc.2, 1) ≤ incrementTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (indexBodyWith comparison)).time (cell, acc, key, xs, env) ≤
      comparisonTime + incrementTime + 256 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hresult := hb (comparison.denote (arithmetic F G₁ G₂ K M cost) (cell.1, key, cell, acc, key, xs, env))
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases hf : acc.1 = true <;>
    by_cases he : comparison.denote (arithmetic F G₁ G₂ K M cost) (cell.1, key, cell, acc, key, xs, env) = true <;>
    dsimp only [indexBodyWith, Expression.compileBound, Expression.variableBound, LocalBound.compose, LocalBound.pair,
      LocalBound.fst, LocalBound.snd, LocalBound.identity, LocalBound.elim, LocalBound.castFunction,
      DataCostLaws.selectBound, DataCostLaws.natBound, DataCostLaws.boolBound, DataCostLaws.unitBound,
      Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env,
      List.append, id, Function.comp_def, Sum.elim] at * <;>
    simp only [hf, he, Bool.false_eq_true, ↓reduceIte] at * <;>
    simp only [List.cons_append, List.nil_append, LanguageRepresentation.env, LanguageRepresentation.ty] at * <;>
    grind only

theorem liveIndexBody_time {Γ : List (Ty CryptoAtom)}
    (cell : (M × G₁) × F) (acc : Bool × Nat) (key : M × G₁)
    (xs : List ((M × G₁) × F)) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width messageTime pointTime incrementTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hnext : Q.size rep.data.nat (acc.2 + 1) ≤ width)
    (hi : Q.size (rep.env ([.pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ))
      (cell, acc, key, xs, env) ≤ width)
    (hm : (primitiveBound .messageEq).time (cell.1.1, key.1) ≤ messageTime)
    (hp : (primitiveBound .point₁Eq).time (cell.1.2, key.2) ≤ pointTime)
    (hadd : (primitiveBound .natAdd).time (acc.2, 1) ≤ incrementTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (liveIndexBody.weakenTail Γ)).time (cell, acc, key, xs, env) ≤
      messageTime + pointTime + incrementTime + 1024 * overhead (256 * width) := by
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hx : Q.size (rep.ty hashKey) cell.1 ≤ width := by
    simp only [List.cons_append, List.nil_append, LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hy : Q.size (rep.ty hashKey) key ≤ width := by
    simp only [List.cons_append, List.nil_append, LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hc := NativeCache.hashEq_time (Γ := [.pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ)
    rep data cost primitive sizes laws dataLaws primitiveBound mono
    cell.1 key (cell, acc, key, xs, env) width messageTime pointTime hh hu hb hx hy hi hm hp
  have h := indexBodyWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (hashEq.weakenTail ([.pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ))
    cell acc key xs env width (messageTime + pointTime + 128 * overhead (128 * width)) incrementTime
    hh hu hb hn1 hnext hi hc hadd
  change (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    (indexBodyWith (hashEq.weakenTail ([.pair hashKey scalar, indexResult, hashKey, hashCache] ++ Γ)))).time
      (cell, acc, key, xs, env) ≤ _
  have hf := mono (show 128 * width ≤ 256 * width by omega)
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeSelection

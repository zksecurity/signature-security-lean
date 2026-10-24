import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendSize
import Proofs.Runtime.Coron

/-! Costs of the compiled group arithmetic used by Coron's hash, signature,
and extraction routines. Only individual field/group/comparison primitives have
supplied certificates; expression routing and branch costs are derived here. -/

open PFunctor

namespace Signatures.Runtime.Coron

open BackendProgram

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

include localLaws dataLaws sizes mono

theorem extract_cost (rho : F) (sigma X : G₁) (width scaleTime subTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : Q.size (rep.ty scalar) rho ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hscale : (primitiveBound CryptoOp.scale₁).time (rho, X) ≤ scaleTime)
    (hsub : (primitiveBound CryptoOp.sub₁).time (sigma, rho • X) ≤ subTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive extract)
      (sigma, rho, X, ()) ≤ scaleTime + subTime + 32 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    localLaws dataLaws primitiveBound extract (sigma, rho, X, ())).trans ?_
  have hprod := @sizes.prod_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [extract, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    LanguageRepresentation.ty, LanguageRepresentation.env, Expr.denote, Var.get, arithmetic] at *
  grind only

theorem signReply_cost (rho : F) (X : G₁) (coin width eqTime zeroTime scaleTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : Q.size rep.data.nat coin ≤ width) (h0 : Q.size rep.data.nat 0 ≤ width)
    (hf : Q.size (rep.ty scalar) rho ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (heq : (primitiveBound CryptoOp.natEq).time (coin, 0) ≤ eqTime)
    (hzero : (primitiveBound CryptoOp.zero₁).time () ≤ zeroTime)
    (hscale : (primitiveBound CryptoOp.scale₁).time (rho, X) ≤ scaleTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive signReply)
      (rho, X, coin, ()) ≤ eqTime + zeroTime + scaleTime + 64 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    localLaws dataLaws primitiveBound signReply (rho, X, coin, ())).trans ?_
  have hprod := @sizes.prod_le
  have hleft := sizes.sum_le (rep.env [scalar, point₁, .nat]) (rep.env [scalar, point₁, .nat])
    (Sum.inl (rho, X, coin, ()))
  have hright := sizes.sum_le (rep.env [scalar, point₁, .nat]) (rep.env [scalar, point₁, .nat])
    (Sum.inr (rho, X, coin, ()))
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [signReply, Expression.compileBound, Expression.variableBound,
    LocalBound.castFunction, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    LocalBound.identity, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.natBound,
    DataCostLaws.selectBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Var.get, arithmetic, id, Function.comp_def, Sum.elim] at *
  by_cases hc : coin = 0 <;> simp [hc] <;> grind only

theorem hashReply_cost (rho : F) (g h : G₁) (coin width eqTime zeroTime scaleTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : Q.size rep.data.nat coin ≤ width) (h0 : Q.size rep.data.nat 0 ≤ width)
    (hf : Q.size (rep.ty scalar) rho ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (heq : (primitiveBound CryptoOp.natEq).time (coin, 0) ≤ eqTime)
    (hzero : (primitiveBound CryptoOp.zero₁).time () ≤ zeroTime)
    (hscale : (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ scaleTime)
    (hadd : ∀ y : G₁, (primitiveBound CryptoOp.add₁).time (rho • g, y) ≤ addTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive hashReply)
      (rho, g, h, coin, ()) ≤ eqTime + zeroTime + scaleTime + addTime + 96 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    localLaws dataLaws primitiveBound hashReply (rho, g, h, coin, ())).trans ?_
  have hprod := @sizes.prod_le
  have hleft := sizes.sum_le (rep.env [scalar, point₁, point₁, .nat]) (rep.env [scalar, point₁, point₁, .nat])
    (Sum.inl (rho, g, h, coin, ()))
  have hright := sizes.sum_le (rep.env [scalar, point₁, point₁, .nat]) (rep.env [scalar, point₁, point₁, .nat])
    (Sum.inr (rho, g, h, coin, ()))
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [hashReply, Expression.compileBound, Expression.variableBound,
    LocalBound.castFunction, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    LocalBound.identity, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.natBound,
    DataCostLaws.selectBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Var.get, arithmetic, id, Function.comp_def, Sum.elim] at *
  by_cases hc : coin = 0 <;> simp [hc] <;> grind only

end Signatures.Runtime.Coron

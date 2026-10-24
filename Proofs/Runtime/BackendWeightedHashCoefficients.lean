import Proofs.Runtime.WeightedExtraction
import Proofs.Runtime.BackendWeightedCoefficientBudget

/-! The hash transcript uses the same chronological coefficient routine as
signatures, with a single base of weight one. These native costs include that
executed one constant and multiplication, even though they simplify in the
source law. No finished preparation budget is assumed. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open Terms Coefficients BackendProgram LazyAGM.ReplySyntax

def hashCoefficientTime (overhead : Nat → Nat)
    (width tokenCap coeffCap oneTime mulTime comparisonTime subtractTime addTime zeroTime : Nat) : Nat :=
  coefficientTime overhead (5 * width) tokenCap coeffCap 1
    (oneTime + 32 * overhead (128 * coefficientGeneratorWidth width tokenCap coeffCap 1))
    mulTime comparisonTime subtractTime addTime zeroTime

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
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include laws dataLaws sizes lists mono

theorem hashTerms_weakenTail_time {indexTy : Ty CryptoAtom} {Γ : List (Ty CryptoAtom)}
    (key : indexTy.Value (cryptoBase F G₁ G₂ K M)) (tail : Env (cryptoBase F G₁ G₂ K M) Γ)
    (width oneTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty indexTy) key ≤ width) (ht : Q.size (rep.env Γ) tail ≤ width)
    (hf : Q.size (rep.ty scalar) (1 : F) ≤ width)
    (h1 : (primitiveBound .one).time () ≤ oneTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound ((hashTerms (indexTy := indexTy)).weakenTail Γ)).time (key, tail) ≤
        oneTime + 32 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hnil := lists.nil_le (rep.ty (termTy indexTy))
  have hcons := lists.cons_le (rep.ty (termTy indexTy)) (key, (1 : F)) []
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [hashTerms, Expr.weakenTail, Var.weakenTail, v0, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound,
    Expr.denote, Var.get, arithmetic, termTy, LanguageRepresentation.ty,
    LanguageRepresentation.env, List.cons_append, List.nil_append, List.append] at *
  grind only

theorem hashCoefficients_cost {indexTy : Ty CryptoAtom}
    (tr : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (width tokenCap coeffCap oneTime mulTime comparisonTime subtractTime addTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ n ≤ tokenCap + 1, Q.size rep.data.nat n ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hk : ∀ p ∈ tr, Q.size (rep.ty (AGM.tokenTy indexTy)) p ≤ width)
    (htc : tr.length ≤ tokenCap) (hcc : coeff.length ≤ coeffCap)
    (h1 : (primitiveBound .one).time () ≤ oneTime)
    (hm : ∀ x y : F, (primitiveBound .mul).time (x, y) ≤ mulTime)
    (hEq : ∀ n ≤ tokenCap, (primitiveBound .natEq).time (n, 0) ≤ comparisonTime)
    (hSub : ∀ n ≤ tokenCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hAdd : ∀ n ≤ tokenCap, (primitiveBound .natAdd).time (n, 1) ≤ addTime)
    (hZero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (signedTerms (hashTerms (indexTy := indexTy)))) (tr, coeff, ()) ≤
      hashCoefficientTime overhead width tokenCap coeffCap oneTime mulTime comparisonTime subtractTime addTime zeroTime := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound _ _).trans
  have hw : width ≤ 5 * width := by omega
  have hkey p (hp : p ∈ tr) : Q.size (rep.ty indexTy) p.1 ≤ width :=
    (sizes.fst_le (rep.ty indexTy) (rep.ty point₁) p).trans (hk p hp)
  have hterms p (hp : p ∈ tr) t
      (ht : t ∈ (hashTerms (indexTy := indexTy)).denote (arithmetic F G₁ G₂ K M cost) (p.1, ())) :
      Q.size (rep.ty (termTy indexTy)) t ≤ 5 * width := by
    change t ∈ [(p.1, (1 : F))] at ht
    have heq := List.mem_singleton.mp ht
    subst t
    have h := sizes.prod_le (rep.ty indexTy) (rep.ty scalar) (p.1, (1 : F))
    exact h.trans (by have := hkey p hp; have := hf 1; dsimp only at *; omega)
  have hW := coefficientGeneratorWidth_ge width tokenCap coeffCap 1
  exact signedTerms_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    hashTerms tr coeff (5 * width) tokenCap coeffCap 1
    (oneTime + 32 * overhead (128 * coefficientGeneratorWidth width tokenCap coeffCap 1))
    mulTime comparisonTime subtractTime addTime zeroTime (hh.trans hw) (hu.trans hw)
    (fun b => (hb b).trans hw) (fun n hn' => (hn n hn').trans hw) (fun f => (hf f).trans hw)
    (fun p hp => (hk p hp).trans hw) htc hcc hterms (fun _ => rfl)
    (by
      intro p hp Δ tail hs
      exact hashTerms_weakenTail_time rep data cost primitive laws dataLaws primitiveBound sizes lists mono
        p.1 tail (coefficientGeneratorWidth width tokenCap coeffCap 1) oneTime
        (hh.trans hW) (hu.trans hW) ((hkey p hp).trans hW) hs ((hf 1).trans hW) h1)
    hm hEq hSub hAdd hZero

end Signatures.Runtime.WeightedAGM.Extract

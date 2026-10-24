import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendExpressionSize
import Proofs.Runtime.BackendDataSize

/-! Turn a compiled two-input comparison expression into a local comparison
routine. The adapter is ordinary product/unit code, with its own time and
stored-description bounds. No new comparison primitive is assumed. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram.Comparison

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  {key : Ty Atom}

def inputs : Q.Realizer (rep.ty (.pair key key)) (rep.env [key, key])
    (fun p => (p.1, p.2, ())) :=
  QP.pair (QP.fst (rep.ty key) (rep.ty key))
    (QP.pair (QP.snd (rep.ty key) (rep.ty key)) (data.unit (rep.ty (.pair key key))))

/-- The executable comparator consists of the input adapter followed by the
actual compiled expression. Its semantic index states equality correctness. -/
def code (eq : Expr Op [key, key] .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y)) :
    Q.Realizer (rep.ty (.pair key key)) rep.data.bool (fun p => decide (p.1 = p.2)) :=
  (Q.compose (inputs rep data) (Expression.compile rep data P primitive eq)).castFunction
    (by funext p; exact heq p.1 p.2)

theorem description (eq : Expr Op [key, key] .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (code rep data P primitive eq heq) ≤
      sizes.localSize (Expression.compile rep data P primitive eq) + 6 * allowance := by
  rw [code, DescriptionSize.castFunction]
  have h := laws.compose_bound
    (laws.pair_bound (laws.fst (rep.ty key) (rep.ty key))
      (laws.pair_bound (laws.snd (rep.ty key) (rep.ty key))
        (dataLaws.unit (rep.ty (.pair key key)))))
    (le_refl (sizes.localSize (Expression.compile rep data P primitive eq)))
  exact h.trans (by omega)

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)

include sizes laws dataLaws mono

theorem cost (eq : Expr Op [key, key] .bool) [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (x y : key.Value base) (width comparisonTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hx : Q.size (rep.ty key) x ≤ width) (hy : Q.size (rep.ty key) y ≤ width)
    (hc : Q.cost (Expression.compile rep data P primitive eq) (x, y, ()) ≤ comparisonTime) :
    Q.cost (code rep data P primitive eq heq) (x, y) ≤
      comparisonTime + 6 * overhead (16 * width) := by
  rw [code, QuantitativeStepClass.Realizer.cost_castFunction]
  let ha := LocalBound.pair laws (LocalBound.fst laws (rep.ty key) (rep.ty key))
    (LocalBound.pair laws (LocalBound.snd laws (rep.ty key) (rep.ty key))
      (dataLaws.unitBound (rep.ty (.pair key key))))
  have h := laws.compose (inputs rep data) (Expression.compile rep data P primitive eq) (x, y)
  have hi := ha.cost_le (x, y)
  have hp := @sizes.prod_le
  have hfee : ∀ n ≤ 16 * width, overhead n ≤ overhead (16 * width) := fun _ h => mono h
  have hbool := hb (eq.denote P (x, y, ()))
  dsimp only [ha, inputs, LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.BackendProgram.Comparison

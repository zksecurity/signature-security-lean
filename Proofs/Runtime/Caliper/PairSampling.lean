import Proofs.Runtime.Caliper.InteractiveControlBounds
import Proofs.Runtime.Caliper.Pairing
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! Independent pair sampling from two executed samplers. The first result is
copied to a buffer beyond the second sampler's lowered footprint. Restoration
and the final permutation execute ordinary Caliper instructions. -/

namespace Signatures.Runtime.CaliperBackend.PairSampling

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {A B I : Type} {spec : OracleSpec I}
    (left : Layout w A) (right : Layout w B)
    (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)

def input (w : Nat) : Layout w Unit := DataImplementation.unitLayout w

def output : Layout w (A × B) := left.prod right fits

def finish : Realizer .unit (right.representation.prod left.representation (by omega))
    (output left right fits).representation
    (fun value => ⟨(value.2.val, value.1.val), value.2.property, value.1.property⟩) :=
  (Pairing.swap .unit (by decide) right.representation left.representation hw (by omega)).viewOutput
    (output left right fits).representation (fun value => (productView left right).symm (value.2, value.1)) (by
      intro value
      exact congrArg (left.representation.prod right.representation fits).encoding.encode
        ((productView left right).apply_symm_apply (value.2, value.1)))

def retained (port : Interactive.Port w spec) (second : Interactive.Code w) : Interactive.Code w :=
  Interactive.retain second (Interactive.savedBuffer port second) 0
    right.representation.encoding.words left.representation.encoding.words

def code (port : Interactive.Port w spec) (first second : Interactive.Code w) : Interactive.Code w :=
  .seq first (.seq (retained left right port second) (.compute (finish left right hw fits).code))

def denote (first : OracleComp spec left.Value) (second : OracleComp spec right.Value) :
    OracleComp spec (output left right fits).Value := do
  let x ← first
  (fun y => ⟨(x.val, y.val), x.property, y.property⟩) <$> second

variable {left right hw fits} {port : Interactive.Port w spec}
    {firstSource : OracleComp spec left.Value} {secondSource : OracleComp spec right.Value}
    {first second : Interactive.Code w}

include hw in
theorem retained_refines
    (secondCorrect : Interactive.Refines port .unit (input w).representation right.representation
      (fun _ => secondSource) second) :
    Interactive.Refines port .unit left.representation
      (right.representation.prod left.representation (by omega))
      (fun x => (fun y => (y, x)) <$> secondSource) (retained left right port second) := by
  have saved := secondCorrect.retain (by decide) left.representation hw
    (by change 0 + left.representation.encoding.words < 2 ^ w; simpa using left.representation.fits)
    (by omega)
  exact saved.viewInput left.representation (fun x => (⟨(), trivial⟩, x)) (fun _ => rfl)

theorem refines
    (firstCorrect : Interactive.Refines port .unit (input w).representation left.representation
      (fun _ => firstSource) first)
    (secondCorrect : Interactive.Refines port .unit (input w).representation right.representation
      (fun _ => secondSource) second) :
    Interactive.Refines port .unit (input w).representation (output left right fits).representation
      (fun _ => denote left right fits firstSource secondSource) (code left right hw fits port first second) := by
  have combined := firstCorrect.seq ((retained_refines (hw := hw) (fits := fits) secondCorrect).seq
    (Interactive.Refines.compute port .unit (finish left right hw fits)))
  convert combined using 1
  · funext value
    simp only [denote, bind_pure_comp, Functor.map_map]
  · rfl

variable (left right fits)

theorem erase (firstSource : OracleComp spec left.Value) (secondSource : OracleComp spec right.Value) :
    Subtype.val <$> denote left right fits firstSource secondSource = (do
      let x ← (Subtype.val <$> firstSource)
      (fun y => (x, y)) <$> (Subtype.val <$> secondSource)) := by
  simp only [denote, map_bind, bind_map_left, Functor.map_map]

/-- Independence is inherited from two sequential source draws. No additional
pair-sampling primitive or law is assumed. -/
theorem uniform [SampleableType A] [SampleableType B]
    (firstSource : ProbComp left.Value) (secondSource : ProbComp right.Value)
    (firstLaw : Subtype.val <$> firstSource = ($ᵗ A : ProbComp A))
    (secondLaw : Subtype.val <$> secondSource = ($ᵗ B : ProbComp B)) :
    Subtype.val <$> denote left right fits firstSource secondSource = ($ᵗ (A × B) : ProbComp (A × B)) := by
  rw [erase, firstLaw, secondLaw]
  change (do let x ← ($ᵗ A : ProbComp A); (fun y => (x, y)) <$> ($ᵗ B : ProbComp B)) =
    ((Prod.mk <$> ($ᵗ A : ProbComp A)) <*> ($ᵗ B : ProbComp B))
  simp only [seq_eq_bind_map, bind_map_left]

end Signatures.Runtime.CaliperBackend.PairSampling

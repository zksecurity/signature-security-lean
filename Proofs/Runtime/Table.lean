import Proofs.Runtime.Sampling
import Proofs.Runtime.Index

/-! Exact correspondence of sampled list storage to the native finite-function sampler.
The function view below is proof-only. Executable accesses must use a charged index or
keyed lookup; converting a runtime key to its canonical index is not a free instruction. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

/-- Proof-only view of complete scalar storage in the native enumeration order. -/
noncomputable def tableFunction {ι α : Type} [Fintype ι] (default : α) (xs : List α) : ι → α :=
  fun i => (xs[(Fintype.equivFin ι i).val]?).getD default

theorem tableFunction_vector {ι α : Type} [Fintype ι] (default : α)
    (v : Vector α (Fintype.card ι)) :
    tableFunction (ι := ι) default v.toList = fun i => v[(Fintype.equivFin ι i).val] := by
  funext i
  simp [tableFunction]

/-- The native Fintype-indexed function instance samples each scalar separately. This is
an equality of oracle programs, not a guessed whole-table primitive price. -/
theorem uniform_function_vector (ι α : Type) [Fintype ι] [DecidableEq ι] [SampleableType α] :
    ($ᵗ (ι → α) : ProbComp (ι → α)) =
      (fun v : Vector α (Fintype.card ι) => fun i => v[(Fintype.equivFin ι i).val]) <$>
        SampleableType.vector α (Fintype.card ι) := by
  change (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl α)) <$>
      ((arrayVectorEquivFin α (Fintype.card ι)) <$> SampleableType.vector α (Fintype.card ι)) = _
  simp only [Functor.map_map]
  rfl

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type} {cell : Ty Atom}

theorem sampleTable_function (ι : Type) [Fintype ι] [DecidableEq ι]
    (P : Primitives base Op) (H : Semantics base Cmd unifSpec)
    [SampleableType (cell.Value base)] (draw : Cmd .unit cell)
    (hdraw : H draw () = $ᵗ cell.Value base) (default : cell.Value base) :
    tableFunction (ι := ι) default <$>
      (sampleTable (Op := Op) draw).denote P H (Fintype.card ι, ()) = $ᵗ (ι → cell.Value base) := by
  rw [sampleTable_uniform P H draw hdraw, uniform_function_vector]
  simp only [Functor.map_map]
  congr 1
  funext v
  exact tableFunction_vector default v

end Signatures.Runtime

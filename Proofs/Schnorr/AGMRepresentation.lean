import Signatures.Schnorr.Spec.AGM
import Proofs.Schnorr.AGM

/-! Flatten the actual AGM interface's coefficient vectors over the chronological
received basis. Outgoing requests never extend this basis. -/

open AlgebraicGroupModel.Interaction

namespace Schnorr.AGM

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- The initial generator and public key, in the order exposed by the game. -/
def initialRepresentations : List (Affine F) := [⟨1, 0⟩, ⟨0, 1⟩]

def representedBasis (g pk : G) (reps : List (Affine F)) : Groups (Group G) :=
  fun _ => reps.map (fun a => a.eval g pk)

@[simp] theorem representedBasis_initial (g pk : G) :
    representedBasis g pk (initialRepresentations (F := F)) = (initial g pk).groups := by
  funext s
  simp [representedBasis, initialRepresentations, Affine.eval, initial]

@[simp] theorem representedBasis_append (g pk : G) (reps bs : List (Affine F)) :
    representedBasis g pk (reps ++ bs) =
      extend (representedBasis g pk reps) (representedBasis g pk bs) := by
  funext s
  simp [representedBasis, extend]

/-- Same zero-padding convention as Interaction.evaluate, including malformed vectors. -/
def flatten (coeff : List F) (reps : List (Affine F)) : Affine F :=
  combine (reps.mapIdx fun n a => ((coeff[n]?).getD 0, a))

theorem flatten_eval (g pk : G) (coeff : List F) (reps : List (Affine F)) :
    (flatten coeff reps).eval g pk = evaluate coeff (representedBasis g pk reps ()) := by
  rw [flatten, combine_eval]
  simp [representedBasis, evaluate, List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def]

/-- A singleton group argument has exactly one vector, and flattening it gives
the very same point received by the hash oracle. -/
theorem valid_singleton {D : Type} (g pk R : G) (reps : List (Affine F))
    (out : Explained F D (Group G))
    (hv : out.Valid (representedBasis g pk reps)) (hR : out.value.groups () = [R]) :
    ∃ coeff : List F, out.coefficients () = [coeff] ∧
      coeff.length = reps.length ∧ (flatten coeff reps).eval g pk = R := by
  have h := hv ()
  rw [hR] at h
  cases hc : out.coefficients () with
  | nil => simp [hc] at h
  | cons coeff rest =>
      rw [hc] at h
      cases h with
      | cons hhead htail =>
          cases htail
          exact ⟨coeff, rfl, by simpa [representedBasis] using hhead.1,
            (flatten_eval g pk coeff reps).trans hhead.2⟩

end Schnorr.AGM

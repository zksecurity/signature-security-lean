import Signatures.Schnorr.Spec.AGM
import Proofs.Schnorr.AGM
import Signatures.Schnorr.Spec.NonzeroNonce
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Schnorr.AGM

namespace SignaturesTest.SchnorrAGM

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example (g pk : ZMod 7) : (initial g pk).groups () = [g, pk] := rfl

/-- Hash replies cannot silently enlarge the basis. -/
example (c : ZMod 7) : (scalarReply (G := ZMod 7) c).groups () = [] := rfl

/-- Signing replies expose exactly the commitment; the response is a scalar. -/
example (R z : ZMod 7) :
    (signingReply R z).groups () = [R] ∧ (signingReply R z).data = z := ⟨rfl, rfl⟩

example (x c : ZMod 7) (a : Affine (ZMod 7)) (h : a.secret + c ≠ 0) :
    ((a.constant + (a.secret + c) * x) - a.constant) / (a.secret + c) = x := by
  apply (div_eq_iff h).2
  ring

/-- If the coefficient is chosen after the challenge, badness can be certain.
This is why the proof must use the representation from the first hash query. -/
example (c : ZMod 7) : (Affine.mk 0 (-c)).secret + c = 0 := by simp

example (g : ZMod 7) (hg : Function.Injective (fun x : ZMod 7 => x • g))
    (a : (ZMod 7)ˣ) : (a : ZMod 7) • g ≠ 0 :=
  Schnorr.NonzeroNonce.commitment_ne_zero (F := ZMod 7) g hg a

end SignaturesTest.SchnorrAGM

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Schnorr.AGM.extract, ``Schnorr.AGM.combine_eval,
      ``Schnorr.AGM.bad_challenge_probability, ``Schnorr.NonzeroNonce.verifies,
      ``Schnorr.NonzeroNonce.commitment_ne_zero] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"

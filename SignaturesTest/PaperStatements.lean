import Signatures.PaperStatements
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

namespace SignaturesTest.PaperStatements

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def repeated : List (ZMod 5 × Bool) := [(1, true), (1, true), (2, false)]

-- The paper-facing game counts repeated calls; the stronger original counts points.
example : OOPS.LazyAGM.admissible 1 (2, true) repeated := by
  unfold OOPS.LazyAGM.admissible
  decide +kernel
example : ¬ OOPS.LazyAGM.callAdmissible 1 (2, true) repeated := by
  unfold OOPS.LazyAGM.callAdmissible
  decide +kernel
example : OOPS.LazyAGM.callAdmissible 2 (2, true) repeated := by
  unfold OOPS.LazyAGM.callAdmissible
  decide +kernel

-- The limit is inclusive and only concerns the target topic, including at degree zero.
example : OOPS.LazyAGM.callAdmissible 1 (3, false) repeated := by
  unfold OOPS.LazyAGM.callAdmissible
  decide +kernel
example : OOPS.LazyAGM.callAdmissible 0 ((2, true) : ZMod 5 × Bool) [(1, false)] := by
  unfold OOPS.LazyAGM.callAdmissible
  decide +kernel
example : ¬ OOPS.LazyAGM.callAdmissible 0 ((2, true) : ZMod 5 × Bool) [(1, true)] := by
  unfold OOPS.LazyAGM.callAdmissible
  decide +kernel

open Lean Meta Elab Command

-- The comparison concerns one lazy execution, even with infinitely many possible topics.
open OracleComp AlgebraicGroupModel in
example {F G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearPairing F G₁ G₂ Gₜ]
    (g₁ : G₁) (g₂ : G₂) (d : Nat)
    (A : Model.LazyAGM.Adversary F (Nat × Fin (d + 1)) (F × Nat) G₁ G₂) :
    𝒟[OOPS.LazyAGM.callGame (Gₜ := Gₜ) g₁ g₂ d A] {true} ≤
      𝒟[OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A] {true} :=
  OOPS.LazyAGM.callGame_le_game g₁ g₂ d A

run_cmd liftTermElabM do
  for name in #[``OOPS.LazyAGM.callGame_le_game] do
    let axioms ← collectAxioms name
    let expected := #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.size == expected.size && axioms.all expected.contains do
      throwError "{name}: unexpected axiom footprint {axioms}"
  forallTelescope (← getConstInfo ``OOPS.LazyAGM.callGame_le_game).type fun ps _ => do
    for p in ps do
      let type ← inferType p
      if type.isAppOf ``Fintype || type.isAppOf ``Finite then
        throwError "Game comparison must not require a finite enumeration: {type}"
      if type.isAppOf ``DecidableEq then
        let .fvar id := type.getAppArgs[0]! | continue
        if (← id.getUserName) == `F then
          throwError "Game comparison must not require scalar decidable equality"

end SignaturesTest.PaperStatements

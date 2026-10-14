import Signatures.Runtime.SchnorrRandomness

/-! A private primitive may have multiple internal queries. Forking must retain their
joint result across the shared prefix rather than sampling it separately in each run. -/

open OracleComp OracleSpec Signatures.Runtime.Replay

namespace SignaturesTest.SchnorrRandomness

private abbrev raw := (Unit →ₒ Bool) + (Unit →ₒ Bool)
private abbrev macros := (Unit →ₒ Bool) + (Unit →ₒ Bool)

private def twoDraws : QueryImpl (Unit →ₒ Bool) (OracleComp raw) := fun _ => do
  let x ← raw.query (.inl ())
  let y ← raw.query (.inl ())
  pure (x != y)

private theorem privateOnly (i : Unit) :
    IsQueryBoundP (twoDraws i) (fun j => j = Sum.inr ()) 0 := by
  simp [twoDraws]

private def program : OracleComp macros (Bool × Bool) := do
  let random ← macros.query (.inl ())
  let challenge ← macros.query (.inr ())
  pure (random, challenge)

example : simulateQ (expandPrivate twoDraws)
    (contextFork program (fun _ => 0) (.inr ()) (fun _ => some 0)) =
      contextFork (simulateQ (expandPrivate twoDraws) program)
        (fun _ => 0) (.inr ()) (fun _ => some 0) :=
  contextFork_expand twoDraws privateOnly program 0 (fun _ => some 0)

-- The private draw is issued once before the two focused challenges.
example : forkKernel (.inr ()) program (fun _ => some 0) = (do
    let random ← macros.query (.inl ())
    let original ← macros.query (.inr ())
    let fresh ← macros.query (.inr ())
    pure ((random, original), some (original, fresh, (random, fresh)))) := by
  change forkKernel (spec := macros) (.inr ())
    (OracleComp.queryBind (spec := macros) (.inl ()) (fun random =>
      OracleComp.queryBind (.inr ()) (fun challenge => pure (random, challenge)))) _ = _
  rw [forkKernel_other (spec := macros) (Sum.inr ()) (Sum.inl ()) (by decide)]
  apply congrArg (OracleComp.queryBind (spec := macros) (Sum.inl ()))
  funext random
  rw [forkKernel_target]
  apply congrArg (OracleComp.queryBind (spec := macros) (Sum.inr ()))
  funext original
  simp [forkKernel_pure]
  rfl

-- Equal answers and an absent selected occurrence still reject after expansion.
example : acceptKernel (fun _ : Bool => some (0 : Fin 1))
    (true, some (false, false, false)) = none := rfl

example : acceptKernel (fun _ : Bool => some (0 : Fin 1))
    (true, (none : Option (Bool × Bool × Bool))) = none := rfl

end SignaturesTest.SchnorrRandomness

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``forkKernel_eq_contextFork, ``forkKernel_expand, ``contextFork_expand,
      ``Signatures.Runtime.Schnorr.expand_contextFork,
      ``Signatures.Runtime.Schnorr.expand_loggedFork] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"

import Proofs.Runtime.SchnorrLazySeedLog
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Schnorr
open Signatures.Runtime.Schnorr.SeedTape Signatures.Runtime.Schnorr.LazySeed

namespace SignaturesTest.SchnorrLazySeed

private abbrev F := ZMod 5
private abbrev spec := replaySpec F

private def first : OracleComp spec (F × Fin 2 × F) := do
  let challenge ← spec.query (.inr ())
  let bit ← spec.query (.inl (.inl 1))
  let scalar ← spec.query (.inl (.inr ()))
  pure (challenge, bit, scalar)

private def second : OracleComp spec (F × Fin 3 × Fin 2 × F × Fin 2) := do
  let challenge ← spec.query (.inr ())
  let newRange ← spec.query (.inl (.inl 2))
  let bit ← spec.query (.inl (.inl 1))
  let scalar ← spec.query (.inl (.inr ()))
  let newBit ← spec.query (.inl (.inl 1))
  pure (challenge, newRange, bit, scalar, newBit)

/-- Both kinds of private randomness are drawn after the challenge, retained
on replay, and unaffected by a previously unseen family on the divergent path.
An additional draw in an exhausted family is sampled fresh exactly once. -/
example : Prod.fst <$> twoPass first (fun _ => second) (.inr ()) (fun _ => 0) (fun _ => (4 : F)) = (do
    let challenge ← spec.query (.inr ())
    let bit ← spec.query (.inl (.inl 1))
    let scalar ← spec.query (.inl (.inr ()))
    let newRange ← spec.query (.inl (.inl 2))
    let newBit ← spec.query (.inl (.inl 1))
    pure ((challenge, bit, scalar), ((4 : F), newRange, bit, scalar, newBit))) := by
  simp only [twoPass, first, second, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  have hbit (bit : Fin 2) : (⟨bit.val % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) = bit := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt bit.isLt
  simp [StateT.run, LazySeed.oracle, restart, State.fromTape, reset, trim, hbit,
    pop, familyTag, encodeReply, decodeReply, map_bind, bind_map_left, Functor.map_map]

/-- A numeric range far larger than the query count requires one saved cell,
not a seed for each smaller range. No answer-space enumeration occurs. -/
example (s : State F) (h : s.remaining = []) :
    (LazySeed.oracle (.inl (.inl 1000000))).run s =
      (fun answer : Fin 1000001 =>
        (answer, { s with saved := s.saved ++ [(1000002, 0, answer.val)] })) <$>
          (liftM (spec.query (.inl (.inl 1000000))) : OracleComp spec _) := by
  simp [LazySeed.oracle, StateT.run, h, pop, encodeReply]

/-- Empty executions still retain the inserted replacement cell. -/
example : twoPass (pure () : OracleComp spec Unit) (fun _ => pure ())
    (.inr ()) (fun _ => 0) (fun _ => (4 : F)) =
      pure (((), ()), (⟨[(1, 4, 0)], [(1, 4, 0)]⟩ : State F)) := rfl

example : IsTotalQueryBound first 3 := by
  simp [first, map_eq_bind_pure_comp, IsTotalQueryBound]

example : IsTotalQueryBound second 5 := by
  simp [second, map_eq_bind_pure_comp, IsTotalQueryBound]

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LazySeed.oracle_refines, ``LazySeed.simulate_seeded,
      ``run'_empty, ``run_log, ``twoPass_seeded, ``restart_seed, ``restart_other,
      ``oracle_saved_extends, ``simulate_growth, ``firstPass_growth,
      ``twoPass_growth, ``twoPass_queryBound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``run_log, ``twoPass_seeded, ``simulate_seeded, ``simulate_growth,
      ``twoPass_growth, ``twoPass_queryBound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Finite, ``Fintype, ``Program,
            `Signatures.Runtime.Schnorr.SourceCertificate] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: unexpected finite-domain or restricted-source requirement {forbidden}"

end SignaturesTest.SchnorrLazySeed

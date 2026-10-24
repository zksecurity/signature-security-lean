import Proofs.Runtime.SchnorrAGMSecurity
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec AlgebraicGroupModel.Interaction Schnorr.AGM
open Signatures.Runtime Signatures.Runtime.SchnorrAGM

namespace SignaturesTest.SchnorrAGMFiniteCache

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7
noncomputable local instance : SampleableType F := SampleableType.ofFintype _

-- Messages have an infinite domain. Only encountered message/point pairs are stored.
private def firstState : SchnorrAGM.State F F Nat :=
  record {} (0, 1) ⟨1, 0⟩ 2

-- A late representation with a zero denominator must not replace the first one.
example : (SchnorrAGM.read (0, (1 : F)) ⟨0, 5⟩).run firstState = pure (2, firstState) := by
  simp [SchnorrAGM.read, StateT.run, firstState, record, cacheMap]

example : (signedState firstState 1 3 0 2 0).cache = firstState.cache := by
  have hR : (0 : F) • (1 : F) - (2 : F) • (3 : F) = 1 := by decide
  simp only [signedState, hR]
  simp [firstState, record, cacheMap]

-- Signing before hashing leaves a programmed entry with no extractable affine record.
private def signedFirst : SchnorrAGM.State F F Nat := signedState {} 1 3 0 2 0

example : (SchnorrAGM.read (0, (1 : F)) ⟨0, 5⟩).run signedFirst = pure (2, signedFirst) := by
  have hR : (0 : F) • (1 : F) - (2 : F) • (3 : F) = 1 := by decide
  simp only [signedFirst, signedState, hR]
  simp [SchnorrAGM.read, StateT.run, cacheMap]

example : cacheMap signedFirst.cache (0, 1) = some ⟨2, none⟩ := by
  have hR : (0 : F) • (1 : F) - (2 : F) • (3 : F) = 1 := by decide
  simp only [signedFirst, signedState, hR]
  simp [cacheMap]

private def lateExplanation : Explained F (Nat × F) (Group F) :=
  ⟨⟨(0, 0), fun _ => [1]⟩, fun _ => [[0, 5]]⟩

example : (SchnorrAGM.finish (1 : F) 3 lateExplanation).run firstState =
    pure ((true, 3), firstState) := by
  simp only [SchnorrAGM.finish, lateExplanation, StateT.run_bind, StateT.run_get,
    StateT.run_pure, pure_bind]
  norm_num [firstState, SchnorrAGM.read, record, cacheMap, StateT.run, smul_eq_mul]
  constructor
  · decide
  · apply (div_eq_iff (by decide : (2 : F) ≠ 0)).2
    decide

private abbrev hashRequest (m : Nat) (coeffs : List (List F)) : Explained F (Request Nat) (Group F) :=
  ⟨⟨.hash m, fun _ => [1]⟩, fun _ => coeffs⟩

example : (SchnorrAGM.handler (1 : F) 3 (hashRequest 0 [])).run firstState =
    pure (scalarReply (0 : F), rejected firstState) := rfl

example : (SchnorrAGM.handler (1 : F) 3 (hashRequest 0 [[1, 0], [0, 5]])).run firstState =
    pure (scalarReply (0 : F), rejected firstState) := rfl

-- A malformed vector length is still treated exactly as by the source handler.
example : (SchnorrAGM.handler (1 : F) 3 (hashRequest 0 [[]])).run firstState =
    pure (scalarReply (2 : F), firstState) := by
  simp [SchnorrAGM.handler, hashRequest, SchnorrAGM.read, StateT.run,
    firstState, record, cacheMap]
  rfl

-- Malformed random requests still consume the requested randomness.
private def malformedRandom : Explained F (Request Nat) (Group F) :=
  ⟨⟨.random 3, fun _ => [1]⟩, fun _ => []⟩

example : (SchnorrAGM.handler (1 : F) 3 malformedRandom).run firstState =
    (fun r => (⟨r, fun _ => []⟩, rejected firstState)) <$>
      (liftM (unifSpec.query 3) : ProbComp (Fin 4)) := by
  simp [SchnorrAGM.handler, malformedRandom, StateT.run, bind_pure_comp]

private def adaptive : OracleComp (explainedSpec F (Group F) (Request Nat) (Reply F Nat))
    (Message F (Group F)) := do
  let reply : Message F (Group F) ←
    (explainedSpec F (Group F) (Request Nat) (Reply F Nat)).query (hashRequest 0 [[1, 0]])
  if reply.data = 2 then
    (explainedSpec F (Group F) (Request Nat) (Reply F Nat)).query (hashRequest 0 [[0, 5]])
  else
    (explainedSpec F (Group F) (Request Nat) (Reply F Nat)).query (hashRequest 1 [[1, 0]])

set_option backward.isDefEq.respectTransparency false in
example : (simulateQ (SchnorrAGM.handler (1 : F) 3) adaptive).run firstState =
    pure (scalarReply 2, firstState) := by
  simp only [adaptive, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp [SchnorrAGM.handler, hashRequest, SchnorrAGM.read, StateT.run,
    firstState, record, cacheMap, scalarReply]

-- The final verification read can insert a previously unseen target.
private def unseenFinal : Explained F (Nat × F) (Group F) :=
  ⟨⟨(1, 0), fun _ => [1]⟩, fun _ => [[1, 0]]⟩

example (p : (Bool × F) × SchnorrAGM.State F F Nat)
    (hp : p ∈ support ((SchnorrAGM.finish (1 : F) 3 unseenFinal).run {})) :
    p.2.cache.length = 1 ∧ p.2.signed = [] := by
  simp only [SchnorrAGM.finish, unseenFinal, StateT.run_bind, StateT.run_get,
    StateT.run_pure, pure_bind] at hp
  simp only [SchnorrAGM.read, StateT.run, cacheMap, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨mid, ⟨c, _, rfl⟩, rfl⟩ := hp
  exact ⟨rfl, rfl⟩

open Lean Meta in
run_meta do
  for name in #[``SchnorrAGM.read_erase, ``SchnorrAGM.handler_erase,
      ``SchnorrAGM.simulate_erase, ``SchnorrAGM.finish_erase, ``SchnorrAGM.run_erase,
      ``SchnorrAGM.run_growth, ``SchnorrAGM.simulate_valid, ``SchnorrAGM.run_extract,
      ``SchnorrAGM.dlogExperiment_eq, ``SchnorrAGM.security] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"

end SignaturesTest.SchnorrAGMFiniteCache

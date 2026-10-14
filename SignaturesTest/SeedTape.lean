import Signatures.Runtime.SchnorrSeededPassBudget
import Signatures.Runtime.SeedTapeReset
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Schnorr
open Signatures.Runtime.Schnorr.SeedTape

namespace SignaturesTest.SeedTape

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def primitives := arithmetic F F F Unit Unit PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨11, fun _ => 7⟩
private def tape : List (TapeCell F) :=
  [(1, 2, 0), (3, 0, 1), (0, 4, 0), (1, 3, 0), (3, 0, 0)]

/-- Interleaved requests consume their own family's first cell. -/
example : pop 3 (0, 0, 0) tape =
    (true, (3, (0 : F), 1), [(1, 2, 0), (0, 4, 0), (1, 3, 0), (3, 0, 0)]) := rfl

example : values (.inl (.inl 1)) tape = [(1 : Fin 2), 0] := rfl

example : (fun z => (z.1.value, z.2)) <$>
    (((uniformDraw 1).run primitives (Machine.effects sampling store) ((), ())).run tape) =
      pure ((1 : Fin 2), [(1, (2 : F), 0), (0, 4, 0), (1, 3, 0), (3, 0, 0)]) := by
  refine (uniformDraw_erase (F := F) (G₁ := F) (G₂ := F) (K := Unit) (M := Unit)
    PrimitiveCosts.unit sampling 1 1 1 tape).trans ?_
  rfl

/-- A missing family falls back to fresh randomness and leaves every cell intact. -/
example : (fun z => (z.1.value, z.2)) <$>
    (((uniformDraw 2).run primitives (Machine.effects sampling store) ((), ())).run tape) =
      (fun b : Fin 3 => (b, tape)) <$> (liftM (unifSpec.query 2) : ProbComp (Fin 3)) := by
  refine (uniformDraw_erase (F := F) (G₁ := F) (G₂ := F) (K := Unit) (M := Unit)
    PrimitiveCosts.unit sampling 1 1 2 tape).trans ?_
  rfl

/-- Reset keeps one hash answer and every private answer, replacing the next hash. -/
example : reset 1 1 (1, (4 : F), 0) tape =
    [(1, (2 : F), 0), (3, 0, 1), (0, 4, 0), (3, 0, 0), (1, 4, 0)] := rfl

example : resetCode.denote primitives (1, 1, tape, (1, (4 : F), 0), ()) =
    [(1, (2 : F), 0), (3, 0, 1), (0, 4, 0), (3, 0, 0), (1, 4, 0)] := by
  unfold primitives
  rw [resetCode_denote]
  rfl

/-- A short or empty hash family still receives its replacement. -/
example : values (.inr ()) (reset 1 100 (1, (4 : F), 0) tape) =
    [(2 : F), (3 : F), (4 : F)] := rfl

example : reset 1 0 (1, (4 : F), 0) [(0, (2 : F), 0)] = [(0, 2, 0), (1, 4, 0)] := rfl

private def afterHash : Program CryptoOp TaggedEffect [] (.pair scalar (boundedNat 1)) :=
  .bind (.query (.scalar true) .unit)
    (.bind (.query (.uniform 1) .unit)
      (.ret (.pair (.var (.there .here)) (.var .here))))

private def cache : cacheStore.Value (cryptoBase F F F Unit Unit) := ((1, 2), [], [])

/-- The compiled program reads its private bit after the forked challenge. -/
example : (fun p => (p.1.value, p.2.1)) <$>
    ((afterHash.inline routines).run primitives (Machine.effects sampling machineStore) ()).run
      (cache, tape) = pure (((2 : F), (1 : Fin 2)), cache) := by
  refine (program_seeded PrimitiveCosts.unit sampling afterHash () cache tape).trans ?_
  rfl

/-- Seed generation samples in order and retains a nonempty ambient store. -/
example : (fun p => (p.1.value, p.2)) <$>
    ((generateCode .nat (fun _ => 2) [.inl (.inl 1)]).run primitives
      (Machine.effects sampling .nat) ()).run 37 = (do
      let x ← (liftM (unifSpec.query 1) : ProbComp (Fin 2))
      let y ← (liftM (unifSpec.query 1) : ProbComp (Fin 2))
      pure ([(3, (0 : F), x.val), (3, (0 : F), y.val)], 37)) := by
  unfold primitives
  rw [generateCode_erase]
  simp [generate, replicate, samples, encodeReply]

/-- Duplicate family entries each receive their full capacity. -/
example : seedLength (fun _ => 2) [.inr (), .inl (.inl 1000), .inr ()] = 6 := rfl

example : ∀ xs ∈ support (generate (F := F) (fun _ => 2) [.inr (), .inr ()]),
    (toSeed xs (.inr ())).length = 4 := by
  intro xs hxs
  have hseed : toSeed xs ∈ support (generateSeed (replaySpec F) (fun _ => 2) [.inr (), .inr ()]) := by
    rw [← toSeed_generate (F := F), support_map]
    exact ⟨xs, hxs, rfl⟩
  simpa using (length_eq_of_mem_support_generateSeed (replaySpec F) (fun _ => 2)
    [.inr (), .inr ()] (toSeed xs) (.inr ()) hseed)

/-- Empty setup still pays for its return and leaves the store intact. -/
example : ((generateCode .nat (fun _ => 1000) []).run primitives
    (Machine.effects sampling .nat) ()).run 37 = pure (⟨[], 2⟩, 37) := rfl

/-- In the second compiled execution that private bit stays fixed. -/
example : (fun p => (p.1.value, p.2.1)) <$>
    ((afterHash.inline routines).run primitives (Machine.effects sampling machineStore) ()).run
      (cache, reset 1 0 (1, (4 : F), 0) tape) = pure (((4 : F), (1 : Fin 2)), cache) := by
  refine (program_seeded PrimitiveCosts.unit sampling afterHash () cache
    (reset 1 0 (1, (4 : F), 0) tape)).trans ?_
  rfl

end SignaturesTest.SeedTape

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``popCode_denote, ``popCode_steps, ``oracle_refines, ``simulate_refines,
      ``draw_bound, ``draw_erase, ``handler_scalar_bound, ``handler_uniform_bound,
      ``program_typed, ``program_seeded, ``samples_expand, ``passCode_seeded, ``passCode_trace,
      ``toSeed_reset, ``resetCode_denote, ``resetCode_steps, ``reset_length,
      ``encodedTable_erase, ``encodedTable_bound, ``generateCode_bound,
      ``toSeed_generate, ``generateCode_seed, ``simulation_bound, ``passCode_bound] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"

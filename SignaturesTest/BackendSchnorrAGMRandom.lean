import Signatures.Runtime.BackendSchnorrAGMRandomBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMRandom

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))

-- Nonempty group lists mark malformed but retain the actual uniform query.
-- Cache contents, chronological histories and the bad flag all survive.
example (rows : List (List F)) :
    (Random.code rep data cost primitive ports).denote
      ([1, 1], rows, 10, [((7, 1), (0, true, 1, 0))], [(1, 0), (0, 1)], [8], false, true) =
    (fun r : Fin 11 => ((r.val, []), [((7, 1), (0, true, 1, 0))], [(1, 0), (0, 1)], [8], true, true)) <$>
      (unifSpec.query 10 : ProbComp (Fin 11)) := by
  rw [Random.denote]
  rfl

-- Empty groups preserve a preexisting malformed flag, regardless of rows.
-- The dependent oracle index is selected at runtime, with no range enumeration.
example (n : Nat) :
    (Random.code rep data cost primitive ports).denote
      ([], [[], [3, 5], [1]], n, [], [], [7, 7], true, false) =
    (fun r : Fin (n + 1) => ((r.val, []), [], [], [7, 7], true, false)) <$>
      (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  rw [Random.denote]
  rfl

-- The singleton randomness domain is valid even on a malformed request; its
-- query is retained rather than replaced by a rejection path.
example :
    (Random.code rep data cost primitive ports).denote
      ([2], [], 0, [], [], [], false, false) =
    (fun r : Fin 1 => ((r.val, []), [], [], [], true, false)) <$>
      (unifSpec.query 0 : ProbComp (Fin 1)) := by
  rw [Random.denote]
  rfl

-- A large arity is an input value, never an array of stored sampler programs.
example : (UniformSampling.code rep.data ports).denote (2 ^ 128) =
    Fin.val <$> (unifSpec.query (2 ^ 128) : ProbComp (Fin (2 ^ 128 + 1))) :=
  UniformSampling.denote rep.data ports _

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``UniformSampling.denote, ``UniformSampling.description, ``UniformSampling.bound,
      ``Random.prepareExpression_value, ``Random.wrapExpression_value, ``Random.denote,
      ``Random.source, ``Random.description, ``Random.marked_property, ``Random.prepare_property,
      ``Random.wrap_property, ``Random.input_size, ``Random.prepared_size, ``Random.output_size,
      ``Random.prepare_cost, ``Random.wrap_cost, ``Random.bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``UniformSampling.code, ``UniformSampling.bound, ``Random.code, ``Random.source, ``Random.bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``UniformSampling.code, ``Random.code, ``Random.prepare, ``Random.wrap,
            ``Random.randomTime, ``Random.prepareTime, ``ListEmpty.scan, ``ListEmpty.scanTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes a completed component's efficiency"

end SignaturesTest.BackendSchnorrAGMRandom

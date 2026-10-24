import Proofs.Runtime.BackendSchnorrAGMSigningBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMSigning

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
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

-- Distinct c,z values check draw order, response arithmetic and affine signs.
example : (Signing.sampledCode rep data cost primitive (iface := iface)).denote
    ((3, 5), 1, 2, 7, [], [(1, 0), (0, 1)], [9], false, true) =
    pure ((6, 5), [((7, 6), (3, false, 0, 0))], [(1, 0), (0, 1), (5, 4)], [9, 7], false, true) := by
  rw [Signing.sampledCode_denote]
  rfl

-- A signing collision keeps a cached zero and its first explanation, including
-- shadowed duplicates. Both histories still append at the chronological end.
example : (Signing.sampledCode rep data cost primitive (iface := iface)).denote
    ((3, 5), 1, 2, 7, [((7, 6), (0, true, 1, 0)), ((7, 6), (4, false, 6, 5))],
      [(1, 0), (0, 1), (1, 0)], [7], true, false) =
    pure ((6, 5), [((7, 6), (0, true, 1, 0)), ((7, 6), (4, false, 6, 5))],
      [(1, 0), (0, 1), (1, 0), (5, 4)], [7, 7], true, false) := by
  rw [Signing.sampledCode_denote]
  rfl

-- The complete sampled path creates the challenge and histories, even when
-- the input already carries a malformed flag. The source keeps that flag.
example (hs : sampler.denote () = pure (2 : F)) :
    (Signing.code rep data cost primitive sampler).denote
      (1, 2, 7, [], [], [], true, false) =
    pure ((5, 2), [((7, 5), (2, false, 0, 0))], [(2, 5)], [7], true, false) := by
  rw [Signing.denote, hs]
  simp only [pure_bind]
  rfl

-- Sampling precedes cache programming: the exact query tree always contains
-- both scalar draws, even for a cache containing every possible commitment.
example (xs : List ((Nat × F) × EncodedEntry F)) :
    (Signing.code rep data cost primitive sampler).denote
      (1, 2, 7, xs, [], [], false, false) = (do
        let c ← sampler.denote ()
        let z ← sampler.denote ()
        pure (Signing.signedValue ((c, z), 1, 2, 7, xs, [], [], false, false))) :=
  Signing.denote rep data cost primitive sampler _

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Signing.arithmeticExpression_value, ``Signing.historiesExpression_value,
      ``Signing.returnExpression_value, ``Signing.signedValue_source, ``Signing.sampledCode_denote,
      ``Signing.denote, ``Signing.source, ``Signing.description, ``Signing.history_size,
      ``Signing.state_size, ``Signing.input_size, ``Signing.sampled_size,
      ``Signing.arithmetic_property, ``Signing.histories_property, ``Signing.return_property,
      ``Signing.work_size, ``Signing.saved_size, ``Signing.programInput_size,
      ``Signing.programOutput_size, ``Signing.output_size, ``Signing.prepare_cost,
      ``Signing.histories_cost, ``Signing.finish_cost, ``Signing.sampled_bound, ``Signing.bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``Signing.code, ``Signing.source, ``Signing.sampled_bound, ``Signing.bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``Signing.code, ``Signing.sampledCode, ``Signing.prepare, ``Signing.histories,
            ``Signing.finish, ``Signing.signingTime, ``Signing.sampledTime, ``ListSnoc.expression,
            ``ListSnoc.snocTime, ``Programming.code, ``Programming.programmingTime, ``PairSampling.code] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes a completed component's efficiency"

end SignaturesTest.BackendSchnorrAGMSigning

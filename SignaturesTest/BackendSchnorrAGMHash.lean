import Signatures.Runtime.BackendSchnorrAGMHashBudget
import Signatures.Runtime.BackendListSingleton
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Schnorr.AGM
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMHash

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

-- Duplicate group values still give a malformed two-element request. An empty
-- inner coefficient vector is distinct from an empty list of vectors.
example : ListSingleton.value (0 : Nat) [] = (false, 0) := rfl
example : ListSingleton.value (0 : Nat) [7] = (true, 7) := rfl
example : (ListSingleton.value (0 : Nat) [7, 7]).1 = false := rfl
example : ListSingleton.value ([] : List Nat) [[]] = (true, []) := rfl
example : (ListSingleton.value ([] : List Nat) [[], []]).1 = false := rfl

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (sampler other : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

-- A late coefficient vector would make the denominator vanish, but a hit keeps
-- the first explanation and all histories, including the malformed flag.
example : (Hash.code rep data cost primitive sampler).denote
    ((7, 1), [0, 5], [((7, 1), (2, true, 1, 0))], [(1, 0), (0, 1)], [8], true, false) =
    pure (2, [((7, 1), (2, true, 1, 0))], [(1, 0), (0, 1)], [8], true, false) := by
  rw [Hash.denote, Read.denote, cacheAccess_denote]
  rfl

-- Costed execution includes coefficient processing on hits, but invokes no
-- scalar sampler, independently of how that sampler is implemented.
example (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (Hash.code rep data cost primitive sampler).run control queryCost
      ((7, 1), [0, 5], [((7, 1), (2, false, 0, 0))], [(1, 0), (0, 1)], [7], false, true) =
    (Hash.code rep data cost primitive other).run control queryCost
      ((7, 1), [0, 5], [((7, 1), (2, false, 0, 0))], [(1, 0), (0, 1)], [7], false, true) := by
  apply Hash.hit_run
  rfl

-- A miss records the affine pair computed before sampling, then sets bad when
-- secret coefficient five plus challenge two vanishes.
example (hs : sampler.denote () = pure (2 : F)) :
    (Hash.code rep data cost primitive sampler).denote
      ((7, 2), [3, 5], [], [(1, 0), (0, 1)], [8], false, false) =
    pure (2, [((7, 2), (2, true, 3, 5))], [(1, 0), (0, 1)], [8], false, true) := by
  rw [Hash.denote, Read.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap, hs, map_pure,
    freshValue, Read.returnValue]
  rfl

-- Inner vector length is not a handler shape check: the source zero-pads it.
example (hs : sampler.denote () = pure (2 : F)) :
    (Hash.code rep data cost primitive sampler).denote
      ((7, 2), [], [], [(1, 0), (0, 1)], [], false, false) =
    pure (2, [((7, 2), (2, true, 0, 0))], [(1, 0), (0, 1)], [], false, false) := by
  rw [Hash.denote, Read.denote, cacheAccess_denote]
  simp only [Hash.prepareValue, Read.packValue, Read.setupValue, cacheMap, hs, map_pure,
    freshValue, Read.returnValue]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Hash.prepareExpression_value, ``Hash.denote, ``Hash.source, ``Hash.hit_run,
      ``Hash.preserved_run, ``Hash.prepare_description, ``Hash.description, ``Hash.input_size,
      ``Hash.prepare_property, ``Hash.prepare_cost, ``Hash.prepare_bound, ``Hash.bound,
      ``Read.framed_cost, ``ListSingleton.valid_iff, ``ListSingleton.value_property,
      ``ListSingleton.scan_denote, ``ListSingleton.scan_cost, ``ListSingleton.output_size,
      ``ListSingleton.description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``Hash.code, ``Hash.source, ``Hash.bound, ``ListSingleton.scan_cost] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``Hash.code, ``Hash.hashTime, ``Hash.prepare,
            ``Read.code, ``Read.readTime, ``Flatten.code, ``Flatten.flattenTime,
            ``ListSingleton.scan, ``ListSingleton.scanTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes a completed component's efficiency"

end SignaturesTest.BackendSchnorrAGMHash

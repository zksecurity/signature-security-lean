import Signatures.Runtime.BackendListSnoc
import Signatures.Runtime.BackendSchnorrAGMProgramming
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMSigningStorage

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

-- Basis positions are chronological and repeated values occupy distinct slots.
example (cost : PrimitiveCosts) :
    (ListSnoc.expression (cell := affineTy) (Γ := [])).denote (arithmetic F F F Nat Nat cost)
      ((3, 4), [(1, 0), (0, 1), (1, 0)], ()) = [(1, 0), (0, 1), (1, 0), (3, 4)] := by
  rw [ListSnoc.denote]
  rfl

-- An empty history also appends correctly, with unrelated context retained.
example (cost : PrimitiveCosts) :
    (ListSnoc.expression (cell := message) (Γ := [.list message])).denote
      (arithmetic F F F Nat Nat cost) (7, [], [9, 10], ()) = [7] := by
  rw [ListSnoc.denote]
  rfl

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))

-- Cached zero is present: neither its challenge nor its explanation is replaced.
example : (Programming.code rep data cost primitive (iface := iface)).denote
    ((7, 1), (2, false, 0, 0), [((7, 1), (0, true, 3, 4))], ()) =
    pure [((7, 1), (0, true, 3, 4))] := by
  rw [Programming.denote]
  rfl

-- Shadowed duplicates are kept exactly, not deduplicated or reordered.
example : (Programming.code rep data cost primitive (iface := iface)).denote
    ((7, 1), (2, false, 0, 0), [((7, 1), (0, true, 3, 4)), ((7, 1), (5, false, 0, 0))], ()) =
    pure [((7, 1), (0, true, 3, 4)), ((7, 1), (5, false, 0, 0))] := by
  rw [Programming.denote]
  rfl

-- A fresh commitment gets the supplied signing challenge with no explanation.
example : (Programming.code rep data cost primitive (iface := iface)).denote
    ((7, 2), (2, false, 0, 0), [((7, 1), (0, true, 3, 4))], ()) =
    pure [((7, 2), (2, false, 0, 0)), ((7, 1), (0, true, 3, 4))] := by
  rw [Programming.denote]
  rfl

-- The actual costed program has no random-oracle call, for any input cache.
example (control : ControlCosts) (firstCosts secondCosts : (i : Nat) → unifSpec.Range i → Nat)
    (input : Env (cryptoBase F F F Nat Nat) [cacheKeyTy, entryTy, cacheTy]) :
    (Programming.code rep data cost primitive (iface := iface)).run control firstCosts input =
    (Programming.code rep data cost primitive (iface := iface)).run control secondCosts input := rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ListSnoc.denote, ``ListSnoc.expression_time, ``ListSnoc.cost, ``ListSnoc.description,
      ``CacheProgramming.denote, ``CacheProgramming.length, ``CacheProgramming.preserves,
      ``CacheProgramming.property, ``CacheProgramming.expression_time, ``CacheProgramming.cost,
      ``CacheProgramming.description, ``Programming.denote, ``Programming.source,
      ``Programming.description, ``Programming.bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``ListSnoc.cost, ``CacheProgramming.cost, ``Programming.code, ``Programming.source,
      ``Programming.bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``ListSnoc.expression, ``ListSnoc.snocTime, ``CacheProgramming.expression,
            ``CacheProgramming.programmingTime, ``Programming.code, ``Programming.programmingTime,
            ``comparison] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes a completed component's efficiency"

end SignaturesTest.BackendSchnorrAGMSigningStorage

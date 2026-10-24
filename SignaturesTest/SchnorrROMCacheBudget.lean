import Proofs.Runtime.BackendSchnorrROMLiveBudget
import Proofs.Runtime.BackendSchnorrROMProgrammingCost
import Proofs.Runtime.BackendSchnorrRawFork
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Executed native cache cases and resource-scope guards. Nat messages keep
the domain infinite; duplicate and zero entries exercise first-hit semantics.
Only the stateful scalar draw may supply a whole-code component budget. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrROMCacheBudget

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

private def advancingZero : Expr CryptoOp [.pair .unit .nat] (.pair scalar .nat) :=
  .pair (.op .zero .unit) (.op .natAdd (.pair (.snd (.var .here)) (.nat 1)))

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))

private def draw : Code Q unifSpec iface
    (StepClass.HasProd.prod rep.data.unit rep.data.nat)
    (StepClass.HasProd.prod (rep.ty scalar) rep.data.nat) :=
  .atomic (RawTape.NativeFork.compileLocal rep data cost primitive advancingZero)

/-- Both a point mismatch and a message mismatch are scanned before this miss;
one fresh zero is inserted and the sampler's state change is retained. -/
example :
    (ListROM.NativeCache.live rep data cost primitive rep.data.nat
      (draw (iface := iface) rep data cost primitive)).denote
      (((7, 1), 4, [((7, 2), 4), ((8, 1), 3)], ()), 9) =
      pure ((0, [((7, 1), 0), ((7, 2), 4), ((8, 1), 3)]), 10) := by
  rw [ListROM.NativeCache.live_denote]
  rfl

/-- A zero at the first matching entry wins over a shadowed nonzero duplicate. -/
example :
    (ListROM.NativeCache.live rep data cost primitive rep.data.nat
      (draw (iface := iface) rep data cost primitive)).denote
      (((7, 1), 4, [((8, 1), 3), ((7, 1), 0), ((7, 1), 2)], ()), 9) =
      pure ((0, [((8, 1), 3), ((7, 1), 0), ((7, 1), 2)]), 9) := by
  rw [ListROM.NativeCache.live_denote]
  rfl

/-- On that hit even the entire costed execution is independent of the draw
implementation, not just the returned challenge and cache. -/
example (other : Code Q unifSpec iface
    (StepClass.HasProd.prod rep.data.unit rep.data.nat)
    (StepClass.HasProd.prod (rep.ty scalar) rep.data.nat))
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat) :
    (ListROM.NativeCache.live rep data cost primitive rep.data.nat
      (draw (iface := iface) rep data cost primitive)).run control queryCost
      (((7, 1), 4, [((8, 1), 3), ((7, 1), 0), ((7, 1), 2)], ()), 9) =
    (ListROM.NativeCache.live rep data cost primitive rep.data.nat other).run control queryCost
      (((7, 1), 4, [((8, 1), 3), ((7, 1), 0), ((7, 1), 2)], ()), 9) := by
  exact ListROM.NativeCache.live_hit_run rep data cost primitive rep.data.nat (draw rep data cost primitive)
    other control queryCost (7, 1) 4 [((8, 1), 3), ((7, 1), 0), ((7, 1), 2)] 9 0 rfl

/-- Signing cache programming preserves the same first zero and both duplicates. -/
example :
    (Code.atomic (iface := iface) (Expression.compile rep data (arithmetic F F F Nat Nat cost)
      primitive (cacheProgram (val := scalar) hashEq))).denote
      ((7, 1), 4, [((7, 1), 0), ((7, 1), 2)], ()) =
      pure [((7, 1), 0), ((7, 1), 2)] := by
  rw [Code.denote, ListROM.NativeCache.programming_value cost]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LookupExprCompiler.body_time_bound, ``LookupExprCompiler.lookup_cost_bound,
      ``CacheCompiler.cacheGetExpr_bound, ``ListROM.NativeCache.hashEq_time,
      ``ListROM.NativeCache.scan_comparison_time, ``ListROM.NativeCache.lookup_cost,
      ``ListROM.NativeCache.live_bound, ``ListROM.NativeCache.liveTime_polynomial,
      ``CacheProgramming.withLookup_time_bound, ``ListROM.NativeCache.programming_property,
      ``ListROM.NativeCache.programming_cost, ``ListROM.NativeCache.programmingTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  forallTelescope (← getConstInfo ``ListROM.NativeCache.live_bound).type fun params conclusion => do
    unless conclusion.isAppOf ``Bounds do
      throwError "the complete live cache must have an actual native execution bound"
    let mut budgets := 0
    for param in params do
      let type ← inferType param
      if type.isAppOf ``Bounds then
        budgets := budgets + 1
        let mut drawBudget := false
        for arg in type.getAppArgs do
          if arg.isFVar then
            if (← getFVarLocalDecl arg).userName == `draw then
              drawBudget := true
        unless drawBudget do
          throwError "only the supplied stateful scalar draw may have a component budget"
    unless budgets == 1 do
      throwError "the live-cache theorem must account for exactly the actual scalar draw component"
  for name in #[``ListROM.NativeCache.live_bound, ``ListROM.NativeCache.lookup_cost,
      ``ListROM.NativeCache.programming_cost] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``Expression.compile, ``Expression.compileBound, ``Program,
            ``SourceCertificate, ``Fintype, ``Finite] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: derive lookup/comparison costs and do not require a finite domain or attacker source"

end SignaturesTest.SchnorrROMCacheBudget

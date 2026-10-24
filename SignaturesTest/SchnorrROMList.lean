import Proofs.Runtime.BackendSchnorrROMCache
import Proofs.Runtime.SchnorrROMListReduction
import Proofs.Runtime.SchnorrROMListGrowth
import Proofs.Runtime.BackendSchnorrRawFork
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! General ROM representation and executed native-cache regressions. Nat
messages exercise an infinite message domain. The sampler fixture changes its
state on every draw, exposing accidental draws and lost state threading. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrROMList

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

private def advancingZero : Expr CryptoOp [.pair .unit .nat] (.pair scalar .nat) :=
  .pair (.op .zero .unit) (.op .natAdd (.pair (.snd (.var .here)) (.nat 1)))

/-- Verification uses the live challenge even when signing programmed a
different value at the same point in the managed cache. -/
example :
    (ListROM.finalHash (F := F) (G₁ := F) (G₂ := F) (K := Nat) (7, 1)).run
      ((1, 2), [((7, 1), 4)], [((7, 1), 2)]) =
      pure (2, ((1, 2), [((7, 1), 4)], [((7, 1), 2)])) := by
  change simulateQ (Replay.expandPrivate privateImpl)
    ((taggedFinalHash.denote (arithmetic F F F Nat Nat PrimitiveCosts.unit) taggedSemantics
      ((7, 1), ())).run ((1, 2), [((7, 1), 4)], [((7, 1), 2)])) = _
  rw [taggedFinalHash_denote]
  rfl

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

/-- A managed hit wins even if the live cache holds a different challenge. -/
example :
    (ListROM.NativeCache.managed rep data cost primitive rep.data.nat (draw (iface := iface) rep data cost primitive)).denote
      (((7, 1), 0, [((7, 1), 4)], [((7, 1), 2)], ()), 9) =
      pure ((4, [((7, 1), 4)], [((7, 1), 2)]), 9) := by
  rw [ListROM.NativeCache.managed_denote]
  rfl

/-- A live hit fills a managed miss without executing the stateful sampler. -/
example :
    (ListROM.NativeCache.managed rep data cost primitive rep.data.nat (draw (iface := iface) rep data cost primitive)).denote
      (((7, 1), 0, [], [((7, 1), 2)], ()), 9) = pure ((2, [((7, 1), 2)], [((7, 1), 2)]), 9) := by
  rw [ListROM.NativeCache.managed_denote]
  simp only [cacheMap]
  rw [ListROM.NativeCache.live_denote]
  rfl

/-- A double miss draws exactly once and installs the same answer in both lists. -/
example :
    (ListROM.NativeCache.managed rep data cost primitive rep.data.nat (draw (iface := iface) rep data cost primitive)).denote
      (((7, 1), 4, [], [], ()), 9) = pure ((0, [((7, 1), 0)], [((7, 1), 0)]), 10) := by
  rw [ListROM.NativeCache.managed_denote]
  simp only [cacheMap]
  rw [ListROM.NativeCache.live_denote]
  rfl

/-- An existing zero is a hit, not the absent-entry fallback. -/
example :
    (ListROM.NativeCache.live rep data cost primitive rep.data.nat (draw (iface := iface) rep data cost primitive)).denote
      (((7, 1), 4, [((7, 1), 0)], ()), 9) = pure ((0, [((7, 1), 0)]), 9) := by
  rw [ListROM.NativeCache.live_denote]
  rfl

/-- A colliding signature preserves the first programmed value but still
executes both private draws in sequence. -/
example :
    (ListROM.NativeCache.signing rep data cost primitive rep.data.nat (draw (iface := iface) rep data cost primitive)).denote
      ((7, 1, 2, [((7, 0), 4)], ()), 9) = pure (((0, 0), [((7, 0), 4)]), 11) := by
  rw [ListROM.NativeCache.signing_denote]
  simp only [draw, Code.denote, advancingZero, Expr.denote, Var.get, arithmetic, pure_bind]
  norm_num
  rw [← Expr.run_value, cacheProgram_value _ _ (hashEq_value cost), lookupValue_cacheMap]
  rfl

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ListROM.handler_refines, ``ListROM.pass_refines, ``ListROM.pass_valid,
      ``ListROM.pass_trace, ``ListROM.handler_growth, ``ListROM.final_growth,
      ``ListROM.simulate_growth, ``ListROM.pass_growth, ``ListROM.pass_capacities,
      ``RawTape.fork_map, ``RawTape.fork_outputs, ``ListROM.fork_extract,
      ``ListROM.dlogReduction_eq_raw, ``ListROM.dlogReduction_eq_lazy, ``ListROM.security,
      ``ListROM.NativeCache.live_denote, ``ListROM.NativeCache.managed_denote,
      ``ListROM.NativeCache.signing_denote, ``ListROM.NativeCache.live_hit_run,
      ``ListROM.NativeCache.live_description, ``ListROM.NativeCache.managed_description,
      ``ListROM.NativeCache.signing_description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``ListROM.handler, ``ListROM.pass, ``ListROM.pass_trace, ``ListROM.pass_capacities,
      ``ListROM.dlogReduction, ``ListROM.dlogReduction_eq_lazy, ``ListROM.security] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        for forbidden in #[``SourceCertificate, ``Program] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: the attacker must not require arithmetic source syntax"
        if type.isAppOf ``Fintype || type.isAppOf ``Finite then
          let domain := type.getAppArgs[0]!
          if domain.isFVar && (← getFVarLocalDecl domain).userName == `M then
            throwError "{name}: no finite message domain may be required"
  for name in #[``ListROM.pass_trace, ``ListROM.fork_extract, ``ListROM.dlogReduction_eq_lazy] do
    forallTelescope (← getConstInfo name).type fun _ conclusion => do
      unless conclusion.isAppOf ``Eq do
        throwError "{name}: representation correspondence must preserve the complete computation"
  for name in #[``ListROM.NativeCache.live, ``ListROM.NativeCache.managed,
      ``ListROM.NativeCache.signing] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        if (← inferType param).isConstOf ``Nat then
          throwError "{name}: cache code must not enumerate capacities, arities or message domains"

end SignaturesTest.SchnorrROMList

import Signatures.Runtime.BackendSchnorrROMPrivateBudget
import Signatures.Runtime.BackendSchnorrRawFork
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Distinct sequential signing draws and resource-scope guards for complete
native cache/signing kernels, including the installed private sampler. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrROMKernelBudget

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

/-- The first call returns one; the next returns zero. Both advance the state. -/
private def advancingBit : Expr CryptoOp [.pair .unit .nat] (.pair scalar .nat) :=
  .pair
    (.branch (.op .natEq (.pair (.snd (.var .here)) (.nat 0)))
      (.op .one .unit) (.op .zero .unit))
    (.op .natAdd (.pair (.snd (.var .here)) (.nat 1)))

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
  .atomic (RawTape.NativeFork.compileLocal rep data cost primitive advancingBit)

/-- The response uses the second draw and the programmed challenge uses the
first. Reusing the initial sampler state or swapping draws changes this result. -/
example :
    (ListROM.NativeCache.signing rep data cost primitive rep.data.nat
      (draw (iface := iface) rep data cost primitive)).denote
      ((7, 1, 2, [], ()), 0) = pure (((3, 0), [((7, 3), 1)]), 2) := by
  rw [ListROM.NativeCache.signing_denote]
  simp only [draw, Code.denote, advancingBit, Expr.denote, Var.get, arithmetic, pure_bind]
  norm_num
  rw [← Expr.run_value, cacheProgram_value _ _ (hashEq_value cost), lookupValue_cacheMap]
  decide

/-- Collision preserves a prior zero and its shadowed duplicate, while both
different private draws still execute. -/
example :
    (ListROM.NativeCache.signing rep data cost primitive rep.data.nat
      (draw (iface := iface) rep data cost primitive)).denote
      ((7, 1, 2, [((7, 3), 0), ((7, 3), 4)], ()), 0) =
      pure (((3, 0), [((7, 3), 0), ((7, 3), 4)]), 2) := by
  rw [ListROM.NativeCache.signing_denote]
  simp only [draw, Code.denote, advancingBit, Expr.denote, Var.get, arithmetic, pure_bind]
  norm_num
  rw [← Expr.run_value, cacheProgram_value _ _ (hashEq_value cost), lookupValue_cacheMap]
  decide

end Execution

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ListROM.NativeCache.Parts.managedGet_eq, ``ListROM.NativeCache.Parts.signCached_eq,
      ``ListROM.NativeCache.Parts.commit_cost, ``ListROM.NativeCache.managed_bound,
      ``ListROM.NativeCache.managedTime_polynomial, ``ListROM.NativeCache.signing_bound,
      ``ListROM.NativeCache.signingTime_polynomial, ``ListROM.NativeCache.private_kernels_bound,
      ``ListROM.NativeCache.private_kernels_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for (name, expected) in #[(
      ``ListROM.NativeCache.managed_bound, 1), (``ListROM.NativeCache.signing_bound, 2)] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Bounds do
        throwError "{name}: require an actual full-kernel execution bound"
      let mut count := 0
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Bounds then
          count := count + 1
          let mut actualDraw := false
          for arg in type.getAppArgs do
            if arg.isFVar then
              if (← getFVarLocalDecl arg).userName == `draw then
                actualDraw := true
          unless actualDraw do
            throwError "{name}: only the actual stateful draw may supply a component budget"
      unless count == expected do
        throwError "{name}: account for every sequential draw with its own invariant transition"
  forallTelescope (← getConstInfo ``ListROM.NativeCache.private_kernels_bound).type fun params conclusion => do
    let mut profile := false
    for param in params do
      let type ← inferType param
      if (type.find? (fun e => e.isConstOf ``ExecutionProfile.Within)).isSome then
        profile := true
      for forbidden in #[``Bounds, ``Program, ``SourceCertificate, ``Fintype, ``Finite,
          ``Expression.compile, ``Expression.compileBound] do
        if (type.find? (fun e => e.isConstOf forbidden)).isSome then
          throwError "derive installed-kernel budgets from original sampler profiles and primitive laws"
    unless profile do
      throwError "measure the original sampler execution"
    let conclusion ← whnf conclusion
    unless conclusion.isAppOf ``And do
      throwError "certify all three installed kernels"
    let first := conclusion.getAppArgs[0]!
    let remaining := conclusion.getAppArgs[1]!
    unless first.isAppOf ``Bounds && remaining.isAppOf ``And do
      throwError "certify live access and both remaining kernels"
    unless remaining.getAppArgs[0]!.isAppOf ``Bounds && remaining.getAppArgs[1]!.isAppOf ``Bounds do
      throwError "certify managed access and complete signing"
    unless (conclusion.find? (fun e => e.isConstOf ``RawTape.NativePrivate.code)).isSome do
      throwError "install the actual transformed sampler in the certified kernels"
  forallTelescope (← getConstInfo ``ListROM.NativeCache.private_kernels_polynomial).type fun params _ => do
    for param in params do
      let name := (← getFVarLocalDecl param).userName
      if #[`arityCap, `counter, `counterCap, `domainSize].contains name then
        throwError "polynomial kernel runtime must not require enumerating numeric arities, counters or message domains"

end SignaturesTest.SchnorrROMKernelBudget

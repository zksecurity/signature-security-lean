import Signatures.Runtime.BackendSchnorrNonzeroPassPolynomial
import Signatures.Runtime.BackendSchnorrNonzeroPassDescription
import Signatures.Runtime.BackendSchnorrRawFork
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Execute the installed three-draw signer on interleaved replay families and
guard source correspondence and resource derivation through dispatch, arbitrary
caller execution and the complete pass, from original resource bounds only. -/

open OracleComp OracleSpec PFunctor Lean Meta
open PFunctor.DynSystem.DynComputation
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrNonzeroPrivateSigning

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

section Execution

variable {C : StepClass} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass C} [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.IsDistributive]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F F F Nat Nat))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F F F Nat Nat cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : RawTape.NativePrivate.Ports (Q := Q) rep (iface := iface))

private def bitValue : Expr CryptoOp [.nat] scalar :=
  .branch (.op .natEq (.pair (.var .here) (.nat 0))) (.op .zero .unit) (.op .one .unit)

private def positiveValue : Expr CryptoOp [.nat] scalar :=
  .branch (.op .natEq (.pair (.var .here) (.nat 0))) (.op .one .unit)
    (.op .add (.pair (.op .one .unit) (.op .one .unit)))

private def fieldSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar) :=
  .seq (.atomic (data.nat 1)) (.seq (UniformSampling.code rep.data uniform)
    (.atomic (RawTape.NativeFork.compileLocal rep data cost primitive bitValue)))

private def nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar) :=
  .seq (.atomic (data.nat 2)) (.seq (UniformSampling.code rep.data uniform)
    (.atomic (RawTape.NativeFork.compileLocal rep data cost primitive positiveValue)))

private theorem replay (msg : Nat) (g pk : F) (cache : List ((Nat × F) × F)) :
    (NonzeroListROM.NativeSigning.code rep data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) (nonzeroSampler rep data cost primitive uniform)).denote
      ((msg, g, pk, cache, ()), [(3, 0, 0)], [(3, 0, 1), (1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)]) =
      let sig := if g - pk = 0 then ((2 : F) • g, (1 : F) + 2) else (g - pk, 1)
      pure ((sig, (cacheProgram (val := scalar) hashEq).denote (arithmetic F F F Nat Nat cost)
        ((msg, sig.1), 1, cache, ())), [(3, 0, 0)], [(1, 4, 0), (3, 0, 0)]) := by
  have first :
      (RawTape.NativePrivate.code rep data cost primitive uniform ports
        (fieldSampler rep data cost primitive uniform)).denote
        ((), [(3, 0, 0)], [(3, 0, 1), (1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)]) =
        pure (1, [(3, 0, 0)], [(1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)]) := by
    refine (RawTape.NativePrivate.source rep data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) ()
      (⟨[(3, 0, 0)], [(3, 0, 1), (1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)]⟩ : RawTape.State F)).trans ?_
    simp only [fieldSampler, Code.denote, UniformSampling.denote]
    rfl
  have second :
      (RawTape.NativePrivate.code rep data cost primitive uniform ports
        (fieldSampler rep data cost primitive uniform)).denote
        ((), [(3, 0, 0)], [(1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)]) =
        pure (1, [(3, 0, 0)], [(1, 4, 0), (4, 0, 1), (3, 0, 0)]) := by
    refine (RawTape.NativePrivate.source rep data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) ()
      (⟨[(3, 0, 0)], [(1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)]⟩ : RawTape.State F)).trans ?_
    simp only [fieldSampler, Code.denote, UniformSampling.denote]
    rfl
  have third :
      (RawTape.NativePrivate.code rep data cost primitive uniform ports
        (nonzeroSampler rep data cost primitive uniform)).denote
        ((), [(3, 0, 0)], [(1, 4, 0), (4, 0, 1), (3, 0, 0)]) =
        pure (2, [(3, 0, 0)], [(1, 4, 0), (3, 0, 0)]) := by
    refine (RawTape.NativePrivate.source rep data cost primitive uniform ports
      (nonzeroSampler rep data cost primitive uniform) ()
      (⟨[(3, 0, 0)], [(1, 4, 0), (4, 0, 1), (3, 0, 0)]⟩ : RawTape.State F)).trans ?_
    simp only [nonzeroSampler, Code.denote, UniformSampling.denote]
    rfl
  unfold NonzeroListROM.NativeSigning.code
  rw [NonzeroSigning.Native.code_denote, first, pure_bind, second, pure_bind, third, pure_bind]
  simp only [one_smul]

-- Repair uses the distinct third family; both caches keep their earlier values.
example :
    (NonzeroListROM.NativeComponents.signing rep data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) (nonzeroSampler rep data cost primitive uniform)).denote
      (7, (((1, 1), [((7, 2), 3)], [((7, 2), 4)]),
        [(3, 0, 0)], [(3, 0, 1), (1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)])) =
      pure ((2, 3), (((1, 1), [((7, 2), 3)], [((7, 2), 4)]),
        [(3, 0, 0)], [(1, 4, 0), (3, 0, 0)])) := by
  rw [NonzeroListROM.NativeComponents.signing_denote, replay, map_pure]
  norm_num
  rw [ListROM.NativeCache.programming_value (F := F) (G₁ := F) (G₂ := F) (K := Nat) (M := Nat) cost]
  rfl

-- The third draw still executes when repair is unnecessary; the live cache is untouched.
example :
    (NonzeroListROM.NativeComponents.signing rep data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) (nonzeroSampler rep data cost primitive uniform)).denote
      (7, (((1, 0), [], [((7, 2), 4)]),
        [(3, 0, 0)], [(3, 0, 1), (1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)])) =
      pure ((1, 1), (((1, 0), [((7, 1), 1)], [((7, 2), 4)]),
        [(3, 0, 0)], [(1, 4, 0), (3, 0, 0)])) := by
  rw [NonzeroListROM.NativeComponents.signing_denote, replay, map_pure]
  norm_num
  rw [ListROM.NativeCache.programming_value (F := F) (G₁ := F) (G₂ := F) (K := Nat) (M := Nat) cost]
  rfl

variable {Input Output : Type}
  (bd : Boundary C (ListROM.NativeInterface.sourceSpec F F Nat).toPFunctor Input Output)
  (handlerPorts : ListROM.NativeInterface.Ports (Q := Q) rep bd)

-- The actual indexed dispatcher selects the nonzero repair signer and tags its reply.
example :
    (NonzeroListROM.NativeHandler.code rep bd handlerPorts data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) (nonzeroSampler rep data cost primitive uniform)).denote
      (.inr 7, (((1, 1), [((7, 2), 3)], [((7, 2), 4)]),
        [(3, 0, 0)], [(3, 0, 1), (1, 4, 0), (4, 0, 1), (3, 0, 1), (3, 0, 0)])) =
      pure ((⟨.inr 7, (2, 3)⟩ : ListROM.NativeInterface.Response F F Nat),
        (((1, 1), [((7, 2), 3)], [((7, 2), 4)]), [(3, 0, 0)], [(1, 4, 0), (3, 0, 0)])) := by
  simp only [NonzeroListROM.NativeHandler.code, ListROM.NativeHandler.codeWithSigning,
    ListROM.NativeHandler.dispatchWithSigning, Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
  rw [ListROM.NativeHandler.tagged_denote, NonzeroListROM.NativeComponents.signing_denote,
    replay, map_pure, map_pure]
  norm_num
  rw [ListROM.NativeCache.programming_value (F := F) (G₁ := F) (G₂ := F) (K := Nat) (M := Nat) cost]
  rfl

-- A random request still decodes malformed raw replies and leaves unrelated families intact.
example :
    (NonzeroListROM.NativeHandler.code rep bd handlerPorts data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) (nonzeroSampler rep data cost primitive uniform)).denote
      (.inl (.inl 2), ((1, 2), [((7, 3), 0)], [((7, 3), 4)]),
        [(3, 0, 1)], [(1, 4, 0), (4, 0, 8), (3, 0, 0)]) =
      pure ((⟨.inl (.inl 2), (2 : Fin 3)⟩ : ListROM.NativeInterface.Response F F Nat),
        ((1, 2), [((7, 3), 0)], [((7, 3), 4)]), [(3, 0, 1)], [(1, 4, 0), (3, 0, 0)]) := by
  simp only [NonzeroListROM.NativeHandler.code, ListROM.NativeHandler.codeWithSigning,
    ListROM.NativeHandler.dispatchWithSigning, ListROM.NativeHandler.inner,
    Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
  rw [ListROM.NativeHandler.random, ListROM.NativeHandler.tagged_denote, ListROM.NativeComponents.random_denote]
  have hd : (RawTape.NativeUniform.code rep data cost primitive uniform).denote
      (2, [(3, 0, 1)], [(1, 4, 0), (4, 0, 8), (3, 0, 0)]) =
      pure (8, [(3, 0, 1)], [(1, 4, 0), (3, 0, 0)]) :=
    RawTape.NativeUniform.denote rep data cost primitive uniform 2
      (⟨[(3, 0, 1)], [(1, 4, 0), (4, 0, 8), (3, 0, 0)]⟩ : RawTape.State F)
  rw [hd]
  rfl

-- Hashing uses the managed cached value, even if live state and replay disagree.
example :
    (NonzeroListROM.NativeHandler.code rep bd handlerPorts data cost primitive uniform ports
      (fieldSampler rep data cost primitive uniform) (nonzeroSampler rep data cost primitive uniform)).denote
      (.inl (.inr (7, 3)), ((1, 2), [((7, 3), 0)], [((7, 3), 2)]), [], [(1, 4, 0)]) =
      pure ((⟨.inl (.inr (7, 3)), (0 : F)⟩ : ListROM.NativeInterface.Response F F Nat),
        ((1, 2), [((7, 3), 0)], [((7, 3), 2)]), [], [(1, 4, 0)]) := by
  simp only [NonzeroListROM.NativeHandler.code, ListROM.NativeHandler.codeWithSigning,
    ListROM.NativeHandler.dispatchWithSigning, ListROM.NativeHandler.inner,
    Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
  rw [ListROM.NativeHandler.hash, ListROM.NativeHandler.tagged_denote,
    ListROM.NativeComponents.hash_denote, ListROM.NativeCache.managed_denote]
  simp only [cacheMap, ↓reduceIte, map_pure]
  rfl

end Execution

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``NonzeroListROM.NativeSigning.sampler_source, ``NonzeroListROM.NativeSigning.code_source,
      ``NonzeroListROM.NativeSigning.code_description, ``NonzeroListROM.NativeSigning.code_bound,
      ``NonzeroListROM.NativeSigning.runtimeBound_polynomial, ``NonzeroListROM.NativeSigning.codeDescription_polynomial,
      ``NonzeroListROM.NativeSigning.code_description_of_inputs, ``ListROM.NativeComponents.signing_wrap_bound,
      ``NonzeroListROM.NativeComponents.signing_denote, ``NonzeroListROM.NativeComponents.signing_source,
      ``NonzeroListROM.NativeComponents.signing_description, ``NonzeroListROM.NativeComponents.signing_bound,
      ``NonzeroListROM.NativeComponents.signingTime_polynomial, ``NonzeroListROM.NativeComponents.signingDescription_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for (name, program) in #[(
      ``NonzeroListROM.NativeSigning.code_bound, ``NonzeroListROM.NativeSigning.code),
      (``NonzeroListROM.NativeComponents.signing_bound, ``NonzeroListROM.NativeComponents.signing)] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Bounds && (conclusion.find? (fun e => e.isConstOf program)).isSome do
        throwError "Require the actual installed program's complete execution bound"
      let mut profiles := #[]
      for param in params do
        let type ← inferType param
        if (type.find? (fun e => e.isConstOf ``ExecutionProfile.Within)).isSome then
          profiles := profiles.push (← getFVarLocalDecl param).userName
        for forbidden in #[``Bounds, ``Program, ``SourceCertificate, ``Finite, ``Fintype,
            ``Expression.compile, ``Expression.compileBound, ``NonzeroListROM.NativeSigning.runtimeBound,
            ``NonzeroListROM.NativeComponents.signingTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: derive transformed costs from original profiles, without domain/syntax restrictions"
      unless profiles == #[`fieldProfile, `nonzeroProfile] do
        throwError "Keep distinct execution profiles for both original samplers"
  for name in #[``NonzeroListROM.NativeSigning.runtimeBound_polynomial,
      ``NonzeroListROM.NativeSigning.codeDescription_polynomial,
      ``NonzeroListROM.NativeComponents.signingTime_polynomial,
      ``NonzeroListROM.NativeComponents.signingDescription_polynomial] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``PolynomiallyBounded do
        throwError "Require polynomial closure of the actual resource formula"
      for param in params do
        if #[`counter, `arityCap, `domainSize].contains (← getFVarLocalDecl param).userName then
          throwError "Do not require polynomial numerical arities, counters or message universes"
  let .defnInfo impl ← getConstInfo ``NonzeroListROM.NativeSigning.code
    | throwError "The installed signer must remain an actual code definition"
  lambdaTelescope impl.value fun params body => do
    for wanted in #[`fieldSampler, `nonzeroSampler] do
      let mut found := false
      for param in params do
        if (← getFVarLocalDecl param).userName == wanted then
          found := (body.find? (fun e => e.isAppOf ``RawTape.NativePrivate.code &&
            e.getAppArgs.contains param)).isSome
      unless found do
        throwError "Install both original samplers in the private replay handler"
    if (body.find? (fun e => e.isConstOf ``ListROM.NativeDraw.challenge)).isSome then
      throwError "Signing must not consume challenge-family cells"

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ListROM.NativeHandler.codeWithSigning_bound_of_components,
      ``NonzeroListROM.NativeHandler.code_denote, ``NonzeroListROM.NativeHandler.code_executed_run,
      ``NonzeroListROM.NativeHandler.executed_erase, ``NonzeroListROM.NativeHandler.caller_source_of_resources,
      ``NonzeroListROM.NativeHandler.caller_no_cutoff_of_resources,
      ``NonzeroListROM.NativeHandler.code_description, ``NonzeroListROM.NativeHandler.caller_description,
      ``NonzeroListROM.NativeHandler.code_bound, ``NonzeroListROM.NativeHandler.code_bound_reserved,
      ``NonzeroListROM.NativeHandler.timeBudget_polynomial, ``NonzeroListROM.NativeHandler.caller_bound,
      ``NonzeroListROM.NativeHandler.caller_bound_of_resources,
      ``NonzeroListROM.NativeHandler.callerResourcesTime_polynomial,
      ``NonzeroListROM.NativeHandler.caller_output_size_of_resources,
      ``NonzeroListROM.NativePass.source_of_resources, ``NonzeroListROM.NativePass.completed_of_resources,
      ``NonzeroListROM.NativePass.code_bound_of_resources, ``NonzeroListROM.NativePass.code_description,
      ``NonzeroListROM.NativePass.resourcesTime_polynomial] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for (name, program) in #[(
      ``NonzeroListROM.NativeHandler.code_bound, ``NonzeroListROM.NativeHandler.code),
      (``NonzeroListROM.NativeHandler.code_bound_reserved, ``NonzeroListROM.NativeHandler.code),
      (``NonzeroListROM.NativeHandler.caller_bound_of_resources, ``NonzeroListROM.NativeHandler.caller),
      (``NonzeroListROM.NativePass.code_bound_of_resources, ``NonzeroListROM.NativePass.code)] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      let mut profiles := #[]
      let mut measured := false
      let mut actual := (conclusion.find? (fun e => e.isConstOf program)).isSome
      let mut nonzeroQueries := none
      for param in params do
        let type ← inferType param
        let userName := (← getFVarLocalDecl param).userName
        if (type.find? (fun e => e.isConstOf ``ExecutionProfile.Within)).isSome then
          profiles := profiles.push userName
        if (type.find? (fun e => e.isConstOf ``QuantitativeRealization.RunsWithin)).isSome then
          measured := true
        if userName == `nonzeroQueries then
          nonzeroQueries := some param
        actual := actual || (type.find? (fun e => e.isConstOf program)).isSome
        for forbidden in #[``Bounds, ``Program, ``SourceCertificate, ``Finite, ``Fintype,
            ``Expression.compile, ``Expression.compileBound, ``NonzeroListROM.NativeHandler.timeBudget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: derive complete runtime from original caller/sampler/primitive resources"
      unless profiles == #[`fieldProfile, `nonzeroProfile] && actual do
        throwError "{name}: require the actual program and exactly both original sampler profiles"
      if name == ``NonzeroListROM.NativeHandler.caller_bound_of_resources ||
          name == ``NonzeroListROM.NativePass.code_bound_of_resources then
        unless measured do
          throwError "{name}: recover attacker invariants from measured arbitrary execution"
      if name == ``NonzeroListROM.NativeHandler.code_bound_reserved ||
          name == ``NonzeroListROM.NativeHandler.caller_bound_of_resources then
        let some count := nonzeroQueries | throwError "Missing original nonzero query count"
        let some reserve := conclusion.find? (fun e => e.isAppOf ``ListROM.NativeHandler.ReservedState)
          | throwError "Preserve future-call reservations"
        let args := reserve.getAppArgs
        unless (args[args.size - 3]!.find? (fun e => e == count)).isSome do
          throwError "Reserve the extra nonzero draw on every adaptive request"
  for (name, source) in #[(
      ``NonzeroListROM.NativeHandler.code_denote, ``NonzeroListROM.NativeHandler.source),
      (``NonzeroListROM.NativeHandler.caller_source_of_resources, ``NonzeroListROM.handler),
      (``NonzeroListROM.NativePass.source_of_resources, ``NonzeroListROM.pass)] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``Eq && (conclusion.find? (fun e => e.isConstOf source)).isSome do
        throwError "{name}: preserve complete nonzero source computation equality"
      for param in params do
        let type ← inferType param
        for forbidden in #[``Bounds, ``Program, ``SourceCertificate, ``Finite, ``Fintype] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: no finite universe or restricted-attacker syntax premise"
        if #[`arityCap, `counterCap, `domainSize, `valid].contains (← getFVarLocalDecl param).userName then
          throwError "{name}: cover every raw tape and dynamic sampling arity"
  for name in #[``NonzeroListROM.NativeHandler.timeBudget_polynomial,
      ``NonzeroListROM.NativeHandler.callerResourcesTime_polynomial,
      ``NonzeroListROM.NativePass.resourcesTime_polynomial] do
    forallTelescope (← getConstInfo name).type fun params conclusion => do
      unless conclusion.isAppOf ``PolynomiallyBounded do
        throwError "Require polynomial closure of the actual composed resource formula"
      for param in params do
        let type ← inferType param
        if #[`counter, `arityCap, `domainSize].contains (← getFVarLocalDecl param).userName then
          throwError "No polynomial numerical arity, loop count or universe assumption"
        for forbidden in #[``NonzeroListROM.NativeHandler.timeBudget,
            ``NonzeroListROM.NativeComponents.signingTime, ``ListROM.NativePass.timeBudget] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "Derive polynomial complete time from original resources"
  for (name, required) in #[(
      ``NonzeroListROM.NativeHandler.code, ``NonzeroListROM.NativeComponents.signing),
      (``NonzeroListROM.NativePass.code, ``NonzeroListROM.NativeHandler.caller)] do
    let .defnInfo impl ← getConstInfo name | throwError "Expected actual code definition"
    unless (impl.value.find? (fun e => e.isConstOf required)).isSome do
      throwError "{name}: install the actual nonzero implementation"
    for forbidden in #[``ListROM.NativeComponents.signing, ``ListROM.NativeHandler.caller] do
      if (impl.value.find? (fun e => e.isConstOf forbidden)).isSome then
        throwError "Do not silently substitute the full-field signer/caller"

end SignaturesTest.SchnorrNonzeroPrivateSigning

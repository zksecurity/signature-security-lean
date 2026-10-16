import Signatures.Runtime.BackendSchnorrNonzeroComponentsPolynomial
import Signatures.Runtime.BackendSchnorrRawFork
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Execute the installed three-draw signer on interleaved replay families and
guard resource derivation from the original sampler programs only. -/

open OracleComp OracleSpec PFunctor Lean Meta
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

end SignaturesTest.SchnorrNonzeroPrivateSigning

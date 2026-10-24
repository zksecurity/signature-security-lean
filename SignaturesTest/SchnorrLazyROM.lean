import Proofs.Schnorr.LazyROM
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Check the named lazy Schnorr probability endpoint, including a duplicate
proof cover, adaptive private randomness, and the original arbitrary-message
scope. These checks do not claim native runtime or encoded-memory bounds. -/

open OracleComp OracleSpec

namespace SignaturesTest.SchnorrLazyROM

private abbrev Spec := Schnorr.FixedTape.Spec (Fin 2)

noncomputable local instance : IsUniformSpec (Unit →ₒ Fin 2) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable local instance : IsUniformMeasureSpec Spec :=
  OracleSpec.instIsUniformMeasureSpecOfIsUniformSpec

private def afterChallenge (challenge : Fin 2) : OracleComp Spec (Fin 2 × Nat) := do
  if challenge = 0 then
    let bit : Fin 2 ← Spec.query (.inl 1)
    pure (challenge, bit.val)
  else
    let trit : Fin 3 ← Spec.query (.inl 2)
    pure (challenge, trit.val)

private def adaptive : OracleComp Spec (Fin 2 × Nat) :=
  Spec.query (.inr ()) >>= afterChallenge

private theorem adaptive_bound : IsPerIndexQueryBound adaptive
    (Schnorr.FixedTape.finiteBounds [1, 1, 2] 1 1) := by
  simp only [adaptive, isPerIndexQueryBound_query_bind_iff]
  constructor
  · decide
  · intro challenge
    by_cases h : challenge = (0 : Fin 2) <;>
      simp [afterChallenge, h, Schnorr.FixedTape.finiteBounds, Function.update]

private theorem adaptive_reachable : PathCfReachable adaptive
    (FiatShamir.nmaForkBudget 0) (.inr ()) (fun _ => some (0 : Fin 1)) := by
  intro path slot selected
  have hslot : slot = 0 := (Option.some.inj selected).symm
  subst slot
  rcases path with ⟨challenge, suffix⟩
  change (PFunctor.FreeM.Cursor.locateAt? (P := Spec.toPFunctor) (.inr ())
    (PFunctor.FreeM.liftBind (.inr ()) afterChallenge) ⟨challenge, suffix⟩ 0).isSome
  rfl

/-- The challenge may send replay into a private sampling family absent from
the first execution. Duplicate proof-cover entries do not change the bound. -/
example : 𝒟[Schnorr.LazyROM.fork adaptive 0 (fun _ => some (0 : Fin 1))] =
    𝒟[Schnorr.FixedTape.completeFork adaptive [1, 1, 2].dedup 1 0
      (fun _ => some (0 : Fin 1))] :=
  Schnorr.LazyROM.fork_eq_complete adaptive [1, 1, 2] 1 0
    (fun _ => some 0) adaptive_bound adaptive_reachable

/-- Interpreting private draws and challenges preserves their joint native law. -/
example : 𝒟[simulateQ Schnorr.LazyROM.sample adaptive] = 𝒟[adaptive] :=
  Schnorr.LazyROM.sample_measure adaptive

section DerivedCover

private abbrev F := ZMod 5
private abbrev Messages := Nat → Bool

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable local instance : SampleableType F := SampleableType.ofFintype _

noncomputable local instance : DecidableEq Messages := Classical.decEq _

/-- Even with no hash/sign calls, this attacker has adaptive private sampling
at large arities and an uncountable message type. No syntax certificate or
private-family list is supplied to the security theorem. -/
private noncomputable def privateOnly :
    Schnorr.ROM.Adversary (F := F) (M := Messages) (1 : F) where
  main _ := do
    let branch : Fin 2 ← (Schnorr.ROM.advSpec F F Messages).query (.inl (.inl 1))
    let value : Fin (1000000 + branch.val + 1) ←
      (Schnorr.ROM.advSpec F F Messages).query (.inl (.inl (1000000 + branch.val)))
    pure ((fun n => decide (n = value.val)), (0, 0))

private theorem privateOnly_queries (pk : F) :
    FiatShamir.signHashQueryBound (M := Messages) (oa := privateOnly.main pk) 0 0 := by
  simp [FiatShamir.signHashQueryBound, privateOnly]

/-- The appended verifier lookup is still the sole hash slot. -/
example (pk : F) : IsQueryBoundP (Schnorr.LazyROM.main 1 pk privateOnly)
    (· = Sum.inr ()) 1 :=
  Schnorr.LazyROM.main_hashBound 1 pk privateOnly 0 0 privateOnly_queries

example :
    let eps := 𝒟[Schnorr.ROM.game 1 privateOnly] {true} -
      (0 : ENNReal) * (0 + 0) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (0 + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[DiffieHellman.dlogExperiment 1 (Schnorr.LazyROM.dlogReduction 1 privateOnly 0)] {true} := by
  have generates : Function.Bijective (fun x : F => x • (1 : F)) := by
    constructor
    · intro x y same
      simpa only [smul_eq_mul, mul_one] using same
    · intro y
      exact ⟨y, by simp⟩
  simpa only [Nat.cast_zero] using
    Schnorr.LazyROM.security 1 generates privateOnly 0 0 privateOnly_queries

end DerivedCover

open Lean Meta in
run_meta do
  let endpoints := #[``Schnorr.LazyROM.fork_eq_complete,
    ``Schnorr.LazyROM.sample_measure, ``Schnorr.LazyROM.dlogReduction_eq_fixed,
    ``Schnorr.LazyROM.dlogExperiment_eq_fixed, ``Schnorr.LazyROM.security_of_seed_bound,
    ``Schnorr.LazyROM.security, ``Schnorr.LazyROM.main_hashBound,
    ``Schnorr.LazyROM.exists_seed_bound,
    ``Signatures.Runtime.FiniteQueryCover.replace_bound,
    ``Signatures.Runtime.FiniteQueryCover.exists_bound,
    ``Signatures.Runtime.FiniteQueryCover.exists_bound_family]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in endpoints do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
    let type := (← getConstInfo name).type
    if (type.find? (fun e => e.isConstOf ``instEvalDistSemanticsOfMonadLiftTSPMF)).isSome then
      throwError "{name}: statement must use native measure semantics"
    forallTelescope type fun params _ => do
      for param in params do
        let declaration ← getFVarLocalDecl param
        if declaration.userName == `M then
          for premise in params do
            let premiseType ← inferType premise
            if (premiseType.isAppOf ``Finite || premiseType.isAppOf ``Fintype ||
                premiseType.isAppOf ``Countable) &&
                (premiseType.find? (fun e => e == param)).isSome then
              throwError "{name}: must not restrict the message universe"
  let securityType := (← getConstInfo ``Schnorr.LazyROM.security).type
  for forbidden in #[``OracleComp.IsPerIndexQueryBound, ``Schnorr.FixedTape.finiteBounds,
      `Proofs.Runtime.Program] do
    if (securityType.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "lazy security must derive its seed cover without a source-language premise"
  for required in #[``Schnorr.ROM.game, ``Schnorr.LazyROM.dlogReduction,
      ``DiffieHellman.dlogExperiment] do
    unless (securityType.find? (fun e => e.isConstOf required)).isSome do
      throwError "lazy security must connect the original game to the named reduction"
  for name in #[``Schnorr.LazyROM.dlogReduction, ``Schnorr.LazyROM.security] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let declaration ← getFVarLocalDecl param
        if #[`privateFamilies, `qR, `bound].contains declaration.userName then
          throwError "{name}: must not take a proof-only seed cover"

end SignaturesTest.SchnorrLazyROM

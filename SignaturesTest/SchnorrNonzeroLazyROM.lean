import Signatures.Schnorr.Proofs.NonzeroLazyROM
import Signatures.Model.NonzeroFieldGrowth
import Signatures.Runtime.BackendSchnorrNonzeroSigningSource
import Signatures.Runtime.BackendSchnorrNonzeroRepairCost
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Guard the nonzero lazy probability endpoint and its new signing kernel.
These tests do not assert completion of the whole reduction's native budget. -/

open OracleComp OracleSpec Lean Meta
open Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrNonzeroLazyROM

private abbrev F := ZMod 5
private abbrev Messages := Nat → Bool
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
noncomputable local instance : SampleableType F := SampleableType.ofFintype _
noncomputable local instance : SampleableType Fˣ := SampleableType.ofFintype _
noncomputable local instance : DecidableEq Messages := Classical.decEq _

private noncomputable def privateOnly :
    Schnorr.NonzeroNonce.Adversary (F := F) (M := Messages) (1 : F) where
  main _ := do
    let branch : Fin 2 ← (Schnorr.ROM.advSpec F F Messages).query (.inl (.inl 1))
    let value : Fin (1000000 + branch.val + 1) ←
      (Schnorr.ROM.advSpec F F Messages).query (.inl (.inl (1000000 + branch.val)))
    pure ((fun n => decide (n = value.val)), (0, 0))

private theorem privateOnly_queries (pk : F) :
    FiatShamir.signHashQueryBound (M := Messages) (oa := privateOnly.main pk) 0 0 := by
  simp [FiatShamir.signHashQueryBound, privateOnly]

-- An uncountable message universe and adaptive private sampling need no cover.
example (pk : F) : IsQueryBoundP (Schnorr.NonzeroNonce.LazyROM.main 1 pk privateOnly)
    (· = Sum.inr ()) 1 :=
  Schnorr.NonzeroNonce.LazyROM.main_hashBound 1 pk privateOnly 0 0 privateOnly_queries

example :
    let eps := 𝒟[Schnorr.NonzeroNonce.game 1 privateOnly] {true} -
      (0 : ENNReal) * (0 + 0) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹
    eps * (eps / (0 + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[DiffieHellman.dlogExperiment 1 (Schnorr.NonzeroNonce.LazyROM.dlogReduction 1 privateOnly 0)] {true} := by
  simpa only [Nat.cast_zero] using
    Schnorr.NonzeroNonce.LazyROM.security 1 (by simp) privateOnly 0 0 privateOnly_queries

-- The generic algorithm specializes definitionally to the existing full-field one.
example (adv : Schnorr.ROM.Adversary (F := F) (M := Messages) (1 : F)) (qH : Nat) :
    Schnorr.LazyROM.dlogReduction 1 adv qH = fun _ pk =>
      FiatShamir.LazyTape.reduction (Schnorr.sigma F F 1) (DiffieHellman.dlogGenerable F 1)
        Messages (Schnorr.simTranscript F F 1) adv qH pk := rfl

private def recorded (c z a : F) :
    SemanticsM (cryptoBase F F F Nat Nat) NonzeroSigning.Native.Draw (StateM (List Bool)) :=
  fun instr _ log => match instr with
  | .field => (if log.isEmpty then c else z, log ++ [false])
  | .nonzero => (a, log ++ [true])

private def runSigning (c z a pk : F) (cache : List ((Nat × F) × F)) :
    ((F × F) × List ((Nat × F) × F)) × List Bool :=
  ((NonzeroSigning.body NonzeroSigning.Native.Draw.field NonzeroSigning.Native.Draw.nonzero).denote
    (arithmetic F F F Nat Nat PrimitiveCosts.unit) (recorded c z a) (7, 1, pk, cache, ())).run []

-- Identity commitment: repair both signature and programmed target.
example : runSigning 2 4 1 2 [] = (((1, 0), [((7, 1), 2)]), [false, false, true]) := by decide
-- Nonidentity commitment: retain the original response, but still consume the third draw.
example : runSigning 2 1 1 2 [] = (((2, 1), [((7, 2), 2)]), [false, false, true]) := by decide
-- A collision preserves the earlier challenge, even when it disagrees with this signature.
example : runSigning 2 4 1 2 [((7, 1), 3)] =
    (((1, 0), [((7, 1), 3)]), [false, false, true]) := by decide
-- A zero public key uses exactly the same finite repair routine.
example : runSigning 2 0 1 0 [] = (((1, 1), [((7, 1), 2)]), [false, false, true]) := by decide

run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``FiatShamir.LazyTape.main_hashBound, ``FiatShamir.LazyTape.exists_seed_bound,
      ``FiatShamir.LazyTape.reduction_eq_fixed, ``FiatShamir.LazyTape.experiment_eq_fixed,
      ``FiatShamir.LazyTape.security, ``Schnorr.NonzeroNonce.LazyROM.main_hashBound,
      ``Schnorr.NonzeroNonce.LazyROM.experiment_eq, ``Schnorr.NonzeroNonce.LazyROM.security,
      ``NonzeroSigning.repair_denote, ``NonzeroSigning.body_denote, ``NonzeroSigning.body_source,
      ``NonzeroSigning.Native.code_denote, ``NonzeroSigning.Native.code_source, ``NonzeroSigning.Native.code_description,
      ``NonzeroSigning.Native.codeDescription_polynomial, ``NonzeroSigning.Native.repair_expression_time,
      ``NonzeroSigning.Native.repair_output_size, ``NonzeroSigning.Native.repairTime_polynomial,
      ``Model.inv_pred_le_twice_inv, ``Model.negligible_inv_pred, ``Model.negligible_inv_card_sub_one] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  let security := (← getConstInfo ``Schnorr.NonzeroNonce.LazyROM.security).type
  for forbidden in #[``IsPerIndexQueryBound, ``Schnorr.FixedTape.finiteBounds, ``Program,
      ``Schnorr.NonzeroNonce.dlogReduction, ``Schnorr.LazyROM.dlogReduction] do
    if (security.find? (fun e => e.isConstOf forbidden)).isSome then
      throwError "Nonzero lazy security must not substitute the older solver, full-field solver or seed cover"
  for required in #[``Schnorr.NonzeroNonce.game, ``Schnorr.NonzeroNonce.LazyROM.dlogReduction,
      ``DiffieHellman.dlogExperiment] do
    unless (security.find? (fun e => e.isConstOf required)).isSome do
      throwError "Keep the nonzero game and actual lazy reduction visible"
  unless (security.find? (fun e => e.isAppOfArity ``HSub.hSub 6 &&
      e.getAppArgs[0]!.isConstOf ``Nat && e.getAppArgs[4]!.isAppOf ``Fintype.card)).isSome do
    throwError "Keep the nonzero signing denominator as cardinality minus one"
  for name in #[``Schnorr.NonzeroNonce.LazyROM.security, ``Schnorr.NonzeroNonce.LazyROM.dlogReduction] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let declaration ← getFVarLocalDecl param
        if #[`privateFamilies, `qR, `bound, `hseed].contains declaration.userName then
          throwError "{name}: proof-only seed input"
        if #[`M, `G].contains declaration.userName then
          for premise in params do
            let type ← inferType premise
            if (type.isAppOf ``Finite || type.isAppOf ``Fintype || type.isAppOf ``Countable) &&
                (type.find? (fun e => e == param)).isSome then
              throwError "{name}: finite message/group premise"

end SignaturesTest.SchnorrNonzeroLazyROM

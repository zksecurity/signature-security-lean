import Proofs.Model.LazyAGM
import AlgebraicGroupModel.Interaction

/-! The signature adapter preserves source interactions and the full winning experiment. -/

open OracleComp OracleSpec Model.LazyAGM

namespace SignaturesTest.AlgebraicSignatureAdapter

private def adaptive : Adversary Nat Nat Nat Nat Nat where
  main _ := do
    let _ ← (liftM ((advSpec Nat Nat Nat).query (.inl (.inl 1))) :
      OracleComp (advSpec Nat Nat Nat) _)
    let H ← (liftM ((advSpec Nat Nat Nat).query (.inl (.inr 3))) :
      OracleComp (advSpec Nat Nat Nat) Nat)
    let s ← (liftM ((advSpec Nat Nat Nat).query (.inr (H + 1))) :
      OracleComp (advSpec Nat Nat Nat) Nat)
    let target ← (liftM ((advSpec Nat Nat Nat).query (.inl (.inr s))) :
      OracleComp (advSpec Nat Nat Nat) Nat)
    let _ ← (liftM ((advSpec Nat Nat Nat).query (.inl (.inr 3))) :
      OracleComp (advSpec Nat Nat Nat) Nat)
    pure ⟨target, 2, [3, 5], [7]⟩

private def execution :
    (AlgebraicGroupModel.Interaction.Explained Nat (Interactive.Result Nat Nat) (Interactive.Group Nat Nat) ×
      AlgebraicGroupModel.Interaction.Groups (Interactive.Group Nat Nat)) ×
      List (Interactive.Query Nat Nat) :=
  (adaptive.toInteractive.run
    (Interactive.impl
      (N := StateM (List (Interactive.Query Nat Nat))) (fun n => do
        modify (fun log : List (Interactive.Query Nat Nat) => log ++ [Sum.inl (Sum.inl n)])
        pure ⟨0, Nat.zero_lt_succ n⟩)
      (fun i => do
        modify (fun log : List (Interactive.Query Nat Nat) => log ++ [Sum.inl (Sum.inr i)])
        pure (i + 7))
      (fun m => do
        modify (fun log : List (Interactive.Query Nat Nat) => log ++ [Sum.inr m])
        pure (m + 100))) (Interactive.initialInput 2 42)).run []

-- The real certified runner tracks chronology, not hash/sign channel order.
example : execution.1.2 .signature = [2, 10, 111, 118, 10] := by decide
example : execution.1.1.coefficients .signature = [[2, 3, 7, 5, 0]] := by decide
example : execution.1.1.value.groups .signature = [1401] := by decide
example : execution.1.1.value.data.map (fun z => (z.1.mstar, z.2)) =
    some (118, [11]) := by decide
example : execution.2 =
    [.inl (.inl 1), .inl (.inr 3), .inr 11, .inl (.inr 111), .inl (.inr 3)] := by decide

-- The public key is tracked in its own sort, never mixed into signature coefficients.
example : execution.1.2 .verification = [42] := by decide
example : execution.1.1.value.groups .verification = [] := by decide
example : execution.1.1.coefficients .verification = [] := by decide
example : (Interactive.initialInput 2 42).data = () := rfl

-- Missing group replies are rejected, not silently invented or put in plain data.
private def missingReply :
    QueryImpl (AlgebraicGroupModel.Interaction.plainSpec (Interactive.Group Nat Nat)
      (Interactive.Query Nat Nat) Interactive.Reply) Id := fun ⟨q, _⟩ =>
  match q with
  | .inl (.inl n) => pure ⟨⟨0, Nat.zero_lt_succ n⟩, fun _ => []⟩
  | .inl (.inr _) => pure ⟨(), fun _ => []⟩
  | .inr _ => pure ⟨(), fun _ => []⟩

example : (adaptive.toInteractive.run missingReply (Interactive.initialInput 2 42)).1.value.data.isNone = true := by
  decide

-- Both initial lists must have the expected shape; a key is never recovered from data.
example : (adaptive.toInteractive.run missingReply
    ⟨(), Interactive.groupLists [2] ([] : List Nat)⟩).1.value.data = none := by decide
example : (adaptive.toInteractive.run missingReply
    ⟨(), Interactive.groupLists [2] [42, 43]⟩).1.value.data = none := by decide
example : (adaptive.toInteractive.run missingReply
    ⟨(), Interactive.groupLists ([] : List Nat) [42]⟩).1.value.data = none := by decide
example : (adaptive.toInteractive.run missingReply
    ⟨(), Interactive.groupLists [2, 3] [42]⟩).1.value.data = none := by decide

-- The adversary reads the tracked key and may use it when choosing scalar coefficients.
private def keyAware : Adversary Nat Nat Unit Nat Nat where
  main pk := pure ⟨(), pk, [], []⟩

example : (keyAware.toInteractive.run (Interactive.impl (N := Id)
    (fun _ => pure 0) (fun _ => pure 0) (fun _ => pure 0))
      (Interactive.initialInput 2 5)).1.value.groups .signature = [10] := by decide

-- Different carrier types prevent accidentally treating the key as a signature-group input.
private def distinctGroups : Adversary Nat Nat Unit Nat Int where
  main pk := pure ⟨(), pk.natAbs, [], []⟩

example : (distinctGroups.toInteractive.run (Interactive.impl (N := Id)
    (fun _ => pure 0) (fun _ => pure 0) (fun _ => pure 0))
      (Interactive.initialInput 2 (-5 : Int))).2 .verification = [-5] := by decide
example : (distinctGroups.toInteractive.run (Interactive.impl (N := Id)
    (fun _ => pure 0) (fun _ => pure 0) (fun _ => pure 0))
      (Interactive.initialInput 2 (-5 : Int))).1.value.groups .signature = [10] := by decide

-- The actual game entry point is definitionally connected to the certified runner.
example {F I M G₁ G₂ : Type} [Field F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    (terms : M → List (I × F)) (a : F) (A : Adversary F I M G₁ G₂)
    (g : G₁) (pk : G₂) :
    interactiveRun terms a A g pk = (fun z => z.1.value) <$>
      A.toInteractive.run (Interactive.impl
        (fun n => (liftM ((baseSpec I G₁).query (.inl n)) : OracleComp (baseSpec I G₁) _))
        (fun i => (liftM ((baseSpec I G₁).query (.inr i)) : OracleComp (baseSpec I G₁) G₁))
        (signing terms a)) (Interactive.initialInput g pk) := rfl

-- The existing signature output acquires exact-length interactive witnesses without changing it.
example {F I M G : Type} [Zero F] [AddCommMonoid G] [SMul F G]
    (g : G) (out : Output F M) (tr : Transcript I M G) :
    (out.toAlgebraic.explain (tr.inputs g)).value = ⟨out.mstar, fun _ => [materialize g out tr]⟩ := by
  rw [AlgebraicGroupModel.Output.explain_value]
  rfl

example {F I M G : Type} [Zero F] [AddCommMonoid G] [SMul F G]
    (g : G) (out : Output F M) (tr : Transcript I M G) :
    (out.toAlgebraic.explain (tr.inputs g)).Valid (fun _ => (tr.inputs g).map Prod.snd) :=
  AlgebraicGroupModel.Output.explain_valid _ _

-- Repeated query labels still get distinct positional tokens; channels cannot alias.
example : Transcript.inputs 1 (([(false, 2), (false, 2)], [(false, 2)]) :
    Transcript Bool Bool Nat) =
      [(.inl (), 1), (.inr (.inl 0), 2), (.inr (.inl 1), 2), (.inr (.inr 0), 2)] := rfl

-- Extra coefficients in one channel do not leak into another channel.
example : materialize 1 (⟨(), 2, [3, 999], [5]⟩ : Output Nat Unit)
    ([(false, 7)], [((), 11)]) = 78 := by decide

example : materialize 1 (⟨(), 2, [], [5]⟩ : Output Nat Unit)
    ([(false, 7)], [((), 11)]) = 57 := by decide

-- Exact computation equality to the pre-separation experiment, not only an event implication.
example {F I M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    (terms : M → List (I × F)) (admissible : M → List M → Prop)
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F I M G₁ G₂) :
    experiment (Gₜ := Gₜ) terms admissible g₁ g₂ A = (by
      classical
      exact do
        let α ← (liftM ($ᵗ F) : OracleComp (baseSpec I G₁) F)
        let (out, tr) ← run terms α A (α • g₂)
        let σ := out.β • g₁ + weightedReplies out.γ tr.1 + weightedReplies out.ξ tr.2
        let target ← evalTerms (terms out.mstar)
        pure (decide (admissible out.mstar (tr.2.map Prod.fst) ∧
          BilinearGroup.pairing (F := F) (Gₜ := Gₜ) σ g₂ =
            BilinearGroup.pairing (F := F) (Gₜ := Gₜ) target (α • g₂) ∧
          out.mstar ∉ tr.2.map Prod.fst))) := by
  rw [experiment_eq]
  apply bind_congr
  intro α
  apply bind_congr
  rintro ⟨out, tr⟩
  apply bind_congr
  intro target
  apply congrArg (pure : Bool → OracleComp (baseSpec I G₁) Bool)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, materialize_eq_weightedReplies]

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``AlgebraicGroupModel.Output.explain_valid,
      ``AlgebraicGroupModel.Output.explain_value, ``Interactive.compile_algebraic, ``Interactive.compile_run,
      ``Adversary.toInteractive_run, ``interactiveRun_eq, ``experiment_eq] do
    for axiomName in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"

end SignaturesTest.AlgebraicSignatureAdapter

import Signatures.Runtime.SeedTapeMachine
import Signatures.Runtime.ProgramSimulation

/-! The compiled machine realizes the typed seeded semantics, including both
cache state and remaining seed. This is equality of oracle computations. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr.SeedTape

private theorem state_pure {m : Type → Type} [Monad m] {S A : Type} (a : A) (s : S) :
    (pure a : StateT S m A) s = pure (a, s) := rfl

private theorem state_bind {m : Type → Type} [Monad m] {S A B : Type}
    (x : StateT S m A) (k : A → StateT S m B) (s : S) :
    (x >>= k) s = (x s >>= fun p => k p.1 p.2) := rfl

private theorem state_map {m : Type → Type} [Monad m] [LawfulMonad m] {S A B : Type}
    (f : A → B) (x : StateT S m A) (s : S) :
    (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s := StateT.run_map _ _ _

variable {F S : Type} [SampleableType F]

/-- Interpret typed randomness using encoded seeds, then lower primitive samples.
The state reassociation is proof-side bookkeeping for the product-store code. -/
def execute [Zero F] : StateT S (OracleComp (replaySpec F)) →ᵐ StateT (S × List (TapeCell F)) ProbComp where
  toFun {_} main s := (fun p => (p.1.1, (p.1.2, p.2))) <$>
    simulateQ samples ((simulateQ oracle (main.run s.1)).run s.2)
  toFun_pure' x := by
    funext s
    simp [StateT.run, state_pure]
  toFun_bind' main next := by
    funext s
    simp only [StateT.run, state_bind, simulateQ_bind, map_bind, bind_map_left]

variable {G₁ G₂ K M : Type} [Field F]

set_option backward.isDefEq.respectTransparency false in
theorem execute_tagged {a b} (cmd : TaggedEffect a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    execute (taggedSemantics cmd arg) = (semantics cmd arg :
      StateT (machineStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp (b.Value (cryptoBase F G₁ G₂ K M))) := by
  funext s
  rcases s with ⟨cache, tape⟩
  cases cmd with
  | read => cases arg; simp [execute, taggedSemantics, semantics, StateT.run, state_pure]
  | write => simp [execute, taggedSemantics, semantics, StateT.run, state_pure]
  | scalar live =>
      cases arg
      cases live <;> simp [execute, taggedSemantics, semantics,
        StateT.run, state_map, Functor.map_map]
  | uniform n =>
      cases arg
      simp [execute, taggedSemantics, semantics, StateT.run, state_map, Functor.map_map]

variable [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem program_typed (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Program CryptoOp TaggedEffect Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    Run.value <$> (code.inline routines).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling machineStore) env =
      execute (code.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics env) := by
  rw [program_erase, Program.denote_mmap]
  apply congrArg (fun H : SemanticsM (cryptoBase F G₁ G₂ K M) TaggedEffect
    (StateT (machineStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp) =>
      code.denote (arithmetic F G₁ G₂ K M cost) H env)
  funext a b cmd arg
  exact (execute_tagged cmd arg).symm

/-- Discarding only the consumed tape leaves exactly the typed seeded run's
returned value and cache, with all primitive sampling expanded identically. -/
theorem program_seeded (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Program CryptoOp TaggedEffect Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F)) :
    (fun p => (p.1.value, p.2.1)) <$>
        ((code.inline routines).run (arithmetic F G₁ G₂ K M cost)
          (Machine.effects sampling machineStore) env).run (cache, tape) =
      simulateQ samples ((simulateQ seededOracle
        ((code.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics env).run cache)).run'
          (toSeed tape)) := by
  have h := congrArg (fun action => (fun p => (p.1, p.2.1)) <$> action.run (cache, tape))
    (program_typed cost sampling code env)
  rw [← run'_eq _ tape]
  simp only [execute, StateT.run, state_map, Functor.map_map, StateT.run', simulateQ_map] at h ⊢
  convert h using 1

end Signatures.Runtime.Schnorr.SeedTape

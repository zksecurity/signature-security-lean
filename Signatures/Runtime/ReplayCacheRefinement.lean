import Signatures.Runtime.EncodedReplay
import Signatures.Runtime.SchnorrReplayPass

/-! The combined state machine refines indexed replay of the cache interpreter.
This identifies its random transcript with the one used by the semantic fork theorem. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

section Generic

variable {F A B S : Type} [Zero F] [SampleableType F]

private theorem state_pure {m : Type → Type} [Monad m] (x : A) (s : S) :
    (pure x : StateT S m A) s = pure (x, s) := rfl

private theorem state_bind {m : Type → Type} [Monad m] (main : StateT S m A)
    (next : A → StateT S m B) (s : S) :
    (main >>= next) s = (main s >>= fun p => next p.1 p.2) := rfl

private theorem state_map {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (main : StateT S m A)
    (s : S) : (f <$> main) s = (fun p => (f p.1, p.2)) <$> main s :=
  StateT.run_map _ _ _

noncomputable def sampleReplay : QueryImpl (replaySpec F) ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr ()) => $ᵗ F
  | .inr () => $ᵗ F

noncomputable def liftCacheReplay (main : StateT S (OracleComp (replaySpec F)) A) :
    StateT (S × TapeState F) ProbComp A := fun s =>
  (fun p => (p.1.1, (p.1.2, p.2))) <$>
    simulateQ sampleReplay (indexedRun (main s.1) s.2)

theorem liftCacheReplay_pure (x : A) :
    liftCacheReplay (pure x : StateT S (OracleComp (replaySpec F)) A) = pure x := by
  funext s
  simp [liftCacheReplay, indexedRun_pure, state_pure]

theorem liftCacheReplay_bind (main : StateT S (OracleComp (replaySpec F)) A)
    (next : A → StateT S (OracleComp (replaySpec F)) B) :
    liftCacheReplay (main >>= next) =
      (liftCacheReplay main >>= fun x => liftCacheReplay (next x)) := by
  funext s
  change (fun p => (p.1.1, (p.1.2, p.2))) <$>
      simulateQ sampleReplay (indexedRun (main s.1 >>= fun p => next p.1 p.2) s.2) = _
  rw [indexedRun_bind]
  simp [state_bind, liftCacheReplay, map_bind, bind_map_left]

private theorem liftCacheReplay_repeat (step : A → StateT S (OracleComp (replaySpec F)) A)
    (n : Nat) (x : A) :
    liftCacheReplay (repeatDenote step n x) =
      repeatDenote (fun x => liftCacheReplay (step x)) n x := by
  induction n generalizing x with
  | zero => exact liftCacheReplay_pure x
  | succ n ih => simp [repeatDenote, liftCacheReplay_bind, ih]

end Generic

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]

theorem liftCacheReplay_tagged {a b} (cmd : TaggedEffect a b)
    (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    liftCacheReplay (taggedSemantics cmd arg) = replaySemantics cmd arg := by
  funext s
  rcases s with ⟨cache, cursor, limit, tape, events⟩
  cases cmd with
  | read => cases arg; simp [taggedSemantics, liftCacheReplay, indexedRun_pure, replaySemantics]
  | write => simp [taggedSemantics, liftCacheReplay, indexedRun_pure, replaySemantics]
  | scalar tag =>
    cases arg
    cases tag <;> by_cases h : cursor < limit <;>
      simp [taggedSemantics, liftCacheReplay, indexedRun, indexedTapeImpl,
        replaySemantics, sampleReplay, encodeReply, decodeReply, h, state_map,
        StateT.run, simulateQ_map, Functor.map_map]
  | uniform n =>
    cases arg
    by_cases h : cursor < limit <;>
      simp [taggedSemantics, liftCacheReplay, indexedRun, indexedTapeImpl,
        replaySemantics, sampleReplay, encodeReply, decodeReply, h, state_map,
        StateT.run, simulateQ_map, Functor.map_map]

variable [DecidableEq F] [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem replayProgram_indexed (cost : PrimitiveCosts) {Γ a}
    (code : Program CryptoOp TaggedEffect Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    code.denote (arithmetic F G₁ G₂ K M cost) replaySemantics env =
      liftCacheReplay (code.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics env) := by
  induction code with
  | ret e => exact (liftCacheReplay_pure _).symm
  | query cmd arg => exact (liftCacheReplay_tagged cmd _).symm
  | bind first next ih ihnext =>
    simp only [Program.denote, liftCacheReplay_bind, ih, ihnext]
  | branch cond yes no ihyes ihno =>
    simp only [Program.denote]
    split <;> first | exact ihyes env | exact ihno env
  | loop count init body ih =>
    simp only [Program.denote, liftCacheReplay_repeat]
    congr 1
    funext x
    exact ih (x, env)
  | call body args ih => exact ih (args.denote _ env)

/-- The complete macro pass includes the final live query even if the source never
queried its forged commitment. The cache is returned by the state transformer. -/
def macroPass (cost : PrimitiveCosts) {Γ} (randomBound : Nat)
    (source : Program CryptoOp (Command randomBound) Γ forgery)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (replaySpec F))
      (observedForgery.Value (cryptoBase F G₁ G₂ K M)) := do
  let forged ← (source.inline (taggedRoutines randomBound)).denote
    (arithmetic F G₁ G₂ K M cost) taggedSemantics env
  let challenge ← taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics
    ((forged.1, forged.2.1), ())
  pure (forged, challenge)

end Signatures.Runtime.Schnorr

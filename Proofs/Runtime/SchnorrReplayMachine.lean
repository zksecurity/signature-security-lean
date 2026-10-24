import Proofs.Runtime.SchnorrTagged
import Proofs.Runtime.MixedReplay

/-! Compiling tagged Schnorr effects into one closed machine store. Cache operations
own the first field, while mixed replay owns the second; the adapters charge every
projection, update, and procedure frame. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

abbrev replayStore : Ty CryptoAtom := .pair cacheStore Replay.Mixed.store

def replayRoutines {a b} : TaggedEffect a b → Program CryptoOp (Machine.Effect replayStore) [a] b
  | .scalar tag => (Replay.Mixed.scalarDraw tag).inline
      (Machine.secondStore cacheStore Replay.Mixed.store)
  | .uniform n => (Replay.Mixed.uniformDraw n).inline
      (Machine.secondStore cacheStore Replay.Mixed.store)
  | .read => Machine.firstStore cacheStore Replay.Mixed.store .read
  | .write => Machine.firstStore cacheStore Replay.Mixed.store .write

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

noncomputable def replayHandler (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) :
    HandlerM (cryptoBase F G₁ G₂ K M) TaggedEffect
      (StateT (replayStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp) :=
  routineHandler (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling replayStore) replayRoutines

def scalarReplayPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) (length : Nat) : Nat :=
  Replay.Mixed.drawBound cost (sampling.scalar + 5) 3 6 length 10 14 + 3

def uniformReplayPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (length n : Nat) : Nat :=
  Replay.Mixed.drawBound cost (sampling.uniform n + 5) (cost.natOp + 4)
    (n + cost.field + cost.natOp + 9) length 10 14 + 3

theorem replayHandler_scalar_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (tag : Bool) (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (out : Run F × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((replayHandler cost sampling (.scalar tag) ()).run
      (cache, cursor, limit, tape, events))) :
    out.1.steps ≤ scalarReplayPrice cost sampling tape.length ∧
      out.2 = (cache, cursor + 1, limit, tape,
        ((if tag then 1 else 0), out.1.value, 0) :: events) := by
  simp only [replayHandler, routineHandler, bind_pure_comp, StateT.run_map,
    support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  rw [replayRoutines, Machine.secondStore_run] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hb := Replay.Mixed.draw_bound cost (Machine.forwardedSampling sampling) 10 14
    .scalar Replay.Mixed.scalarDecode (Replay.Mixed.scalarEncode tag) ($ᵗ F)
    (sampling.scalar + 5) 3 6 (fun _ => rfl)
    (fun _ => le_of_eq (Replay.Mixed.scalarDecode_steps cost _))
    (Replay.Mixed.scalarEncode_steps cost tag) cursor limit tape events p hp
  refine ⟨by dsimp [scalarReplayPrice]; omega, ?_⟩
  rw [hb.2]
  rfl

theorem replayHandler_uniform_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (n : Nat) (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (cursor limit : Nat) (tape events : List (Nat × F × Nat))
    (out : Run (Fin (n + 1)) × replayStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((replayHandler cost sampling (.uniform n) ()).run
      (cache, cursor, limit, tape, events))) :
    out.1.steps ≤ uniformReplayPrice cost sampling tape.length n ∧
      out.2 = (cache, cursor + 1, limit, tape, (n + 2, 0, out.1.value.val) :: events) := by
  simp only [replayHandler, routineHandler, bind_pure_comp, StateT.run_map,
    support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  rw [replayRoutines, Machine.secondStore_run] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hb := Replay.Mixed.draw_bound cost (Machine.forwardedSampling sampling) 10 14
    (.uniform n) (Replay.Mixed.uniformDecode n) (Replay.Mixed.uniformEncode n)
    (liftM (unifSpec.query n)) (sampling.uniform n + 5)
    (cost.natOp + 4) (n + cost.field + cost.natOp + 9) (fun _ => rfl)
    (fun _ => le_of_eq (Replay.Mixed.uniformDecode_steps cost n _))
    (fun _ => le_of_eq (Replay.Mixed.uniformEncode_steps cost n _)) cursor limit tape events p hp
  refine ⟨by dsimp [uniformReplayPrice]; omega, ?_⟩
  rw [hb.2]
  rfl

theorem replayHandler_read (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (tape : Replay.Mixed.store.Value (cryptoBase F G₁ G₂ K M)) :
    (replayHandler cost sampling .read ()).run (cache, tape) = pure (⟨cache, 10⟩, (cache, tape)) := by
  exact (Machine.firstStore_refines cost sampling cacheStore Replay.Mixed.store tape
    .read () cache).symm

theorem replayHandler_write (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (before after : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (tape : Replay.Mixed.store.Value (cryptoBase F G₁ G₂ K M)) :
    (replayHandler cost sampling .write after).run (before, tape) =
      pure (⟨(), 14⟩, (after, tape)) := by
  exact (Machine.firstStore_refines cost sampling cacheStore Replay.Mixed.store tape
    .write after before).symm

end Signatures.Runtime.Schnorr

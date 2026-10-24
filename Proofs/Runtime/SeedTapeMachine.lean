import Proofs.Runtime.SeedTapeDraw
import Proofs.Runtime.SchnorrTagged

/-! The seeded Schnorr machine owns a cache and a finite family-indexed tape.
These adapters compile every tagged operation into primitive machine effects. -/

open OracleComp

namespace Signatures.Runtime.Schnorr.SeedTape

abbrev machineStore : Ty CryptoAtom := .pair cacheStore store

def routines {a b} : TaggedEffect a b → Program CryptoOp (Machine.Effect machineStore) [a] b
  | .scalar live => (scalarDraw live).inline (Machine.secondStore cacheStore store)
  | .uniform n => (uniformDraw n).inline (Machine.secondStore cacheStore store)
  | .read => Machine.firstStore cacheStore store .read
  | .write => Machine.firstStore cacheStore store .write

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

noncomputable def handler (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) :
    HandlerM (cryptoBase F G₁ G₂ K M) TaggedEffect
      (StateT (machineStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp) :=
  routineHandler (arithmetic F G₁ G₂ K M cost) (Machine.effects sampling machineStore) routines

def scalarPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) (length : Nat) : Nat :=
  drawBound cost 1 (sampling.scalar + 5) 3 length 10 14 + 3

def uniformPrice (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts) (length n : Nat) : Nat :=
  drawBound cost (n + 2) (sampling.uniform n + 5) (cost.natOp + 4) length 10 14 + 3

theorem handler_scalar_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (live : Bool) (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F))
    (out : Run F × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((handler cost sampling (.scalar live) ()).run (cache, tape))) :
    out.1.steps ≤ scalarPrice cost sampling tape.length ∧
      out.2.1 = cache ∧ out.2.2.length ≤ tape.length := by
  simp only [handler, routineHandler, bind_pure_comp, StateT.run_map,
    support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  rw [routines, Machine.secondStore_run] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hb := draw_bound cost (Machine.forwardedSampling sampling) 10 14
    (if live then 1 else 0) .scalar Replay.Mixed.scalarDecode ($ᵗ F)
    (sampling.scalar + 5) 3 (fun _ => rfl)
    (fun _ => le_of_eq (Replay.Mixed.scalarDecode_steps cost _)) tape p hp
  refine ⟨?_, rfl, hb.2⟩
  cases live <;> dsimp [scalarPrice, drawBound] at hb ⊢ <;> omega

theorem handler_uniform_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (n : Nat) (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F))
    (out : Run (Fin (n + 1)) × machineStore.Value (cryptoBase F G₁ G₂ K M))
    (hout : out ∈ support ((handler cost sampling (.uniform n) ()).run (cache, tape))) :
    out.1.steps ≤ uniformPrice cost sampling tape.length n ∧
      out.2.1 = cache ∧ out.2.2.length ≤ tape.length := by
  simp only [handler, routineHandler, bind_pure_comp, StateT.run_map,
    support_map, Set.mem_image] at hout
  obtain ⟨r, hr, rfl⟩ := hout
  rw [routines, Machine.secondStore_run] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hb := draw_bound cost (Machine.forwardedSampling sampling) 10 14
    (n + 2) (.uniform n) (Replay.Mixed.uniformDecode n) (liftM (unifSpec.query n))
    (sampling.uniform n + 5) (cost.natOp + 4) (fun _ => rfl)
    (fun _ => le_of_eq (Replay.Mixed.uniformDecode_steps cost n _)) tape p hp
  exact ⟨by dsimp [uniformPrice]; omega, rfl, hb.2⟩

theorem handler_read (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (cache : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F)) :
    (handler cost sampling .read ()).run (cache, tape) = pure (⟨cache, 10⟩, (cache, tape)) :=
  (Machine.firstStore_refines cost sampling cacheStore store tape .read () cache).symm

theorem handler_write (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (before after : cacheStore.Value (cryptoBase F G₁ G₂ K M)) (tape : List (TapeCell F)) :
    (handler cost sampling .write after).run (before, tape) = pure (⟨(), 14⟩, (after, tape)) :=
  (Machine.firstStore_refines cost sampling cacheStore store tape .write after before).symm

def semantics : SemanticsM (cryptoBase F G₁ G₂ K M) TaggedEffect
    (StateT (machineStore.Value (cryptoBase F G₁ G₂ K M)) ProbComp) := fun cmd arg s =>
  match cmd with
  | .read => pure (s.1, s)
  | .write => pure ((), (arg, s.2))
  | .scalar live => (fun p => (p.1, (s.1, p.2))) <$>
      simulateQ samples (if live then (oracle (.inr ())).run s.2
        else (oracle (.inl (.inr ()))).run s.2)
  | .uniform n => (fun p => (p.1, (s.1, p.2))) <$>
      simulateQ samples ((oracle (.inl (.inl n))).run s.2)

set_option backward.isDefEq.respectTransparency false in
theorem handler_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {a b} (cmd : TaggedEffect a b) (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    Run.value <$> handler cost sampling cmd arg = semantics cmd arg := by
  funext s
  rcases s with ⟨cache, tape⟩
  cases cmd with
  | read =>
    cases arg
    change (Run.value <$> handler cost sampling .read ()).run _ = _
    rw [StateT.run_map, handler_read]
    rfl
  | write =>
    change (Run.value <$> handler cost sampling .write arg).run _ = _
    rw [StateT.run_map, handler_write]
    rfl
  | scalar live =>
    cases arg
    change (Run.value <$> handler cost sampling (.scalar live) ()).run _ = _
    simp only [handler, routineHandler, bind_pure_comp, StateT.run_map, Functor.map_map]
    rw [routines, Machine.secondStore_run]
    have h := scalarDraw_erase (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost (Machine.forwardedSampling sampling) 10 14 live tape
    have hh := congrArg (Functor.map (fun p : F × List (TapeCell F) => (p.1, (cache, p.2)))) h
    simp only [Functor.map_map, semantics, StateT.run] at hh ⊢
    convert hh using 1
  | uniform n =>
    cases arg
    change (Run.value <$> handler cost sampling (.uniform n) ()).run _ = _
    simp only [handler, routineHandler, bind_pure_comp, StateT.run_map, Functor.map_map]
    rw [routines, Machine.secondStore_run]
    have h := uniformDraw_erase (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)
      cost (Machine.forwardedSampling sampling) 10 14 n tape
    have hh := congrArg (Functor.map
      (fun p : Fin (n + 1) × List (TapeCell F) => (p.1, (cache, p.2)))) h
    simp only [Functor.map_map, semantics, StateT.run] at hh ⊢
    convert hh using 1

/-- Erasure retains the joint cache/tape state through adaptive program control. -/
theorem program_erase (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Program CryptoOp TaggedEffect Γ a) (env : Env (cryptoBase F G₁ G₂ K M) Γ) :
    Run.value <$> (code.inline routines).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling machineStore) env =
      code.denote (arithmetic F G₁ G₂ K M cost) semantics env := by
  rw [Program.inline_run]
  change Run.value <$> code.run (arithmetic F G₁ G₂ K M cost) (handler cost sampling) env = _
  rw [Program.run_erase]
  simp_rw [handler_erase]

end Signatures.Runtime.Schnorr.SeedTape

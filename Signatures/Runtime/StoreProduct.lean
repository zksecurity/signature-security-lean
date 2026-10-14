import Signatures.Runtime.Machine
import Signatures.Runtime.Refinement

/-! Executable adapters for disjoint fields of a product store. The refinement keeps
exact costs: read/write adapters cost 10/14 including their call frame, and primitive
randomness forwarding adds five steps. No store projection is an uncharged handler. -/

open OracleComp

namespace Signatures.Runtime.Machine

def firstStore (left right : Ty CryptoAtom) {a b} :
    Effect left a b → Program CryptoOp (Effect (.pair left right)) [a] b
  | .scalar => .query .scalar .unit
  | .uniform n => .query (.uniform n) .unit
  | .read => .bind (.query .read .unit) (.ret (.fst (.var .here)))
  | .write => .bind (.query .read .unit)
    (.query .write (.pair (.var (.there .here)) (.snd (.var .here))))

def secondStore (left right : Ty CryptoAtom) {a b} :
    Effect right a b → Program CryptoOp (Effect (.pair left right)) [a] b
  | .scalar => .query .scalar .unit
  | .uniform n => .query (.uniform n) .unit
  | .read => .bind (.query .read .unit) (.ret (.snd (.var .here)))
  | .write => .bind (.query .read .unit)
    (.query .write (.pair (.fst (.var .here)) (.var (.there .here))))

def forwardedSampling (sampling : SamplingCosts) : SamplingCosts :=
  ⟨sampling.scalar + 5, fun n => sampling.uniform n + 5⟩

variable {F G₁ G₂ K M : Type} [SampleableType F]

/-- Proof-side exact accounting for compiled accessors. Closed programs still execute
the ordinary Machine.effects interpreter; these prices describe the adapter code. -/
noncomputable def pricedStoreEffects (sampling : SamplingCosts) (store : Ty CryptoAtom)
    (readPrice writePrice : Nat) : HandlerM (cryptoBase F G₁ G₂ K M) (Effect store)
      (StateT (store.Value (cryptoBase F G₁ G₂ K M)) ProbComp) := fun cmd arg state => match cmd with
  | .scalar => (fun x => (⟨x, sampling.scalar⟩, state)) <$> ($ᵗ F : ProbComp F)
  | .uniform n => (fun x => (⟨x, sampling.uniform n⟩, state)) <$>
      (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .read => pure (⟨state, readPrice⟩, state)
  | .write => pure (⟨(), writePrice⟩, arg)

theorem pricedStoreEffects_one (sampling : SamplingCosts) (store : Ty CryptoAtom) :
    (pricedStoreEffects sampling store 1 1 : HandlerM (cryptoBase F G₁ G₂ K M) (Effect store)
      (StateT (store.Value (cryptoBase F G₁ G₂ K M)) ProbComp)) =
      (fun {a b} cmd arg => effects sampling store (a := a) (b := b) cmd arg) := rfl

private theorem state_map {S A B : Type} (f : A → B) (x : StateT S ProbComp A) (s : S) :
    (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s := StateT.run_map _ _ _

private theorem state_bind {S A B : Type} (x : StateT S ProbComp A)
    (next : A → StateT S ProbComp B) (s : S) :
    (x >>= next) s = (x s >>= fun p => next p.1 p.2) := rfl

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq K] [DecidableEq M]

theorem firstStore_refines (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (left right : Ty CryptoAtom) (other : right.Value (cryptoBase F G₁ G₂ K M))
    {a b} (cmd : Effect left a b) (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    StateRefines (fun s => (s, other))
      (pricedStoreEffects (forwardedSampling sampling) left 10 14 cmd arg)
      (routineHandler (arithmetic F G₁ G₂ K M cost) (effects sampling (.pair left right))
        (firstStore left right) cmd arg) := by
  intro s
  cases cmd <;>
    simp [firstStore, routineHandler, Program.run, Expr.run, Var.get, Var.depth,
      pricedStoreEffects, forwardedSampling, StateT.run,
      bind_pure_comp, Functor.map_map, Nat.add_assoc]
  all_goals simp only [state_map, state_bind]
  all_goals dsimp [effects]
  all_goals simp [Functor.map_map, bind_pure_comp, Nat.add_left_comm, Nat.add_comm]

theorem secondStore_refines (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (left right : Ty CryptoAtom) (other : left.Value (cryptoBase F G₁ G₂ K M))
    {a b} (cmd : Effect right a b) (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    StateRefines (fun s => (other, s))
      (pricedStoreEffects (forwardedSampling sampling) right 10 14 cmd arg)
      (routineHandler (arithmetic F G₁ G₂ K M cost) (effects sampling (.pair left right))
        (secondStore left right) cmd arg) := by
  intro s
  cases cmd <;>
    simp [secondStore, routineHandler, Program.run, Expr.run, Var.get, Var.depth,
      pricedStoreEffects, forwardedSampling, StateT.run,
      bind_pure_comp, Functor.map_map, Nat.add_assoc]
  all_goals simp only [state_map, state_bind]
  all_goals dsimp [effects]
  all_goals simp [Functor.map_map, bind_pure_comp, Nat.add_left_comm, Nat.add_comm]

/-- Executing any adapted program preserves the untouched field and its complete
joint law, including the charged result and updated owned field. -/
theorem firstStore_run (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (left right : Ty CryptoAtom) {Γ a} (code : Program CryptoOp (Effect left) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (s : left.Value (cryptoBase F G₁ G₂ K M)) (other : right.Value (cryptoBase F G₁ G₂ K M)) :
    ((code.inline (firstStore left right)).run (arithmetic F G₁ G₂ K M cost)
      (effects sampling (.pair left right)) env).run (s, other) =
      (fun p => (p.1, (p.2, other))) <$>
        (code.run (arithmetic F G₁ G₂ K M cost)
          (pricedStoreEffects (forwardedSampling sampling) left 10 14) env).run s := by
  rw [Program.inline_run]
  exact (Program.run_refines (arithmetic F G₁ G₂ K M cost) (fun s => (s, other))
    _ _ (firstStore_refines cost sampling left right other) code env s).symm

theorem secondStore_run (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (left right : Ty CryptoAtom) {Γ a} (code : Program CryptoOp (Effect right) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (other : left.Value (cryptoBase F G₁ G₂ K M)) (s : right.Value (cryptoBase F G₁ G₂ K M)) :
    ((code.inline (secondStore left right)).run (arithmetic F G₁ G₂ K M cost)
      (effects sampling (.pair left right)) env).run (other, s) =
      (fun p => (p.1, (other, p.2))) <$>
        (code.run (arithmetic F G₁ G₂ K M cost)
          (pricedStoreEffects (forwardedSampling sampling) right 10 14) env).run s := by
  rw [Program.inline_run]
  exact (Program.run_refines (arithmetic F G₁ G₂ K M cost) (fun s => (other, s))
    _ _ (secondStore_refines cost sampling left right other) code env s).symm

end Signatures.Runtime.Machine

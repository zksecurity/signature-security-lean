import Proofs.Runtime.SchnorrMachine
import Proofs.Runtime.GrowingState
import Proofs.Runtime.SchnorrRandomness
import Proofs.Runtime.SchnorrCacheRefinement

/-! Schnorr simulation before lowering to the replay machine. Only fresh live-cache
challenges carry the forkable tag; signing randomness is private. Cache reads and
writes are explicit commands and are not random-oracle queries. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

/-- Native adversary capabilities; randomness has bounded request arity, not fixed answers. -/
inductive Command (randomBound : Nat) : Ty CryptoAtom → Ty CryptoAtom → Type
  | random (n : Fin (randomBound + 1)) : Command randomBound .unit (boundedNat n.val)
  | hash : Command randomBound hashKey scalar
  | sign : Command randomBound message (.pair point₁ scalar)

def kind {randomBound a b} : Command randomBound a b → Fin 3
  | .random _ => 0
  | .hash => 1
  | .sign => 2

/-- No reply values are excluded when certifying source resources. -/
def replies {F G₁ G₂ K M : Type} [Zero F] [Zero G₁] (randomBound : Nat) :
    ReplyContract (cryptoBase F G₁ G₂ K M) (Command randomBound) where
  allows _ _ _ := True
  responds cmd _ := by
    cases cmd with
    | random _ => exact ⟨0, trivial⟩
    | hash => exact ⟨0, trivial⟩
    | sign => exact ⟨(0, 0), trivial⟩

def cacheSize {F G₁ G₂ K M : Type} (s : cacheStore.Value (cryptoBase F G₁ G₂ K M)) : Nat :=
  max s.2.1.length s.2.2.length

inductive TaggedEffect : Ty CryptoAtom → Ty CryptoAtom → Type
  | scalar (live : Bool) : TaggedEffect .unit scalar
  | uniform (n : Nat) : TaggedEffect .unit (boundedNat n)
  | read : TaggedEffect .unit cacheStore
  | write : TaggedEffect cacheStore .unit

def taggedHash := hashProgram TaggedEffect.read TaggedEffect.write (.scalar true)
def taggedFinalHash := finalHashProgram TaggedEffect.read TaggedEffect.write (.scalar true)
def taggedSign := signProgram TaggedEffect.read TaggedEffect.write (.scalar false)

def taggedRoutines (randomBound : Nat) {a b} :
    Command randomBound a b → Program CryptoOp TaggedEffect [a] b
  | .random n => .query (.uniform n.val) .unit
  | .hash => taggedHash
  | .sign => taggedSign

variable {F G₁ G₂ K M : Type} [Field F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

omit [Field F] [DecidableEq F] in
private theorem state_pure {S A : Type} (a : A) (s : S) :
    (pure a : StateT S (OracleComp (replaySpec F)) A) s = pure (a, s) := rfl

omit [Field F] [DecidableEq F] in
private theorem state_map {S A B : Type} (f : A → B)
    (x : StateT S (OracleComp (replaySpec F)) A) (s : S) :
    (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s := by
  exact StateT.run_map _ _ _

omit [Field F] [DecidableEq F] in
private theorem state_bind {S A B : Type} (x : StateT S (OracleComp (replaySpec F)) A)
    (next : A → StateT S (OracleComp (replaySpec F)) B) (s : S) :
    (x >>= next) s = (x s >>= fun p => next p.1 p.2) := rfl

def taggedSemantics : SemanticsM (cryptoBase F G₁ G₂ K M) TaggedEffect
    (StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (replaySpec F))) :=
  fun cmd arg state => match cmd with
  | .scalar live =>
    (fun x => (x, state)) <$>
      (if live then (liftM ((replaySpec F).query (.inr ())) : OracleComp (replaySpec F) F)
       else liftM ((replaySpec F).query (.inl (.inr ()))))
  | .uniform n =>
    (fun x => (x, state)) <$>
      (liftM ((replaySpec F).query (.inl (.inl n))) : OracleComp (replaySpec F) (Fin (n + 1)))
  | .read => pure (state, state)
  | .write => pure ((), arg)

theorem taggedHash_denote (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    (taggedHash.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (k, ())).run
        ((g, pk), managed, live) =
      match cacheMap managed k with
      | some c => pure (c, ((g, pk), managed, live))
      | none =>
        (fun p => (p.1, ((g, pk), (k, p.1) :: managed, p.2))) <$>
          (match cacheMap live k with
          | some c => pure (c, live)
          | none => (fun c => (c, (k, c) :: live)) <$>
              (liftM ((replaySpec F).query (.inr ())) : OracleComp (replaySpec F) F)) := by
  unfold taggedHash
  rw [hashProgram_denote]
  dsimp [StateT.run, StateT.bind, StateT.pure, taggedSemantics]
  simp only [pure_bind]
  rw [managedGet_denote, lookupValue_cacheMap]
  cases hm : cacheMap managed k with
  | some c => simp [state_pure]
  | none =>
    simp only [Bool.false_eq_true, ite_false]
    rw [cacheGetExpr_denote _ _ _ _ (hashEq_value (F := F) (G₂ := G₂) (K := K) cost)]
    rw [lookupValue_cacheMap]
    cases hl : cacheMap live k <;>
      simp [state_map, state_pure, taggedSemantics, bind_pure_comp, Functor.map_map]

theorem taggedFinalHash_denote (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    (taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (k, ())).run
        ((g, pk), managed, live) =
      (fun p => (p.1, ((g, pk), managed, p.2))) <$>
        (match cacheMap live k with
        | some c => pure (c, live)
        | none => (fun c => (c, (k, c) :: live)) <$>
            (liftM ((replaySpec F).query (.inr ())) : OracleComp (replaySpec F) F)) := by
  unfold taggedFinalHash
  rw [finalHashProgram_denote]
  dsimp [StateT.run, StateT.bind, StateT.pure, taggedSemantics]
  simp only [pure_bind]
  rw [cacheGetExpr_denote _ _ _ _ (hashEq_value (F := F) (G₂ := G₂) (K := K) cost),
    lookupValue_cacheMap]
  cases cacheMap live k <;>
    simp [state_map, state_pure, taggedSemantics, bind_pure_comp, Functor.map_map]

theorem taggedSign_denote (cost : PrimitiveCosts) (msg : M) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    (taggedSign.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (msg, ())).run
        ((g, pk), managed, live) = (do
      let c ← (replaySpec F).query (.inl (.inr ()))
      let z ← (replaySpec F).query (.inl (.inr ()))
      let R := z • g - c • pk
      let updated := ((cacheProgram (val := scalar) hashEq).run (arithmetic F G₁ G₂ K M cost)
        ((msg, R), c, managed, ())).value
      pure ((R, z), ((g, pk), updated, live))) := by
  unfold taggedSign
  rw [signProgram_denote]
  dsimp [StateT.run, StateT.bind, StateT.pure, taggedSemantics]
  simp only [pure_bind]
  rw [signCached_denote]
  simp only [state_bind, state_pure]
  dsimp [taggedSemantics]
  simp only [bind_map_left, pure_bind, bind_assoc]

/-- A simulated signature consumes private randomness, never a forkable live challenge. -/
theorem taggedSign_noChallenge (cost : PrimitiveCosts) (msg : M) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    IsQueryBoundP ((taggedSign.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (msg, ())).run ((g, pk), managed, live)) (fun i => i = Sum.inr ()) 0 := by
  rw [taggedSign_denote]
  simp

theorem taggedSign_privateBound (cost : PrimitiveCosts) (msg : M) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    IsQueryBoundP ((taggedSign.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (msg, ())).run ((g, pk), managed, live))
      (fun i => i = Sum.inl (Sum.inr ())) 2 := by
  rw [taggedSign_denote]
  simp

theorem taggedHash_liveBound (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    IsQueryBoundP ((taggedHash.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (k, ())).run ((g, pk), managed, live)) (fun i => i = Sum.inr ()) 1 := by
  rw [taggedHash_denote]
  cases cacheMap managed k <;> cases cacheMap live k <;>
    simp [map_eq_bind_pure_comp]

theorem taggedFinalHash_liveBound (cost : PrimitiveCosts) (k : M × G₁) (g pk : G₁)
    (managed live : List ((M × G₁) × F)) :
    IsQueryBoundP ((taggedFinalHash.denote (arithmetic F G₁ G₂ K M cost)
      taggedSemantics (k, ())).run ((g, pk), managed, live)) (fun i => i = Sum.inr ()) 1 := by
  rw [taggedFinalHash_denote]
  cases cacheMap live k <;> simp [map_eq_bind_pure_comp]

end Signatures.Runtime.Schnorr

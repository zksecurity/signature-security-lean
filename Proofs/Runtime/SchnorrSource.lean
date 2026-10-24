import Proofs.Runtime.SchnorrForkCorrectness
import Proofs.Runtime.Refinement
import Signatures.Schnorr.Spec.ROM

/-! Native CMA requests and implementation certificates for the original Schnorr
adversary. Source code receives a public key and fixed data, never simulator caches. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.Schnorr

private theorem state_pure {m : Type → Type} [Monad m] {S A : Type} (a : A) (s : S) :
    (pure a : StateT S m A) s = pure (a, s) := rfl

private theorem state_bind {m : Type → Type} [Monad m] {S A B : Type}
    (main : StateT S m A) (next : A → StateT S m B) (s : S) :
    (main >>= next) s = (main s >>= fun p => next p.1 p.2) := rfl

private theorem state_map {m : Type → Type} [Monad m] [LawfulMonad m] {S A B : Type}
    (f : A → B) (main : StateT S m A) (s : S) :
    (f <$> main) s = (fun p => (f p.1, p.2)) <$> main s := StateT.run_map _ _ _

section Expansion

variable {F S A B : Type} [SampleableType F]

def expandState (main : StateT S (OracleComp (replaySpec F)) A) :
    StateT S (OracleComp (expandedSpec F)) A := fun s =>
  simulateQ (Replay.expandPrivate privateImpl) (main s)

theorem expandState_pure (a : A) :
    expandState (pure a : StateT S (OracleComp (replaySpec F)) A) = pure a := by
  funext s
  simp [expandState, state_pure]

theorem expandState_bind (main : StateT S (OracleComp (replaySpec F)) A)
    (next : A → StateT S (OracleComp (replaySpec F)) B) :
    expandState (main >>= next) = (expandState main >>= fun a => expandState (next a)) := by
  funext s
  simp [expandState, state_bind]

theorem expandState_repeat (step : A → StateT S (OracleComp (replaySpec F)) A)
    (n : Nat) (a : A) :
    expandState (repeatDenote step n a) = repeatDenote (fun a => expandState (step a)) n a := by
  induction n generalizing a with
  | zero => exact expandState_pure a
  | succ n ih => simp only [repeatDenote, expandState_bind, ih]

theorem Program.denote_expand {Atom : Type} {base : Atom → Type}
    {Op Cmd : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (H : SemanticsM base Cmd (StateT S (OracleComp (replaySpec F))))
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    expandState (code.denote P H env) =
      code.denote P (fun cmd arg => expandState (H cmd arg)) env := by
  induction code with
  | ret e => exact expandState_pure _
  | query cmd arg => rfl
  | bind first next ih ihnext => simp only [Program.denote, expandState_bind, ih, ihnext]
  | branch cond yes no ihyes ihno =>
      simp only [Program.denote]
      split <;> first | exact ihyes env | exact ihno env
  | loop count init body ih => simp only [Program.denote, expandState_repeat, ih]
  | call body args ih => exact ih (args.denote P env)

end Expansion

variable {F G₁ G₂ K M : Type}

def sourceSemantics (randomBound : Nat) :
    Semantics (cryptoBase F G₁ G₂ K M) (Command randomBound) (FiatShamir.cmaOracleSpec M G₁ F F) :=
  fun cmd arg => match cmd with
  | .random n => liftM ((FiatShamir.cmaOracleSpec M G₁ F F).query (.inl (.inl n.val)))
  | .hash => liftM ((FiatShamir.cmaOracleSpec M G₁ F F).query (.inl (.inr arg)))
  | .sign => liftM ((FiatShamir.cmaOracleSpec M G₁ F F).query (.inr arg))

variable [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

/-- Exact native behavior and all-reply-path resources of the source, for every
public key. Fixed data may be structured; loading it is charged by forkPackage. -/
structure SourceCertificate (cost : PrimitiveCosts) (randomBound localTime : Nat)
    (queries : Fin 3 → Nat)
    (adv : G₁ → OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) (M × G₁ × F)) where
  dataTy : Ty CryptoAtom
  data : dataTy.Value (cryptoBase F G₁ G₂ K M)
  code : Program CryptoOp (Command randomBound) [point₁, dataTy] forgery
  semantics : ∀ pk, code.denote (arithmetic F G₁ G₂ K M cost)
    (sourceSemantics randomBound) (pk, data, ()) = adv pk
  budget : ∀ pk, SourceBudget (arithmetic F G₁ G₂ K M cost) (replies randomBound) kind
    code (pk, data, ()) localTime queries

def expandedSource (cost : PrimitiveCosts) (randomBound : Nat) :
    SemanticsM (cryptoBase F G₁ G₂ K M) (Command randomBound)
      (StateT (cacheStore.Value (cryptoBase F G₁ G₂ K M)) (OracleComp (expandedSpec F))) :=
  fun cmd arg => expandState ((taggedRoutines randomBound cmd).denote
    (arithmetic F G₁ G₂ K M cost) taggedSemantics (arg, ()))

theorem expandedSource_run (cost : PrimitiveCosts) {Γ a} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (s : cacheStore.Value (cryptoBase F G₁ G₂ K M)) :
    simulateQ (Replay.expandPrivate privateImpl)
      (((code.inline (taggedRoutines randomBound)).denote (arithmetic F G₁ G₂ K M cost)
        taggedSemantics env).run s) =
      (code.denote (arithmetic F G₁ G₂ K M cost) (expandedSource cost randomBound) env).run s := by
  change (expandState ((code.inline (taggedRoutines randomBound)).denote
    (arithmetic F G₁ G₂ K M cost) taggedSemantics env)).run s = _
  rw [Program.inline_denote, Program.denote_expand]
  rfl

abbrev NativeStore (F G M : Type) :=
  (G × G) × (FiatShamir.fsRoSpec M G F).QueryCache × FiatShamir.Fork.SimState M G F

def nativeRepr (s : cacheStore.Value (cryptoBase F G₁ G₂ K M)) : NativeStore F G₁ M :=
  (s.1, managedState s.2.1, liveState s.2.2)

def liveImpl : QueryImpl (FiatShamir.fsRoSpec M G₁ F)
    (StateT (FiatShamir.Fork.SimState M G₁ F) (OracleComp (expandedSpec F))) :=
  FiatShamir.Fork.unifForward M G₁ F + FiatShamir.Fork.roImpl M G₁ F

def nativeImpl : QueryImpl (FiatShamir.cmaOracleSpec M G₁ F F)
    (StateT (NativeStore F G₁ M) (OracleComp (expandedSpec F))) := fun i s =>
  (fun p => (p.1.1, (s.1, p.1.2, p.2))) <$>
    (simulateQ liveImpl ((FiatShamir.simulatedNmaImpl (M := M)
      (_root_.Schnorr.simTranscript F G₁ s.1.1) s.1.2 i).run s.2.1)).run s.2.2

omit [DecidableEq F] in
theorem nativeImpl_run {A : Type}
    (main : OracleComp (FiatShamir.cmaOracleSpec M G₁ F F) A)
    (g pk : G₁) (managed : (FiatShamir.fsRoSpec M G₁ F).QueryCache)
    (live : FiatShamir.Fork.SimState M G₁ F) :
    (simulateQ nativeImpl main).run ((g, pk), managed, live) =
      (fun p => (p.1.1, ((g, pk), p.1.2, p.2))) <$>
        (simulateQ liveImpl ((simulateQ (FiatShamir.simulatedNmaImpl (M := M)
          (_root_.Schnorr.simTranscript F G₁ g) pk) main).run managed)).run live := by
  induction main using OracleComp.inductionOn generalizing managed live with
  | pure a => simp
  | query_bind i next ih =>
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, map_bind]
    dsimp only [nativeImpl, StateT.run]
    simp only [bind_map_left]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

/-- The proof-side cache interpreter has just one capability: a fresh live challenge. -/
inductive LiveDraw : Ty CryptoAtom → Ty CryptoAtom → Type
  | sample : LiveDraw .unit scalar

def liveDraw : Semantics (cryptoBase F G₁ G₂ K M) LiveDraw (expandedSpec F) :=
  fun .sample _ => FiatShamir.Fork.wrappedChallengeQuery F

theorem expandedSource_hash (cost : PrimitiveCosts) (randomBound : Nat)
    (k : M × G₁) (g pk : G₁) (managed live : List ((M × G₁) × F)) :
    (expandedSource cost randomBound .hash k).run ((g, pk), managed, live) =
      (fun p => (p.1, ((g, pk), p.2.1, p.2.2))) <$>
        (managedGet LiveDraw.sample).denote (arithmetic F G₁ G₂ K M cost) liveDraw
          (k, 0, managed, live, ()) := by
  change simulateQ (Replay.expandPrivate privateImpl)
    ((taggedHash.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (k, ())).run
      ((g, pk), managed, live)) = _
  rw [taggedHash_denote, managedGet_denote, lookupValue_cacheMap]
  cases hm : cacheMap managed k with
  | some c => simp
  | none =>
    simp only [Bool.false_eq_true, ite_false]
    rw [cacheGetExpr_denote _ _ _ _ (hashEq_value (F := F) (G₂ := G₂) (K := K) cost),
      lookupValue_cacheMap]
    cases hl : cacheMap live k <;>
      simp [liveDraw, Replay.expandPrivate,
        FiatShamir.Fork.wrappedChallengeQuery, Functor.map_map]

theorem expandedSource_hash_refines (cost : PrimitiveCosts) (randomBound : Nat) (k : M × G₁) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (expandedSource cost randomBound .hash k)
      (nativeImpl (.inl (.inr k))) := by
  rintro ⟨⟨g, pk⟩, managed, live⟩
  rw [expandedSource_hash]
  have h := managedGet_refines cost (liveDraw (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
    LiveDraw.sample rfl k 0 managed live
  have he := congrArg (fun main => (fun p : (F × (FiatShamir.fsRoSpec M G₁ F).QueryCache) ×
      FiatShamir.Fork.SimState M G₁ F => (p.1.1, ((g, pk), p.1.2, p.2))) <$> main) h
  change _ = (fun p => (p.1.1, ((g, pk), p.1.2, p.2))) <$>
    (simulateQ (FiatShamir.Fork.unifForward M G₁ F + FiatShamir.Fork.roImpl M G₁ F)
      ((FiatShamir.simulatedNmaRoSim (M := M) (Commit := G₁) (Chal := F) k).run
        (managedState managed))).run (liveState live)
  simpa only [Functor.map_map, Function.comp_def, nativeRepr] using he

omit [Field F] [SampleableType F] [DecidableEq F] [AddCommGroup G₁] [Module F G₁] in
theorem liveImpl_uniform {A : Type} (main : ProbComp A)
    (live : FiatShamir.Fork.SimState M G₁ F) :
    (simulateQ liveImpl (simulateQ (uniformToRo (F := F) (G₁ := G₁) (M := M)) main)).run live =
      (fun a => (a, live)) <$> liftRandom main := by
  induction main using OracleComp.inductionOn generalizing live with
  | pure a => simp [liftRandom]
  | query_bind n next ih =>
    have hu : (liveImpl (F := F) (G₁ := G₁) (M := M) (.inl n)).run live =
        (fun x => (x, live)) <$> (liftM ((expandedSpec F).query (.inl n)) : OracleComp _ (Fin (n + 1))) := by
      change (FiatShamir.Fork.unifForward M G₁ F n).run live = _
      simp [FiatShamir.Fork.unifForward_run, FiatShamir.Fork.wrappedUniformQuery, bind_pure_comp]
    simp only [simulateQ_bind, simulateQ_spec_query, uniformToRo, StateT.run_bind,
      liftRandom, map_bind, hu, bind_map_left]
    congr 1
    funext a
    exact ih a live

theorem expandedSource_random_refines (cost : PrimitiveCosts) (randomBound : Nat)
    (n : Fin (randomBound + 1)) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (expandedSource cost randomBound (.random n) ())
      (nativeImpl (.inl (.inl n.val))) := by
  rintro ⟨⟨g, pk⟩, managed, live⟩
  have h : (FiatShamir.simulatedNmaImpl (M := M) (_root_.Schnorr.simTranscript F G₁ g) pk
      (.inl (.inl n.val))).run (managedState managed) =
      (fun x => (x, managedState managed)) <$>
        (liftM ((FiatShamir.fsRoSpec M G₁ F).query (.inl n.val)) : OracleComp _ (Fin (n.val + 1))) := rfl
  change (fun p => (p.1, nativeRepr p.2)) <$>
    simulateQ (Replay.expandPrivate privateImpl)
      (((taggedRoutines randomBound (.random n)).denote (arithmetic F G₁ G₂ K M cost)
        taggedSemantics ((), ())).run ((g, pk), managed, live)) = _
  simp only [taggedRoutines, Program.denote, taggedSemantics,
    StateT.run, simulateQ_map, simulateQ_spec_query, Replay.expandPrivate, privateImpl,
    Functor.map_map]
  change _ = (fun p => (p.1.1, ((g, pk), p.1.2, p.2))) <$>
    (simulateQ liveImpl ((FiatShamir.simulatedNmaImpl (M := M)
      (_root_.Schnorr.simTranscript F G₁ g) pk (.inl (.inl n.val))).run (managedState managed))).run
        (liveState live)
  rw [h]
  simp [liveImpl, simulateQ_map,
    FiatShamir.Fork.unifForward_run, StateT.run_map, Functor.map_map,
    FiatShamir.Fork.wrappedUniformQuery, nativeRepr]

omit [DecidableEq F] in
theorem nativeImpl_sign (msg : M) (g pk : G₁)
    (managed : (FiatShamir.fsRoSpec M G₁ F).QueryCache) (live : FiatShamir.Fork.SimState M G₁ F) :
    (nativeImpl (.inr msg)).run ((g, pk), managed, live) =
      (fun t : G₁ × F × F => ((t.1, t.2.2), ((g, pk),
        (match managed (.inr (msg, t.1)) with
        | some _ => managed
        | none => managed.cacheQuery (.inr (msg, t.1)) t.2.1), live))) <$>
        liftRandom (_root_.Schnorr.simTranscript F G₁ g pk) := by
  change (fun p => (p.1.1, ((g, pk), p.1.2, p.2))) <$>
    (simulateQ liveImpl ((FiatShamir.simulatedNmaSigSim (M := M)
      (_root_.Schnorr.simTranscript F G₁ g) pk msg).run managed)).run live = _
  simp only [FiatShamir.simulatedNmaSigSim, StateT.run_bind, unifSim_run,
    StateT.run_modifyGet, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [liveImpl_uniform]
  simp only [Functor.map_map]
  congr 1
  funext t
  cases managed (.inr (msg, t.1)) <;> rfl

theorem expandedSource_sign_refines (cost : PrimitiveCosts) (randomBound : Nat) (msg : M) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (expandedSource cost randomBound .sign msg) (nativeImpl (.inr msg)) := by
  rintro ⟨⟨g, pk⟩, managed, live⟩
  change (fun p => (p.1, nativeRepr p.2)) <$>
    simulateQ (Replay.expandPrivate privateImpl)
      ((taggedSign.denote (arithmetic F G₁ G₂ K M cost) taggedSemantics (msg, ())).run
        ((g, pk), managed, live)) = _
  rw [taggedSign_denote]
  change _ = (nativeImpl (.inr msg)).run ((g, pk), managedState managed, liveState live)
  rw [nativeImpl_sign]
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query, Replay.expandPrivate,
    privateImpl, _root_.Schnorr.simTranscript, liftRandom, map_bind, map_pure]
  congr 1
  funext c
  congr 1
  funext z
  apply congrArg pure
  change ((z • g - c • pk, z), ((g, pk),
    managedState ((cacheProgram (val := scalar) hashEq).run (arithmetic F G₁ G₂ K M cost)
      ((msg, z • g - c • pk), c, managed, ())).value, liveState live)) = _
  rw [cacheProgram_managedState (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M)]
  cases (managedState managed (.inr (msg, z • g - c • pk))) <;> rfl

def nativeSource (randomBound : Nat) :
    SemanticsM (cryptoBase F G₁ G₂ K M) (Command randomBound)
      (StateT (NativeStore F G₁ M) (OracleComp (expandedSpec F))) :=
  fun cmd arg => simulateQ nativeImpl (sourceSemantics randomBound cmd arg)

theorem expandedSource_refines (cost : PrimitiveCosts) (randomBound : Nat)
    {a b} (cmd : Command randomBound a b) (arg : a.Value (cryptoBase F G₁ G₂ K M)) :
    StateRefines (nativeRepr (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M))
      (expandedSource cost randomBound cmd arg) (nativeSource randomBound cmd arg) := by
  cases cmd with
  | random n =>
    cases arg
    simpa [nativeSource, sourceSemantics] using
      expandedSource_random_refines (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost randomBound n
  | hash => simpa [nativeSource, sourceSemantics] using
      expandedSource_hash_refines (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost randomBound arg
  | sign => simpa [nativeSource, sourceSemantics] using
      expandedSource_sign_refines (F := F) (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost randomBound arg

/-- Full adaptive source interpretation agrees with the native CMA simulator,
including both represented caches. The source certificate is not needed for this
structural theorem; it applies to every program in the source language. -/
theorem source_refines (cost : PrimitiveCosts) {Γ a} (randomBound : Nat)
    (code : Program CryptoOp (Command randomBound) Γ a)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (s : cacheStore.Value (cryptoBase F G₁ G₂ K M)) :
    (fun p => (p.1, nativeRepr p.2)) <$>
        simulateQ (Replay.expandPrivate privateImpl)
          (((code.inline (taggedRoutines randomBound)).denote (arithmetic F G₁ G₂ K M cost)
            taggedSemantics env).run s) =
      (simulateQ nativeImpl (code.denote (arithmetic F G₁ G₂ K M cost)
        (sourceSemantics randomBound) env)).run (nativeRepr s) := by
  rw [expandedSource_run, Program.denote_simulate]
  exact code.denote_refines (arithmetic F G₁ G₂ K M cost) nativeRepr
    (expandedSource cost randomBound) (nativeSource randomBound)
    (expandedSource_refines cost randomBound) env s

end Signatures.Runtime.Schnorr

import Proofs.Runtime.BackendStateSimulation
import Proofs.Runtime.BackendSchnorrRawUniform
import Proofs.Runtime.BackendLanguage

/-! Run an actual scalar sampler through the raw private tape. Its internal
uniform queries use the same families as the attacker's private requests.
The supplied interface conversions are backend realizers, not free casts. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.RawTape

namespace NativeUniform

def decodeNat (n value : Nat) : Fin (n + 1) :=
  ⟨value % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ n)⟩

@[simp] theorem decodeNat_val (n : Nat) (value : Fin (n + 1)) :
    decodeNat n value.val = value := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt value.isLt

end NativeUniform

namespace NativePrivate

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {iface : Interface (C := C) unifSpec}
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))

/-- Runtime conversions for the sampler's dynamic request and dependent reply.
Decoding uses the original request's arity, including on malformed tape input. -/
structure Ports where
  arity : Q.Realizer iface.position rep.data.nat id
  reply : Q.Realizer (StepClass.HasProd.prod rep.data.nat rep.data.nat) iface.response
    (fun p => ⟨p.2, NativeUniform.decodeNat p.2 p.1⟩)

variable (ports : Ports (Q := Q) rep (iface := iface))

def handler : Code Q unifSpec iface
    (StepClass.HasProd.prod iface.position (rep.ty NativeUniform.stateTy))
    (StepClass.HasProd.prod iface.response (rep.ty NativeUniform.stateTy)) :=
  .seq (.first (rep.ty NativeUniform.stateTy) (.atomic ports.arity))
    (.seq (Language.withContext (rep.ty NativeUniform.stateTy) (Q.identity rep.data.nat)
      (NativeUniform.code rep data cost primitive uniform))
      (.first (rep.ty NativeUniform.stateTy) (.atomic ports.reply)))

omit QD ports in
/-- Typed decoding agrees with the source oracle on every tape. Validity is
only needed when exposing the unreduced natural as the reply. -/
theorem uniform_decoded [SampleableType F] (n : Nat) (state : State F) :
    (fun p => (NativeUniform.decodeNat n p.1, p.2)) <$>
      (NativeUniform.code rep data cost primitive uniform).denote (n, NativeUniform.encodeState state) =
    (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
      simulateQ _root_.Schnorr.LazyROM.sample ((oracle (.inl n)).run state) := by
  rw [NativeUniform.denote]
  cases found : (SeedTape.pop (n + 2) (0, (0 : F), 0) state.remaining).1 with
  | false =>
      simp [oracle, tag, family, SeedTape.familyTag, found, StateT.run,
        _root_.Schnorr.LazyROM.sample, encode, encodeReply,
        NativeUniform.encodeState, Functor.map_map]
  | true =>
      simp [oracle, tag, family, SeedTape.familyTag, found, StateT.run,
        decode, decodeReply, NativeUniform.encodeState, NativeUniform.decodeNat]

variable [SampleableType F]

def semantics : QueryImpl unifSpec
    (StateT (List (TapeCell F) × List (TapeCell F)) ProbComp) :=
  fun n saved => (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
    simulateQ _root_.Schnorr.LazyROM.sample ((oracle (.inl n)).run ⟨saved.1, saved.2⟩)

omit QD in
theorem handler_denote (n : Nat) (saved : List (TapeCell F) × List (TapeCell F)) :
    (handler rep data cost primitive uniform ports).denote (n, saved) =
      (fun p => (Sigma.mk n p.1, p.2)) <$> (semantics n).run saved := by
  have h := congrArg (Functor.map (fun p => ((⟨n, p.1⟩ : Σ n, Fin (n + 1)), p.2)))
    (uniform_decoded rep data cost primitive uniform n ⟨saved.1, saved.2⟩)
  simpa only [handler, Code.denote, Language.withContext_denote,
    map_pure, pure_bind, bind_pure_comp, bind_map_left,
    Functor.map_map, id_eq, NativeUniform.encodeState, semantics, StateT.run] using h

omit rep data cost primitive uniform ports QD QS QP [Q.HasCategory] [DecidableEq F] in
theorem simulate_source {A : Type} (main : ProbComp A) (state : State F) :
    (simulateQ semantics main).run (NativeUniform.encodeState state) =
      (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample
          ((simulateQ oracle (liftRandom main)).run state) := by
  induction main using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind n next ih =>
      simp only [liftRandom, simulateQ_bind, simulateQ_spec_query]
      change ((semantics n).run (NativeUniform.encodeState state) >>= fun p =>
        (simulateQ semantics (next p.1)).run p.2) =
        (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
          simulateQ _root_.Schnorr.LazyROM.sample
            (((oracle (.inl n)).run state) >>= fun p =>
              (simulateQ oracle (liftRandom (next p.1))).run p.2)
      simp only [semantics, StateT.run, NativeUniform.encodeState,
        bind_map_left, simulateQ_bind, map_bind]
      congr 1
      funext p
      exact ih p.1 p.2

def code {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q unifSpec iface a b) :
    Code Q unifSpec iface (StepClass.HasProd.prod a (rep.ty NativeUniform.stateTy))
      (StepClass.HasProd.prod b (rep.ty NativeUniform.stateTy)) :=
  StateSimulation.compile (rep.ty NativeUniform.stateTy)
    (handler rep data cost primitive uniform ports) program

theorem source {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q unifSpec iface a b) (input : A) (state : State F) :
    (code rep data cost primitive uniform ports program).denote (input, NativeUniform.encodeState state) =
      (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample
          ((simulateQ oracle (liftRandom (program.denote input))).run state) := by
  rw [code, StateSimulation.compile_denote _ _ semantics
    (handler_denote rep data cost primitive uniform ports)]
  exact simulate_source (program.denote input) state

theorem scalar_source (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (hsample : sampler.denote () = ($ᵗ F : ProbComp F)) (state : State F) :
    (code rep data cost primitive uniform ports sampler).denote ((), NativeUniform.encodeState state) =
      (fun p => (p.1, NativeUniform.encodeState p.2)) <$>
        simulateQ _root_.Schnorr.LazyROM.sample
          ((simulateQ oracle (privateImpl (.inr ()))).run state) := by
  rw [source, hsample]
  rfl

end NativePrivate
end Signatures.Runtime.Schnorr.RawTape

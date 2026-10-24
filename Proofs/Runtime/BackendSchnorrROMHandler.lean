import Proofs.Runtime.BackendSchnorrROMInterface
import Proofs.Runtime.BackendSchnorrROMHandlerSource
import Proofs.Runtime.BackendIndexedHandler
import Proofs.Runtime.BackendCallerCorrectness
import Proofs.Runtime.GeneralCallerResources

/-! Executed dispatch for arbitrary ordinary-ROM callers. Source requests and
dependent replies cross actual backend ports. The costed handler is a typed view
of this same code's run, with no separately assumed dispatcher runtime. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram NativeInterface NativeComponents

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : RawTape.NativePrivate.Ports (Q := Q) rep (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def tagged {a b : Ty CryptoAtom}
    {f : (a.Value (cryptoBase F G₁ G₂ K M) × b.Value (cryptoBase F G₁ G₂ K M)) → Response F G₁ M}
    (tag : Q.Realizer (rep.ty (.pair a b)) bd.idx f)
    (body : Code Q unifSpec iface (rep.ty (withStore a)) (rep.ty (withStore b))) :
    Code Q unifSpec iface (rep.ty (withStore a)) (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (Language.withContext (rep.ty storeTy) (Q.identity (rep.ty a)) body)
    (.first (rep.ty storeTy) (.atomic (Q.compose
      (QP.pair (QP.snd (rep.ty b) (rep.ty a)) (QP.fst (rep.ty b) (rep.ty a))) tag)))

def random : Code Q unifSpec iface (rep.ty (withStore .nat)) (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  tagged rep bd ports.randomTag (NativeComponents.random rep data cost primitive uniform)

def hash : Code Q unifSpec iface (rep.ty (withStore hashKey)) (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  tagged rep bd ports.hashTag (NativeComponents.hash rep data cost primitive sampler)

def signing : Code Q unifSpec iface (rep.ty (withStore message)) (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  tagged rep bd ports.signingTag (NativeComponents.signing rep data cost primitive uniform privatePorts sampler)

def inner : Code Q unifSpec iface
    (StepClass.HasProd.prod (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey)) (rep.ty storeTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.atomic (QD.distribute rep.data.nat (rep.ty hashKey) (rep.ty storeTy)))
    (.branch (random rep bd ports data cost primitive uniform) (hash rep bd ports data cost primitive sampler))

def dispatch : Code Q unifSpec iface (StepClass.HasProd.prod (positions rep) (rep.ty storeTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.atomic (QD.distribute (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey))
    (rep.ty message) (rep.ty storeTy)))
    (.branch (inner rep bd ports data cost primitive uniform sampler)
      (signing rep bd ports data cost primitive uniform privatePorts sampler))

def code : Code Q unifSpec iface (StepClass.HasProd.prod bd.pos (rep.ty storeTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.first (rep.ty storeTy) (.atomic ports.request))
    (dispatch rep bd ports data cost primitive uniform privatePorts sampler)

/-- The shared dispatcher with an explicit executed signing component. -/
def dispatchWithSigning
    (signer : Code Q unifSpec iface (rep.ty (withStore message)) (rep.ty (withStore signatureTy))) :
    Code Q unifSpec iface (StepClass.HasProd.prod (positions rep) (rep.ty storeTy))
      (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.atomic (QD.distribute (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey))
    (rep.ty message) (rep.ty storeTy)))
    (.branch (inner rep bd ports data cost primitive uniform sampler)
      (tagged rep bd ports.signingTag signer))

/-- Request conversion and dispatch retain the actual supplied signer code. -/
def codeWithSigning
    (signer : Code Q unifSpec iface (rep.ty (withStore message)) (rep.ty (withStore signatureTy))) :
    Code Q unifSpec iface (StepClass.HasProd.prod bd.pos (rep.ty storeTy))
      (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.first (rep.ty storeTy) (.atomic ports.request))
    (dispatchWithSigning rep bd ports data cost primitive uniform sampler signer)

omit QD QS [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G₁]
  [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem tagged_denote {a b : Ty CryptoAtom}
    {f : (a.Value (cryptoBase F G₁ G₂ K M) × b.Value (cryptoBase F G₁ G₂ K M)) → Response F G₁ M}
    (tag : Q.Realizer (rep.ty (.pair a b)) bd.idx f)
    (body : Code Q unifSpec iface (rep.ty (withStore a)) (rep.ty (withStore b)))
    (arg : a.Value (cryptoBase F G₁ G₂ K M)) (saved : Shared.Store F G₁ M) :
    (tagged rep bd tag body).denote (arg, saved) =
      (fun p => (f (arg, p.1), p.2)) <$> body.denote (arg, saved) := by
  simp only [tagged, Language.withContext_denote, Code.denote, map_pure, bind_pure_comp, Functor.map_map]
  rfl

def source : QueryImpl (sourceSpec F G₁ M) (StateT (Shared.Store F G₁ M) ProbComp) :=
  fun q => Shared.interpret (ListROM.handler (G₂ := G₂) (K := K) q)

variable (sample : sampler.denote () = ($ᵗ F : ProbComp F))

include sample in
theorem code_denote (q : NativeInterface.Request G₁ M) (saved : Shared.Store F G₁ M) :
    (code rep bd ports data cost primitive uniform privatePorts sampler).denote (q, saved) =
      (fun p => ((⟨q, p.1⟩ : Response F G₁ M), p.2)) <$>
        (source (G₂ := G₂) (K := K) q).run saved := by
  rcases q with (n | k) | msg
  · simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
    rw [random, tagged_denote]
    calc
      _ = (fun p : Fin (n + 1) × Shared.Store F G₁ M =>
          ((⟨.inl (.inl n), p.1⟩ : Response F G₁ M), p.2)) <$>
          ((fun p => (RawTape.NativeUniform.decodeNat n p.1, p.2)) <$>
            (NativeComponents.random rep data cost primitive uniform).denote (n, saved)) := by
        rw [Functor.map_map]
        rfl
      _ = _ := by
        rw [NativeComponents.random_source rep data cost primitive uniform]
        rfl
  · simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
    rw [hash, tagged_denote, NativeComponents.hash_source rep data cost primitive sampler sample]
    rfl
  · simp only [code, dispatch, Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
    rw [signing, tagged_denote, NativeComponents.signing_source rep data cost primitive sampler sample]
    rfl

variable (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

def executed : GeneralCaller.Handler (spec := sourceSpec F G₁ M) (StateT (Shared.Store F G₁ M) ProbComp) :=
  IndexedHandler.handler control queryCost (code rep bd ports data cost primitive uniform privatePorts sampler) defaultReply

include sample in
theorem code_executed_run (q : NativeInterface.Request G₁ M) (saved : Shared.Store F G₁ M) :
    (code rep bd ports data cost primitive uniform privatePorts sampler).run control queryCost (q, saved) =
      (fun p => (⟨(⟨q, p.1.value⟩, p.2), p.1.steps⟩ : Run (Response F G₁ M × Shared.Store F G₁ M))) <$>
        ((executed rep bd ports data cost primitive uniform privatePorts sampler control queryCost q).run saved) := by
  apply IndexedHandler.handler_run
  exact IndexedHandler.matches_of_denote control queryCost _ (source (G₂ := G₂) (K := K))
    (code_denote rep bd ports data cost primitive uniform privatePorts sampler sample)

include sample in
theorem executed_erase (q : NativeInterface.Request G₁ M) (saved : Shared.Store F G₁ M) :
    (fun p => (p.1.value, p.2)) <$>
      ((executed rep bd ports data cost primitive uniform privatePorts sampler control queryCost q).run saved) =
        (source (G₂ := G₂) (K := K) q).run saved :=
  IndexedHandler.handler_erase control queryCost _ defaultReply (source (G₂ := G₂) (K := K))
    (code_denote rep bd ports data cost primitive uniform privatePorts sampler sample) q saved

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def caller (fuel : Nat) : Code Q unifSpec iface (StepClass.HasProd.prod bd.input (rep.ty storeTy))
    (Caller.result (bd := bd) (rep.ty storeTy)) :=
  Caller.program R (rep.ty storeTy) (code rep bd ports data cost primitive uniform privatePorts sampler) fuel

include sample in
theorem caller_denote (fuel : Nat) (input : Input) (saved : Shared.Store F G₁ M) :
    (caller rep bd ports data cost primitive uniform privatePorts sampler R fuel).denote (input, saved) =
      (R.machine.runWithInput (source (G₂ := G₂) (K := K)) fuel input).run saved :=
  Caller.program_denote R (rep.ty storeTy) _ (source (G₂ := G₂) (K := K))
    (code_denote rep bd ports data cost primitive uniform privatePorts sampler sample) fuel input saved

include sample in
theorem caller_source (fuel : Nat) (program : Input → OracleComp (sourceSpec F G₁ M) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input) (saved : Shared.Store F G₁ M) :
    (caller rep bd ports data cost primitive uniform privatePorts sampler R fuel).denote (input, saved) =
      (fun p => (some p.1, p.2)) <$>
        (Shared.interpret (simulateQ (ListROM.handler (G₂ := G₂) (K := K)) (program input))).run saved := by
  rw [caller_denote rep bd ports data cost primitive uniform privatePorts sampler sample R,
    hprogram.simulateQ_run_eq]
  change (some <$> simulateQ (fun q => Shared.interpret (ListROM.handler (G₂ := G₂) (K := K) q))
    (program input)).run saved = _
  rw [← Shared.interpret_simulate, StateT.run_map]

include sample in
theorem caller_source_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (sourceSpec F G₁ M) Output)
    (hprogram : R.machine.Implements program) (input : Input) (saved : Shared.Store F G₁ M) :
    (caller rep bd ports data cost primitive uniform privatePorts sampler R fuel).denote (input, saved) =
      (fun p => (some p.1, p.2)) <$>
        (Shared.interpret (simulateQ (ListROM.handler (G₂ := G₂) (K := K)) (program input))).run saved :=
  caller_source rep bd ports data cost primitive uniform privatePorts sampler sample R fuel program
    (GeneralCaller.implementsWithin_of_resources R bound hrun program hprogram fuel hfuel) input saved

include sample in
theorem caller_no_cutoff_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (sourceSpec F G₁ M) Output) (hprogram : R.machine.Implements program)
    (input : Input) (saved : Shared.Store F G₁ M) (z : Run (Option Output × Shared.Store F G₁ M))
    (hz : z ∈ support ((caller rep bd ports data cost primitive uniform privatePorts sampler R fuel).run
      control queryCost (input, saved))) : ∃ out, z.value.1 = some out := by
  have hv := Code.value_mem_denote control queryCost
    (caller rep bd ports data cost primitive uniform privatePorts sampler R fuel) (input, saved) z hz
  rw [caller_source_of_resources rep bd ports data cost primitive uniform privatePorts sampler sample R
    bound hrun fuel hfuel program hprogram, support_map] at hv
  obtain ⟨p, _, he⟩ := hv
  exact ⟨p.1, (congrArg Prod.fst he).symm⟩

end Signatures.Runtime.Schnorr.ListROM.NativeHandler

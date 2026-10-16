import Signatures.Runtime.BackendSchnorrROMHandler
import Signatures.Runtime.BackendSchnorrNonzeroComponents

/-! Executed nonzero-nonce Schnorr dispatch and arbitrary caller semantics.
Both original scalar samplers are installed in the signing component. Random
and hash requests use the same source interface and shared replay store. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open BackendProgram ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeHandler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
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
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def code : Code Q unifSpec iface (StepClass.HasProd.prod bd.pos (rep.ty storeTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  codeWithSigning rep bd ports data cost primitive uniform fieldSampler
    (NativeComponents.signing rep data cost primitive uniform privatePorts fieldSampler nonzeroSampler)

def source : QueryImpl (sourceSpec F G₁ M) (StateT (Shared.Store F G₁ M) ProbComp) :=
  fun q => Shared.interpret (NonzeroListROM.handler (G₂ := G₂) (K := K) q)

variable (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))

include fieldLaw nonzeroLaw in
theorem code_denote (q : NativeInterface.Request G₁ M) (saved : Shared.Store F G₁ M) :
    (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler).denote (q, saved) =
      (fun p => ((⟨q, p.1⟩ : Response F G₁ M), p.2)) <$>
        (source (G₂ := G₂) (K := K) q).run saved := by
  rcases q with (n | k) | msg
  · simp only [code, codeWithSigning, dispatchWithSigning, ListROM.NativeHandler.inner, Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
    rw [ListROM.NativeHandler.random, tagged_denote]
    calc
      _ = (fun p : Fin (n + 1) × Shared.Store F G₁ M =>
          ((⟨.inl (.inl n), p.1⟩ : Response F G₁ M), p.2)) <$>
          ((fun p => (RawTape.NativeUniform.decodeNat n p.1, p.2)) <$>
            (ListROM.NativeComponents.random rep data cost primitive uniform).denote (n, saved)) := by
        rw [Functor.map_map]
        rfl
      _ = _ := by
        rw [ListROM.NativeComponents.random_source rep data cost primitive uniform]
        rfl
  · simp only [code, codeWithSigning, dispatchWithSigning, ListROM.NativeHandler.inner, Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
    rw [ListROM.NativeHandler.hash, tagged_denote, ListROM.NativeComponents.hash_source rep data cost primitive fieldSampler fieldLaw]
    rfl
  · simp only [code, codeWithSigning, dispatchWithSigning, Code.denote, map_pure, pure_bind, id_eq, Sum.elim]
    rw [tagged_denote, NativeComponents.signing_source rep data cost primitive uniform privatePorts
      fieldSampler nonzeroSampler fieldLaw nonzeroLaw]
    rfl

variable (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

def executed : GeneralCaller.Handler (spec := sourceSpec F G₁ M) (StateT (Shared.Store F G₁ M) ProbComp) :=
  IndexedHandler.handler control queryCost (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler) defaultReply

include fieldLaw nonzeroLaw in
theorem code_executed_run (q : NativeInterface.Request G₁ M) (saved : Shared.Store F G₁ M) :
    (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler).run control queryCost (q, saved) =
      (fun p => (⟨(⟨q, p.1.value⟩, p.2), p.1.steps⟩ : Run (Response F G₁ M × Shared.Store F G₁ M))) <$>
        ((executed rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler control queryCost q).run saved) := by
  apply IndexedHandler.handler_run
  exact IndexedHandler.matches_of_denote control queryCost _ (source (G₂ := G₂) (K := K))
    (code_denote rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw)

include fieldLaw nonzeroLaw in
theorem executed_erase (q : NativeInterface.Request G₁ M) (saved : Shared.Store F G₁ M) :
    (fun p => (p.1.value, p.2)) <$>
      ((executed rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler control queryCost q).run saved) =
        (source (G₂ := G₂) (K := K) q).run saved :=
  IndexedHandler.handler_erase control queryCost _ defaultReply (source (G₂ := G₂) (K := K))
    (code_denote rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw) q saved

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def caller (fuel : Nat) : Code Q unifSpec iface (StepClass.HasProd.prod bd.input (rep.ty storeTy))
    (Caller.result (bd := bd) (rep.ty storeTy)) :=
  Caller.program R (rep.ty storeTy) (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler) fuel

include fieldLaw nonzeroLaw in
theorem caller_denote (fuel : Nat) (input : Input) (saved : Shared.Store F G₁ M) :
    (caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).denote (input, saved) =
      (R.machine.runWithInput (source (G₂ := G₂) (K := K)) fuel input).run saved :=
  Caller.program_denote R (rep.ty storeTy) _ (source (G₂ := G₂) (K := K))
    (code_denote rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw) fuel input saved

include fieldLaw nonzeroLaw in
theorem caller_source (fuel : Nat) (program : Input → OracleComp (sourceSpec F G₁ M) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input) (saved : Shared.Store F G₁ M) :
    (caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).denote (input, saved) =
      (fun p => (some p.1, p.2)) <$>
        (Shared.interpret (simulateQ (NonzeroListROM.handler (G₂ := G₂) (K := K)) (program input))).run saved := by
  rw [caller_denote rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw R,
    hprogram.simulateQ_run_eq]
  change (some <$> simulateQ (fun q => Shared.interpret (NonzeroListROM.handler (G₂ := G₂) (K := K) q))
    (program input)).run saved = _
  rw [← Shared.interpret_simulate, StateT.run_map]

include fieldLaw nonzeroLaw in
theorem caller_source_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (sourceSpec F G₁ M) Output)
    (hprogram : R.machine.Implements program) (input : Input) (saved : Shared.Store F G₁ M) :
    (caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).denote (input, saved) =
      (fun p => (some p.1, p.2)) <$>
        (Shared.interpret (simulateQ (NonzeroListROM.handler (G₂ := G₂) (K := K)) (program input))).run saved :=
  caller_source rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw R fuel program
    (GeneralCaller.implementsWithin_of_resources R bound hrun program hprogram fuel hfuel) input saved

include fieldLaw nonzeroLaw in
theorem caller_no_cutoff_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (sourceSpec F G₁ M) Output) (hprogram : R.machine.Implements program)
    (input : Input) (saved : Shared.Store F G₁ M) (z : Run (Option Output × Shared.Store F G₁ M))
    (hz : z ∈ support ((caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).run
      control queryCost (input, saved))) : ∃ out, z.value.1 = some out := by
  have hv := Code.value_mem_denote control queryCost
    (caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel) (input, saved) z hz
  rw [caller_source_of_resources rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw R
    bound hrun fuel hfuel program hprogram, support_map] at hv
  obtain ⟨p, _, he⟩ := hv
  exact ⟨p.1, (congrArg Prod.fst he).symm⟩

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

import Proofs.Runtime.BackendSchnorrAGMCallerResources
import Proofs.Runtime.BackendSchnorrAGMHandlerSource
import Proofs.Runtime.GeneralCallerOutput

/-! Measured return sizes and termination for the actual native Schnorr caller.
These bounds include a return at zero remaining fuel. Sufficient measured query
fuel gives exact finite-list source correspondence and rules out cutoff. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [DecidableEq (SourceRequest F G₁ M)]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem caller_reference_denote (fuel : Nat) (input : Input) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (caller rep bd ports data cost primitive randomPorts sampler R fuel).denote (input, saved) =
      (fun p => (p.1.value, p.2)) <$>
        ((GeneralCaller.run R (executed rep bd ports data cost primitive randomPorts sampler control queryCost) fuel input).run saved) := by
  have hhandler : (fun q => Run.value <$> executed rep bd ports data cost primitive randomPorts sampler control queryCost q) =
      source rep data cost primitive randomPorts sampler := by
    funext q saved
    change (Run.value <$> executed rep bd ports data cost primitive randomPorts sampler control queryCost q).run saved = _
    rw [StateT.run_map]
    exact executed_erase rep bd ports data cost primitive randomPorts sampler control queryCost q saved
  rw [caller_denote]
  have h := congrArg (fun computation => computation.run saved)
    (GeneralCaller.runFrom_erase R (executed rep bd ports data cost primitive randomPorts sampler control queryCost)
      fuel (R.machine.init input))
  rw [hhandler, GeneralCaller.denoteFrom_eq_runWith] at h
  simp only [runWithInput, GeneralCaller.run, bind_pure_comp, StateT.run_map, Functor.map_map] at h ⊢
  exact h.symm

theorem caller_output_invariant (inv : Nat → R.machine.State → Prop) (valid : Output → Prop)
    (hstep : ∀ n state, inv (n + 1) state → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ → ∀ answer, inv n (next answer))
    (hreturn : ∀ n state, inv n state → ∀ out, R.machine.view state = .inl out → valid out)
    (fuel : Nat) (input : Input) (hi : inv fuel (R.machine.init input)) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (z : Run (Option Output × ((G₁ × G₁) × EncodedState F G₁ M)))
    (hz : z ∈ support ((caller rep bd ports data cost primitive randomPorts sampler R fuel).run control queryCost (input, saved)))
    (out : Output) (hout : z.value.1 = some out) : valid out := by
  have hv := Code.value_mem_denote control queryCost
    (caller rep bd ports data cost primitive randomPorts sampler R fuel) (input, saved) z hz
  rw [caller_reference_denote rep bd ports data cost primitive randomPorts sampler control queryCost R, support_map] at hv
  obtain ⟨p, hp, he⟩ := hv
  exact GeneralCaller.run_output_invariant R (executed rep bd ports data cost primitive randomPorts sampler control queryCost)
    inv valid hstep hreturn fuel input hi saved p hp out ((congrArg Prod.fst he).trans hout)

variable (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include hrun

theorem caller_output_size_of_resources {header : Nat} (sizes : SizeLaws Q header)
    (fuel : Nat) (input : Input) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (z : Run (Option Output × ((G₁ × G₁) × EncodedState F G₁ M)))
    (hz : z ∈ support ((caller rep bd ports data cost primitive randomPorts sampler R fuel).run control queryCost (input, saved)))
    (out : Output) (hout : z.value.1 = some out) : Q.size bd.out out ≤ bound.peakHeadSize := by
  exact caller_output_invariant rep bd ports data cost primitive randomPorts sampler control queryCost R
    (fun _ => GeneralCaller.Reachable R) (fun out => Q.size bd.out out ≤ bound.peakHeadSize)
    (fun _ state hs q next hv answer => GeneralCaller.reachable_step R state hs q next hv answer)
    (fun _ state hs out hv => reachable_output bd sizes R bound hrun state hs out hv)
    fuel input (GeneralCaller.reachable_init R input) saved z hz out hout

/-- No sampler law is needed to show that the realized attacker finishes:
termination is uniform over every typed oracle reply. -/
theorem caller_no_cutoff_of_resources (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (sourceSpec F G₁ M) Output)
    (hprogram : R.machine.Implements program) (input : Input) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (z : Run (Option Output × ((G₁ × G₁) × EncodedState F G₁ M)))
    (hz : z ∈ support ((caller rep bd ports data cost primitive randomPorts sampler R fuel).run control queryCost (input, saved))) :
    ∃ out, z.value.1 = some out := by
  have hv := Code.value_mem_denote control queryCost
    (caller rep bd ports data cost primitive randomPorts sampler R fuel) (input, saved) z hz
  rw [caller_denote,
    (GeneralCaller.implementsWithin_of_resources R bound hrun program hprogram fuel hfuel).simulateQ_run_eq
      (source rep data cost primitive randomPorts sampler) input,
    StateT.run_map, support_map] at hv
  obtain ⟨p, _, he⟩ := hv
  exact ⟨p.1, (congrArg Prod.fst he).symm⟩

variable [SampleableType F]

theorem caller_source_of_resources (hsample : sampler.denote () = ($ᵗ F : ProbComp F))
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (sourceSpec F G₁ M) Output)
    (hprogram : R.machine.Implements program) (input : Input) (g pk : G₁) (s : State F G₁ M) :
    (caller rep bd ports data cost primitive randomPorts sampler R fuel).denote (input, (g, pk), encodeState s) =
      (fun p => (some p.1, (g, pk), encodeState p.2)) <$>
        (simulateQ (handler g pk) (program input)).run s :=
  caller_source rep data cost primitive randomPorts sampler hsample bd ports R fuel program
    (GeneralCaller.implementsWithin_of_resources R bound hrun program hprogram fuel hfuel) input g pk s

end Signatures.Runtime.SchnorrAGM.Native.Handler

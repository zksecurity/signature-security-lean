import Signatures.Runtime.BackendCoronSolverBudget
import Signatures.Runtime.BackendCoronSolverDescription

/-! An actual executable witness for the named lazy Coron co-CDH solver, in the
same fixed backend class that executes the general caller. Its complete time
and stored-code bounds are derived; caller premises concern only its own local
work, queries, representations, termination, and source identification. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeSolver

open BackendProgram ReplyCompiler

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (boundary : DataPorts (Q := Q) rep bd)
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptionSizes allowance)
  (descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance)
  (descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance)

include sizes lists mono routing localLaws dispatchLaws dataLaws
  descriptionLaws descriptionData descriptionDispatch

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem program_within
    (qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel localTime tickTime : Nat)
    (queries : Fin 3 → Nat)
    (comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hm : messageWidth ≤ width) (hroute : 8 * width ≤ routeWidth) (hcap : fuel ≤ cap)
    (hf : ∀ y : F, Q.size (rep.ty scalar) y ≤ scalarWidth)
    (hc : ∀ y : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) y ≤ coinWidth)
    (hg : ∀ y : G₁, Q.size (rep.ty point₁) y ≤ groupWidth)
    (hw : storeWidth header messageWidth scalarWidth coinWidth groupWidth cap ≤ width)
    (handlerCaps : NativeHandler.PortCaps rep bd ports width handlerAdapterTime)
    (solverCaps : PortCaps rep bd boundary inputWidth routeWidth solverAdapterTime)
    (dynamicSamples : NativeHandler.DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        NativeHandler.RequestSized (Q := Q) rep width i ∧
        NativeHandler.RequestMessages (fun m => Q.size (rep.ty message) m ≤ messageWidth) i ∧
        ∀ reply, callerInv n (next reply))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (hmessage : ∀ n state, callerInv n state → ∀ out, R.machine.view state = .inl out →
      Q.size (rep.ty message) out.1 ≤ messageWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (hentry : ∀ pk, Q.size (rep.ty point₂) pk ≤ inputWidth →
      callerInv fuel (R.machine.init pk) ∧
      GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind fuel pk localTime queries)
    (sourceProgram : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin sourceProgram fuel)
    (adv : BLS.CoCDH.Tight.TightAdvPK M G₁ G₂)
    (hsource : ∀ pk, simulateQ (generalSource randomBound) (sourceProgram pk) = adv pk)
    (instructionSize handlerPortSize solverPortSize : Nat)
    (instructionDescriptions : NativeInstructionDescriptions rep cost primitive descriptionSizes qS instructionSize)
    (handlerDescriptions : NativeHandler.PortDescriptions rep bd ports descriptionSizes handlerPortSize)
    (solverDescriptions : PortDescriptions rep bd boundary descriptionSizes solverPortSize) :
    Within backend descriptionSizes factor description (rep.env inputTypes) (rep.ty point₁) inputWidth
      (factor * (descriptionSizes.localSize R.initCode + 2 * descriptionSizes.localSize R.headCode +
        descriptionSizes.localSize R.updateCode + fuel + 3 * samplingCode.scalar.descriptionSize descriptionSizes +
        3 * (samplingCode.uniform qS).descriptionSize descriptionSizes + sampler.code.descriptionSize descriptionSizes +
        4000 * allowance + 40 * instructionSize + 4 * handlerPortSize + 3 * solverPortSize + 500))
      (nativeSolverTime overhead inputWidth width routeWidth cap fuel localTime tickTime queries
        comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime)
      (fun input => BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.CoCDH.Tight.cacheForgeryPK adv)
        input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1) := by
  have he : ∀ input,
      (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel).denote input =
        BLS.CoCDH.coronReductionLazyPK (F := F) qS (BLS.CoCDH.Tight.cacheForgeryPK adv)
          input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1 := by
    rintro ⟨g, g₂, X, pk, h, u⟩
    cases u
    exact program_denote_original rep bd ports sampler boundary data samplingCode cost primitive R
      ⟨0, fun _ => 0⟩ qS fuel sourceProgram hprogram adv hsource g g₂ X pk h
  have hb : Bounds control queryCost (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel)
      (fun input => Q.size (rep.env inputTypes) input ≤ inputWidth) (fun _ => True)
      (nativeSolverTime overhead inputWidth width routeWidth cap fuel localTime tickTime queries
        comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime) := by
    rintro ⟨g, g₂, X, pk, h, u⟩ hi z hz
    cases u
    obtain ⟨hiCaller, hbudget⟩ := hentry pk ((input_key_size rep sizes g g₂ X pk h).trans hi)
    have ht := program_bound rep bd ports sampler boundary data samplingCode cost primitive control queryCost
      sizes lists mono routing localLaws dispatchLaws dataLaws primitiveBound R
      qS inputWidth messageWidth width scalarWidth coinWidth groupWidth cap routeWidth fuel localTime tickTime queries
      comparisonTime scalarTime coinTime opTime handlerAdapterTime solverAdapterTime dynamicTime hh hm hroute hcap
      hf hc hg hw handlerCaps solverCaps dynamicSamples values ops samples callerInv hcallerStep hcallerWidth
      hmessage htick g g₂ X pk h hi hiCaller hbudget (g, g₂, X, pk, h, ()) rfl z hz
    exact ⟨trivial, ht.2⟩
  have h := within_compile backend descriptionSizes factor description
    (program rep bd ports sampler boundary data samplingCode cost primitive R qS fuel) inputWidth _ _ he hb
  have hd := program_descriptionSize rep bd ports sampler boundary data samplingCode cost primitive R
    descriptionSizes allowance descriptionLaws descriptionData descriptionDispatch qS fuel instructionSize
    handlerPortSize solverPortSize instructionDescriptions handlerDescriptions solverDescriptions
  exact Within.mono backend descriptionSizes factor description h (Nat.mul_le_mul_left factor hd) le_rfl

end Signatures.Runtime.Coron.NativeSolver

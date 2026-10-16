import Signatures.Runtime.BackendSchnorrROMDLog
import Signatures.Runtime.BackendSchnorrNonzeroSolverWithin

/-! Concrete nonzero-nonce Schnorr ROM security for general implemented attackers
in one fixed backend. The complete solver witness is constructed from original
resources before applying DLog hardness. The original quadratic forking loss
and signing-simulation loss are preserved. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open scoped ENNReal

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeSolver

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

variable {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)]
  [Field F] [SampleableType F] [SampleableType Fˣ]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : ListROM.NativePass.DataPorts (Q := Q) rep bd) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : ListROM.NativeHandler.RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

variable
  (backend : Backend.{v, w, x} Q unifSpec iface control queryCost)
  (descriptionSizes : DescriptionSize Q) (factor : Nat)
  (description : backend.DescriptionBound descriptionSizes factor)
  (allowance : Nat) (descriptionLaws : LocalDescriptionLaws descriptionSizes allowance)
  (descriptionData : DataDescriptionLaws descriptionSizes rep.data data allowance)
  (descriptionDispatch : DispatchDescriptionLaws (Q := Q) descriptionSizes allowance)

variable [Fintype F] [SampleableType G₁]

include fieldLaw nonzeroLaw sizes lists laws dataLaws mono routing dispatch hrun
  descriptionLaws descriptionData descriptionDispatch

theorem security_of_resources (inputWidth width tapeWidth managedCap liveCap fuel qH : Nat)
    (first : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts fieldSampler nonzeroSampler primitiveBound
      control queryCost recovery bound (header := header) width tapeWidth managedCap liveCap 0 0 fuel)
    (second : NativePass.Resources rep bd boundary ports cost primitive uniform privatePorts fieldSampler nonzeroSampler primitiveBound
      control queryCost recovery bound (header := header) width tapeWidth managedCap liveCap
        (first.savedCap + 2) (first.savedCap + 2) fuel)
    (scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
      extractionScalarTime fieldSubTime divTime : Nat)
    (selectorOps : NativeSelection.Operations rep cost primitive primitiveBound width (liveCap + 1) qH
      scaleTime addTime messageTime pointTime incrementTime comparisonTime)
    (extractionOps : NativeExtraction.Operations rep cost primitive primitiveBound width pointTime
      extractionScalarTime fieldSubTime divTime first.zeroTime)
    (hn : ∀ n ≤ max (liveCap + 1) qH + 1, Q.size rep.data.nat n ≤ tapeWidth)
    (hscalar : ∀ f g, Q.size (rep.ty scalar) f ≤ tapeWidth → Q.size (rep.ty scalar) g ≤ tapeWidth →
      (primitiveBound .scalarEq).time (f, g) ≤ scalarComparisonTime)
    (hsub : ∀ n ≤ qH, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (hinl : Q.cost (QS.inl rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) () ≤
      overhead (Q.size rep.data.unit () +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) (.inl ())))
    (hinr : ∀ p, Q.cost (QS.inr rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) p ≤
      overhead (Q.size (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy)) p +
        Q.size (StepClass.HasSum.sum rep.data.unit (rep.ty (.pair ListROM.NativePass.outputTy ListROM.NativePass.outputTy))) (.inr p)))
    (hinput : inputWidth ≤ width) (hfuel : bound.queries ≤ fuel)
    (g : G₁) (generates : Function.Bijective (fun x : F => x • g))
    (adv : _root_.Schnorr.NonzeroNonce.Adversary (F := F) (M := M) g)
    (implementation : R.machine.Implements adv.main) (qS : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH)
    (hchallenge : ∀ x : F, Q.size (rep.env inputTypes) (g, x • g, ()) ≤ inputWidth)
    (codeBudget timeBudget : Nat) (epsilon : ENNReal)
    (hcode : factor * (descriptionInputs rep cost primitive fieldSampler nonzeroSampler descriptionSizes bd boundary ports uniform privatePorts R).solver
      allowance fuel qH ≤ codeBudget)
    (htime : resourcesTime overhead bound width tapeWidth managedCap liveCap fuel first.timeInputs second.timeInputs
      scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
      extractionScalarTime fieldSubTime divTime ≤ timeBudget)
    (hardness : Model.HardWithin (fun solver => 𝒟[DiffieHellman.dlogExperiment g solver] {true})
      (ListROM.NativeSolver.dlogWithin rep backend descriptionSizes factor description g inputWidth codeBudget) timeBudget epsilon) :
    let eps := 𝒟[_root_.Schnorr.NonzeroNonce.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤ epsilon := by
  have certificate := program_within rep sizes lists bd boundary ports data cost primitive uniform privatePorts
    fieldSampler nonzeroSampler fieldLaw nonzeroLaw laws dataLaws primitiveBound mono control queryCost routing dispatch R recovery bound hrun
    backend descriptionSizes factor description allowance descriptionLaws descriptionData descriptionDispatch
    inputWidth width tapeWidth managedCap liveCap fuel qH first second scaleTime addTime messageTime pointTime
    incrementTime comparisonTime scalarComparisonTime subtractTime extractionScalarTime fieldSubTime divTime
    selectorOps extractionOps hn hscalar hsub hinl hinr hinput hfuel adv.main implementation
  have hdlog := hardness (reduction (G₂ := G₂) (K := K) adv.main qH)
    ⟨hchallenge, Within.mono backend descriptionSizes factor description certificate hcode htime⟩
  change 𝒟[DiffieHellman.dlogExperiment g (reduction (G₂ := G₂) (K := K) adv.main qH)] {true} ≤ epsilon at hdlog
  rw [reduction_experiment (G₂ := G₂) (K := K) g adv qH] at hdlog
  exact (_root_.Schnorr.NonzeroNonce.LazyROM.security g generates adv qS qH queries).trans hdlog

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver

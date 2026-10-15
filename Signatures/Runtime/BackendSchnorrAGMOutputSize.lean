import Signatures.Runtime.BackendSchnorrAGMCallerOutput

/-! Recover all final forgery sizes from the measured attacker return. Every
group and coefficient row is retained, including malformed or surplus rows.
The output conversion is an encoding relation here; BackendSchnorrAGMSolverOutput
implements and charges the corresponding adapter for the complete solver. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure ForgeryBound (width : Nat) (out : SourceForgery F G₁ M) : Prop where
  encoded : Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ width
  message : Q.size (rep.ty (.atom .message)) out.value.data.1 ≤ width
  scalar : Q.size (rep.ty (.atom .scalar)) out.value.data.2 ≤ width
  groups : (out.value.groups ()).length ≤ width
  rows : (out.coefficients ()).length ≤ width
  coefficients : ∀ row ∈ out.coefficients (), row.length ≤ width

variable (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input (SourceForgery F G₁ M))

structure OutputRecovery where
  recover : Nat → Nat
  monotone : Monotone recover
  encoded : ∀ out, Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ recover (Q.size bd.out out)

/-- Equal-size encodings have identity recovery; this does not supply a free
executable conversion between their underlying types. -/
def canonicalOutputRecovery
    (encoded : ∀ out, Q.size (rep.ty forgeryTy) (encodeForgery out) = Q.size bd.out out) :
    OutputRecovery (Q := Q) rep bd :=
  ⟨id, monotone_id, fun out => (encoded out).le⟩

variable {header : Nat} (sizes : SizeLaws Q header)
  (lengths : ListLengthLaws Q rep.data) (payloads : ListPayloadLaws Q rep.data)

include sizes lengths payloads

theorem forgeryBound_of_size (out : SourceForgery F G₁ M) (width : Nat)
    (ho : Q.size (rep.ty forgeryTy) (encodeForgery out) ≤ width) :
    ForgeryBound (Q := Q) rep width out := by
  have h := argsBound_of_size rep sizes lengths payloads (.pair message scalar) (encodeForgery out) width ho
  exact ⟨ho, (sizes.fst_le (rep.ty message) (rep.ty scalar) out.value.data).trans h.data,
    (sizes.snd_le (rep.ty message) (rep.ty scalar) out.value.data).trans h.data,
    h.groups, h.rows, h.coefficients⟩

theorem forgeryBound_of_output_size (recovery : OutputRecovery (Q := Q) rep bd)
    (out : SourceForgery F G₁ M) (width : Nat) (ho : Q.size bd.out out ≤ width) :
    ForgeryBound (Q := Q) rep (recovery.recover width) out :=
  forgeryBound_of_size rep sizes lengths payloads out _
    ((recovery.encoded out).trans (recovery.monotone ho))

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [DecidableEq (SourceRequest F G₁ M)]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (ports : Ports (Q := Q) rep bd) (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

theorem caller_forgery_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (recovery : OutputRecovery (Q := Q) rep bd)
    (fuel : Nat) (input : Input) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (z : Run (Option (SourceForgery F G₁ M) × ((G₁ × G₁) × EncodedState F G₁ M)))
    (hz : z ∈ support ((caller rep bd ports data cost primitive randomPorts sampler R fuel).run control queryCost (input, saved)))
    (out : SourceForgery F G₁ M) (hout : z.value.1 = some out) :
    ForgeryBound (Q := Q) rep (recovery.recover bound.peakHeadSize) out :=
  forgeryBound_of_output_size rep bd sizes lengths payloads recovery out _
    (caller_output_size_of_resources rep bd ports data cost primitive randomPorts sampler control queryCost R
      bound hrun sizes fuel input saved z hz out hout)

end Signatures.Runtime.SchnorrAGM.Native.Handler

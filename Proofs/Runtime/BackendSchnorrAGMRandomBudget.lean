import Proofs.Runtime.BackendSchnorrAGMRandomLocalCost

/-! Complete randomness-handler accounting: one dynamic uniform query,
request/reply encoding, group scan, state marking, retention and construction.
All budgets follow from local encoding and external-query contracts. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Random

open BackendProgram

def randomTime (overhead : Nat → Nat)
    (width cap basisCap signedCap groupCap rowCap coeffCap requestTime responseTime drawTime : Nat) : Nat :=
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  prepareTime overhead W groupCap + requestTime + responseTime + drawTime + 269 * overhead (256 * W)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (ports : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes lists laws dataLaws mono routing

theorem bound (width cap basisCap signedCap groupCap rowCap coeffCap arityCap requestTime responseTime drawTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ width)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ width)
    (hrequest : ∀ n ≤ arityCap, Q.cost ports.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost ports.response ⟨n, r⟩ ≤ responseTime)
    (hdraw : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ drawTime) :
    Bounds control queryCost (code rep data cost primitive ports)
      (Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap)
      (Output (Q := Q) rep width cap basisCap signedCap arityCap)
      (randomTime overhead width cap basisCap signedCap groupCap rowCap coeffCap requestTime responseTime drawTime) := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  let fee := overhead (256 * W)
  let prepTime := prepareTime overhead W groupCap
  let sampleTime := requestTime + responseTime + drawTime
  let pre := Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap
  let middle := Prepared (Q := Q) rep width cap basisCap signedCap arityCap
  let post := Output (Q := Q) rep width cap basisCap signedCap arityCap
  let primitiveBound := fun {a b : Ty CryptoAtom} (instr : CryptoOp a b) => LocalBound.measured (primitive instr)
  have hw : width ≤ W := calc
    width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
    _ ≤ W := Nat.le_add_right _ _
  have hcore : Signing.frameWidth width cap basisCap signedCap ≤ W := Nat.le_add_right _ _
  have hmiddle (p : preparedTy.Value (cryptoBase F G₁ G₂ K M)) (h : middle p) :
      Q.size (rep.ty preparedTy) p ≤ W :=
    (prepared_size rep sizes lists width cap basisCap signedCap arityCap hh hb hf hn p h).trans hcore
  have hpost (p : outputTy.Value (cryptoBase F G₁ G₂ K M)) (h : post p) :
      Q.size (rep.ty outputTy) p ≤ W :=
    (output_size rep sizes lists width cap basisCap signedCap arityCap hh hb hf hn p h).trans hcore
  have hprepare : Bounds control queryCost (.atomic (iface := iface) (prepare rep data cost primitive))
      pre middle (prepTime + fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := prepare_property rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap input hi
    have hin := (input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap arityCap hh hu hb hf hg hn input hi).1
    have hout := hmiddle (prepareValue input) ho
    have ht := prepare_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
      width cap basisCap signedCap groupCap rowCap coeffCap arityCap hh hu hb hf hg hn input hi
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty inputTy) input + Q.size (rep.ty preparedTy) (prepareValue input) ≤ 256 * W by omega))
    exact ⟨ho, Nat.add_le_add ht hc⟩
  have hs := UniformSampling.bound rep.data ports mono control queryCost routing width arityCap
    requestTime responseTime drawTime hn hp hr hrequest hresponse hdraw
  have hsampling : Bounds control queryCost (.first (rep.ty stateTy) (UniformSampling.code rep.data ports))
      middle middle (sampleTime + 5 * fee) := by
    have h := Bounds.first control queryCost (rep.ty stateTy) (UniformSampling.code rep.data ports)
      (fun n => n ≤ arityCap) (fun r => r ≤ arityCap ∧ Q.size rep.data.nat r ≤ width)
      (Signing.StateBound (Q := Q) rep width cap basisCap signedCap)
      (sampleTime + 4 * overhead (8 * width)) fee hs (by
        intro state hstate r hr'
        have hsize := Signing.state_size rep sizes lists width cap basisCap signedCap hh hb hf state hstate
        have hstateWidth : Q.size (rep.ty stateTy) state ≤ Signing.frameWidth width cap basisCap signedCap := by
          dsimp only [Signing.frameWidth]
          nlinarith
        exact (routing.retain _ _).trans (mono (by omega)))
    intro input hi out hout
    obtain ⟨ho, ht⟩ := h input hi out hout
    have hfee := mono (show 8 * width ≤ 256 * W by omega)
    exact ⟨⟨ho.1.1, ho.2⟩, ht.trans (by dsimp only [fee]; omega)⟩
  have hwrap : Bounds control queryCost (.atomic (iface := iface) (wrap rep data cost primitive)) middle post (261 * fee) := by
    apply Bounds.atomic
    intro input hi
    have ho := wrap_property rep width cap basisCap signedCap arityCap input hi
    have hin := hmiddle input hi
    have hout := hpost (wrapValue input) ho
    have ht := wrap_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono input W
      (hh.trans hw) (hu.trans hw) hin
    have hc := (routing.localCall _ _).trans (mono (show
      Q.size (rep.ty preparedTy) input + Q.size (rep.ty outputTy) (wrapValue input) ≤ 256 * W by omega))
    exact ⟨ho, by dsimp only [fee]; omega⟩
  have htail := Bounds.seq control queryCost _ _ middle middle post (sampleTime + 5 * fee) (261 * fee) fee
    hsampling hwrap (by
      intro input hi output ho
      have hi' := hmiddle input hi
      have ho' := hmiddle output ho
      exact (routing.sequence _ _).trans (mono (by
        dsimp only [LanguageRepresentation.ty] at hi' ho' ⊢
        omega)))
  have hall := Bounds.seq control queryCost _ _ pre middle post (prepTime + fee)
    (sampleTime + 5 * fee + 261 * fee + fee) fee hprepare htail (by
      intro input hi output ho
      have hin := (input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap arityCap hh hu hb hf hg hn input hi).1
      have hout := hmiddle output ho
      exact (routing.sequence _ _).trans (mono (by omega)))
  intro input hi out hout
  obtain ⟨ho, ht⟩ := hall input hi out hout
  exact ⟨ho, ht.trans (by dsimp only [randomTime, prepTime, sampleTime, fee, W]; omega)⟩

end Signatures.Runtime.SchnorrAGM.Native.Random

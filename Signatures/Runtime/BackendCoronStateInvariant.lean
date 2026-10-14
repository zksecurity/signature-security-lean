import Signatures.Runtime.BackendCoronContracts

/-! Preserve source cache invariants through the costed native reply, then use
the same certificate when the reply is called inline by final extraction. The
message-width and store-width caps are separate; growing the store does not
enlarge the bound on encountered messages. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron.ReplyCompiler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type} (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

def StateInvariant (qS messageWidth storeWidth cap : Nat)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) : Prop :=
  Q.size (rep.ty (machineStore qS)) saved ≤ storeWidth ∧
    (machineCaches saved).Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth) ∧
    (machineCaches saved).size ≤ cap

omit [C.HasSum] in
theorem StateInvariant.mono (qS messageWidth storeWidth cap messageWidth' storeWidth' cap' : Nat)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hi : StateInvariant (Q := Q) rep qS messageWidth storeWidth cap saved)
    (hm : messageWidth ≤ messageWidth') (hs : storeWidth ≤ storeWidth') (hc : cap ≤ cap') :
    StateInvariant (Q := Q) rep qS messageWidth' storeWidth' cap' saved := by
  exact ⟨hi.1.trans hs, ⟨(fun p hp => (hi.2.1.1 p hp).trans hm),
    (fun p hp => (hi.2.1.2.1 p hp).trans hm), (fun m hm' => (hi.2.1.2.2 m hm').trans hm)⟩,
    hi.2.2.trans hc⟩

omit [C.HasSum] in
theorem StateInvariant.ready (qS messageWidth storeWidth width cap : Nat)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hi : StateInvariant (Q := Q) rep qS messageWidth storeWidth cap saved)
    (hm : messageWidth ≤ width) (hs : storeWidth ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ width)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ width) :
    StoreReady (Q := Q) rep qS width cap saved := by
  exact ⟨hi.1.trans hs, (fun p hp => ⟨(hi.2.1.1 p hp).trans hm, hf p.2⟩),
    (Nat.le_max_left _ _).trans hi.2.2,
    (fun p hp => ⟨(hi.2.1.2.1 p hp).trans hm, hc p.2⟩),
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans hi.2.2⟩

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

theorem backendReply_stateFacts (qS : Nat) (signing : Bool) (m : M)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) (messageWidth storeWidth cap : Nat)
    (hm : Q.size (rep.ty message) m ≤ messageWidth)
    (hi : StateInvariant (Q := Q) rep qS messageWidth storeWidth cap saved)
    (z : Run (G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((backendReply rep data samplingCode cost primitive qS signing).run control queryCost (m, saved))) :
    (machineCaches z.value.2).Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth) ∧
      (machineCaches z.value.2).size ≤ cap + 1 := by
  -- Old interpreter prices are erased by the state-correspondence theorem.
  obtain ⟨state', he, hmessages, hcount⟩ := backendReply_state_invariant rep data samplingCode cost primitive
    control queryCost ⟨0, fun _ => 0⟩ saved.1.1 saved.1.2.1 saved.1.2.2 qS signing m
    (fun m => Q.size (rep.ty message) m ≤ messageWidth) (machineCaches saved) hm hi.2.1 z hz
  rw [he]
  exact ⟨hmessages, hcount.trans (Nat.add_le_add_right hi.2.2 1)⟩

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)
  (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)

include sizes lists localLaws dataLaws mono routing

theorem backendReply_invariant_bound (qS : Nat) (signing : Bool)
    (width cap comparisonTime scalarTime coinTime opTime : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime) :
    Bounds control queryCost (backendReply rep data samplingCode cost primitive qS signing)
      (fun p => Q.size (rep.ty message) p.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width width cap p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧
        StateInvariant (Q := Q) rep qS width (writtenStoreWidth width cap) (cap + 1) p.2)
      (nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime) := by
  have hb := backendReply_bound rep data samplingCode cost primitive localLaws dataLaws primitiveBound sizes lists mono
    control queryCost routing qS signing width cap comparisonTime scalarTime coinTime opTime hh
    values.unit values.bool values.scalar values.coin values.point values.nat ops.message ops.fieldZero ops.coinZero
    ops.convert ops.natEq ops.pointZero ops.scale ops.add samples.scalar samples.coin
  intro input hi z hz
  have hr := hb input ⟨hi.1, StateInvariant.ready rep qS width width width cap input.2 hi.2 le_rfl le_rfl
    values.scalar values.coin⟩ z hz
  have hs := backendReply_stateFacts rep data samplingCode cost primitive control queryCost qS signing input.1 input.2
    width width cap hi.1 hi.2 z hz
  exact ⟨⟨hr.1.1, hr.1.2, hs⟩, hr.2⟩

theorem replyProgram_invariant_bound (qS : Nat) (signing : Bool)
    (width cap comparisonTime scalarTime coinTime opTime : Nat) (hh : header ≤ width)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime) :
    Bounds control queryCost (MachineCompiler.program rep data samplingCode cost primitive (machineStore qS) (machineReply qS signing))
      (fun p => Q.size (rep.ty message) p.1.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width width cap p.2)
      (fun p => Q.size (rep.ty point₁) p.1 ≤ width ∧
        StateInvariant (Q := Q) rep qS width (writtenStoreWidth width cap) (cap + 1) p.2)
      (nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime) := by
  let pre := fun p : M × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size (rep.ty message) p.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width width cap p.2
  let post := fun p : G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M) =>
    Q.size (rep.ty point₁) p.1 ≤ width ∧ StateInvariant (Q := Q) rep qS width (writtenStoreWidth width cap) (cap + 1) p.2
  have hb := backendReply_invariant_bound rep data samplingCode cost primitive control queryCost sizes lists localLaws dataLaws
    primitiveBound mono routing qS signing width cap comparisonTime scalarTime coinTime opTime hh values ops samples
  have hcode : backendReply rep data samplingCode cost primitive qS signing =
      MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS) (machineReply qS signing) := by
    rw [backendReply]
  have hu : Bounds control queryCost (MachineCompiler.unary rep data samplingCode cost primitive (machineStore qS)
      (machineReply qS signing)) pre post (nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime) :=
    Eq.mp (congrArg (fun code : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.ty message) (rep.ty (machineStore qS)))
      (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) =>
        Bounds control queryCost code pre post (nativeReplyTime overhead width cap comparisonTime scalarTime coinTime opTime)) hcode) hb
  exact MachineCompiler.program_bound_of_unary rep data samplingCode control queryCost cost primitive (machineStore qS)
    (machineReply qS signing) pre post _ hu

end Signatures.Runtime.Coron.ReplyCompiler

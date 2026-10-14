import Signatures.Runtime.BackendCoronHandlerBudget
import Signatures.Runtime.BackendCoronCaller

/-! The complete native dispatcher's actual cache provenance and encoded size.
The message-width bound stays fixed as queries accumulate. Runtime certificates
may use a larger frame width, while reachable storage is bounded linearly in
the number of encountered entries. Distributional correspondence is used only
for state facts; costs come from the native dispatcher budget. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeHandler

open BackendProgram ReplyCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

def RequestMessages (valid : M → Prop) : GeneralRequest M randomBound → Prop
  | .inl (.inl _) => True
  | .inl (.inr m) => valid m
  | .inr m => valid m

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem code_stateFacts (qS : Nat) (g X h : G₁) (valid : M → Prop)
    (state : CacheState F M qS) (hs : state.Messages valid) (i : GeneralRequest M randomBound)
    (hi : RequestMessages valid i)
    (z : Run (GeneralIndex M G₁ randomBound × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((code rep bd ports sampler data samplingCode cost primitive qS).run control queryCost
      (i, machineState g X h state))) :
    ∃ state' : CacheState F M qS, z.value.2 = machineState g X h state' ∧
      state'.Messages valid ∧ state'.size ≤ state.size + 1 := by
  have hv := Code.value_mem_denote control queryCost
    (code rep bd ports sampler data samplingCode cost primitive qS) (i, machineState g X h state) z hz
  rcases i with (n | m) | m
  · rw [code_random_denote, support_map] at hv
    obtain ⟨reply, _, he⟩ := hv
    exact ⟨state, congrArg Prod.snd he.symm, hs, Nat.le_succ _⟩
  · rw [code_hash_denote, ← Code.run_erase control queryCost, Functor.map_map, support_map] at hv
    obtain ⟨out, hout, he⟩ := hv
    obtain ⟨state', hstate, hm, hc⟩ := backendReply_state_invariant rep data samplingCode cost primitive
      control queryCost ⟨0, fun _ => 0⟩ g X h qS false m valid state hi hs out hout
    exact ⟨state', (congrArg Prod.snd he.symm).trans hstate, hm, hc⟩
  · rw [code_sign_denote, ← Code.run_erase control queryCost, Functor.map_map, support_map] at hv
    obtain ⟨out, hout, he⟩ := hv
    obtain ⟨state', hstate, hm, hc⟩ := backendReply_state_invariant rep data samplingCode cost primitive
      control queryCost ⟨0, fun _ => 0⟩ g X h qS true m valid state hi hs out hout
    exact ⟨state', (congrArg Prod.snd he.symm).trans hstate, hm, hc⟩

/-- A supported typed-handler outcome is the same native run with its reply
index restored, including the exact native step count. -/
theorem executed_mem_code (qS : Nat) (i : GeneralRequest M randomBound)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (z : Run ((generalSpec M G₁ randomBound).Range i) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support ((executed rep bd ports sampler data samplingCode cost primitive control queryCost qS i).run saved)) :
    (⟨(⟨i, z.1.value⟩, z.2), z.1.steps⟩ : Run (GeneralIndex M G₁ randomBound ×
      (machineStore qS).Value (cryptoBase F G₁ G₂ M M))) ∈
        support ((code rep bd ports sampler data samplingCode cost primitive qS).run control queryCost (i, saved)) := by
  rw [code_executed_run, support_map]
  exact ⟨z, hz, rfl⟩

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)
  (lists : ListSizeLaws Q rep.data header)

include sizes lists

/-- The store bound is linear in the cache cap, with independently fixed
message, scalar, coin, and challenge-point widths. -/
theorem code_stateInvariant (qS messageWidth initialWidth scalarWidth coinWidth groupWidth cap : Nat)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : ∀ x : G₁, Q.size (rep.ty point₁) x ≤ groupWidth)
    (i : GeneralRequest M randomBound)
    (hi : RequestMessages (fun m => Q.size (rep.ty message) m ≤ messageWidth) i)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hs : StateInvariant (Q := Q) rep qS messageWidth initialWidth cap saved)
    (z : Run (GeneralIndex M G₁ randomBound × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((code rep bd ports sampler data samplingCode cost primitive qS).run control queryCost (i, saved))) :
    StateInvariant (Q := Q) rep qS messageWidth
      (storeWidth header messageWidth scalarWidth coinWidth groupWidth (cap + 1)) (cap + 1) z.value.2 := by
  obtain ⟨state', he, hm, hn⟩ := code_stateFacts rep bd ports sampler data samplingCode cost primitive control queryCost
    qS saved.1.1 saved.1.2.1 saved.1.2.2 (fun m => Q.size (rep.ty message) m ≤ messageWidth)
    (machineCaches saved) hs.2.1 i hi z hz
  have hn' := hn.trans (Nat.add_le_add_right hs.2.2 1)
  have hw := machineState_encoded_size rep sizes lists qS saved.1.1 saved.1.2.1 saved.1.2.2 state'
    messageWidth scalarWidth coinWidth groupWidth (cap + 1) hm hf hc (hg _) (hg _) (hg _) hn'
  rw [he]
  exact ⟨hw, hm, hn'⟩

/-- Remaining fuel reserves room for future requests. Message width is
independent of the store and temporary-frame width. -/
def ReservedState (qS messageWidth width cap remaining : Nat)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) : Prop :=
  Q.size (rep.ty (machineStore qS)) saved ≤ width ∧
    (machineCaches saved).Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth) ∧
    (machineCaches saved).size + remaining ≤ cap

theorem code_reservedState (qS messageWidth width scalarWidth coinWidth groupWidth cap remaining : Nat)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : ∀ x : G₁, Q.size (rep.ty point₁) x ≤ groupWidth)
    (hw : storeWidth header messageWidth scalarWidth coinWidth groupWidth cap ≤ width)
    (i : GeneralRequest M randomBound)
    (hi : RequestMessages (fun m => Q.size (rep.ty message) m ≤ messageWidth) i)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hs : ReservedState (Q := Q) rep qS messageWidth width cap (remaining + 1) saved)
    (z : Run (GeneralIndex M G₁ randomBound × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((code rep bd ports sampler data samplingCode cost primitive qS).run control queryCost (i, saved))) :
    ReservedState (Q := Q) rep qS messageWidth width cap remaining z.value.2 := by
  obtain ⟨state', he, hm, hn⟩ := code_stateFacts rep bd ports sampler data samplingCode cost primitive control queryCost
    qS saved.1.1 saved.1.2.1 saved.1.2.2 (fun m => Q.size (rep.ty message) m ≤ messageWidth)
    (machineCaches saved) hs.2.1 i hi z hz
  have hn' : state'.size + remaining ≤ cap := by have := hs.2.2; omega
  have hsize := machineState_encoded_size rep sizes lists qS saved.1.1 saved.1.2.1 saved.1.2.2 state'
    messageWidth scalarWidth coinWidth groupWidth cap hm hf hc (hg _) (hg _) (hg _) (by omega)
  rw [he]
  exact ⟨hsize.trans hw, hm, hn'⟩

variable [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {overhead : Nat → Nat} (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (localLaws : LocalCostLaws Q overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))

include mono routing localLaws dispatchLaws dataLaws

/-- A complete per-request certificate for the exact native handler used by
caller composition. Runtime uses a common global frame cap; cache provenance
and storage use fixed smaller message/value widths and the remaining fuel. -/
theorem executed_reserved_bound
    (qS messageWidth width scalarWidth coinWidth groupWidth cap remaining : Nat)
    (comparisonTime scalarTime coinTime opTime adapterTime dynamicTime : Nat)
    (hh : header ≤ width) (hm : messageWidth ≤ width)
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : ∀ x : G₁, Q.size (rep.ty point₁) x ≤ groupWidth)
    (hw : storeWidth header messageWidth scalarWidth coinWidth groupWidth cap ≤ width)
    (caps : PortCaps rep bd ports width adapterTime)
    (dynamicSamples : DynamicSamplingCaps rep bd ports sampler control queryCost width dynamicTime)
    (values : NativeValueCaps (Q := Q) rep qS width)
    (ops : NativeInstructionCaps rep cost primitive primitiveBound qS width comparisonTime opTime)
    (samples : NativeSamplingCaps rep samplingCode control queryCost qS scalarTime coinTime)
    (i : GeneralRequest M randomBound) (hi : RequestSized (Q := Q) rep width i)
    (hiMessage : RequestMessages (fun m => Q.size (rep.ty message) m ≤ messageWidth) i)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hs : ReservedState (Q := Q) rep qS messageWidth width cap (remaining + 1) saved)
    (z : Run ((generalSpec M G₁ randomBound).Range i) × (machineStore qS).Value (cryptoBase F G₁ G₂ M M))
    (hz : z ∈ support ((executed rep bd ports sampler data samplingCode cost primitive control queryCost qS i).run saved)) :
    ReservedState (Q := Q) rep qS messageWidth width cap remaining z.2 ∧
      Q.size bd.idx ⟨i, z.1.value⟩ ≤ 8 * width ∧
      z.1.steps ≤ nativeHandlerTime overhead width cap comparisonTime scalarTime coinTime opTime adapterTime dynamicTime := by
  have hmem := executed_mem_code rep bd ports sampler data samplingCode cost primitive control queryCost qS i saved z hz
  have hsmall : StateInvariant (Q := Q) rep qS messageWidth width cap saved :=
    ⟨hs.1, hs.2.1, by have := hs.2.2; omega⟩
  have hwide := StateInvariant.mono rep qS messageWidth width cap width width cap saved hsmall hm le_rfl le_rfl
  have hb := code_bound rep bd ports sampler control queryCost sizes mono routing data samplingCode cost primitive
    localLaws dispatchLaws lists dataLaws primitiveBound qS width cap comparisonTime scalarTime coinTime opTime
    adapterTime dynamicTime hh caps dynamicSamples values ops samples (i, saved) ⟨hi, hwide⟩ _ hmem
  have hs' := code_reservedState rep bd ports sampler data samplingCode cost primitive control queryCost sizes lists
    qS messageWidth width scalarWidth coinWidth groupWidth cap remaining hf hc hg hw i hiMessage saved hs _ hmem
  exact ⟨hs', hb.1.1, hb.2⟩

end Signatures.Runtime.Coron.NativeHandler

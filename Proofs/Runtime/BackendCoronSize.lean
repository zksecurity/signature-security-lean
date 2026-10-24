import Proofs.Runtime.BackendCoron
import Proofs.Runtime.BackendDataSize
import Proofs.Runtime.CacheInvariant

/-! Reachable message and encoded-store bounds for the lazy Coron wrapper.
The key type remains arbitrary. Only encountered messages need a size bound;
sampling finite scalars/coins and group outputs uses their encoding contracts.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Coron

open BackendProgram

def CacheState.Messages {F M : Type} {qS : Nat} (valid : M → Prop)
    (state : CacheState F M qS) : Prop :=
  (∀ p ∈ state.scalars, valid p.1) ∧ (∀ p ∈ state.coins, valid p.1) ∧
    ∀ m ∈ state.signed, valid m

theorem CacheState.messages_empty {F M : Type} {qS : Nat} (valid : M → Prop) :
    (CacheState.empty : CacheState F M qS).Messages valid := by
  simp [CacheState.Messages, CacheState.empty]

section Semantics

variable {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]

theorem reply_messages (cost : PrimitiveCosts) (sampling : SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (valid : M → Prop)
    (state : CacheState F M qS) (hm : valid m) (hs : state.Messages valid)
    (z : Run G₁ × CacheState F M qS)
    (hz : z ∈ support ((reply (G₂ := G₂) cost sampling g X h qS signing m).run state)) :
    z.2.Messages valid := by
  simp only [reply, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨rho, hrho, coin, hcoin, rfl⟩ := hz
  have hr := cacheHandler_keys (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.scalar (fun _ _ => rfl) valid m 0 state.scalars hm hs.1 rho hrho
  have hc := cacheHandler_keys (arithmetic F G₁ G₂ M M cost) (draws qS sampling)
    CryptoOp.messageEq Draw.coin (fun _ _ => rfl) valid m 0 state.coins hm hs.2.1 coin hcoin
  refine ⟨hr, hc, ?_⟩
  cases signing <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact hs.2.2
  · intro m' hm'
    rcases List.mem_cons.mp hm' with rfl | hm'
    · exact hm
    · exact hs.2.2 m' hm'

end Semantics

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

/-- Three challenge points and three lists, with every pair/list header charged.
The count is the maximum of the three list lengths, so repeated signatures are
included even when no new private hash or coin entry is created. -/
def storeWidth (header messageWidth scalarWidth coinWidth groupWidth cap : Nat) : Nat :=
  3 * groupWidth + 8 * header + cap * (3 * messageWidth + scalarWidth + coinWidth + 5 * header)

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header)
  (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem machineState_encoded_size (qS : Nat) (g X h : G₁) (state : CacheState F M qS)
    (messageWidth scalarWidth coinWidth groupWidth cap : Nat)
    (hm : state.Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth))
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : Q.size (rep.ty point₁) g ≤ groupWidth)
    (hX : Q.size (rep.ty point₁) X ≤ groupWidth)
    (hh : Q.size (rep.ty point₁) h ≤ groupWidth) (hn : state.size ≤ cap) :
    Q.size (rep.ty (machineStore qS)) (machineState g X h state) ≤
      storeWidth header messageWidth scalarWidth coinWidth groupWidth cap := by
  have hsc : state.scalars.length ≤ cap := (Nat.le_max_left _ _).trans hn
  have hco : state.coins.length ≤ cap :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans hn
  have hsi : state.signed.length ≤ cap :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans hn
  have hscalar := lists.size_le_cap (rep.ty (.pair message scalar)) state.scalars
    (messageWidth + scalarWidth + header) cap (by
      intro p hp
      have h := sizes.prod_le (rep.ty message) (rep.ty scalar) p
      have h1 := hm.1 p hp
      have h2 := hf p.2
      exact h.trans (by omega)) hsc
  have hcoin := lists.size_le_cap (rep.ty (.pair message (boundedNat qS))) state.coins
    (messageWidth + coinWidth + header) cap (by
      intro p hp
      have h := sizes.prod_le (rep.ty message) (rep.ty (boundedNat qS)) p
      have h1 := hm.2.1 p hp
      have h2 := hc p.2
      exact h.trans (by omega)) hco
  have hsigned := lists.size_le_cap (rep.ty message) state.signed messageWidth cap hm.2.2 hsi
  have hpoints := sizes.prod_le (rep.ty point₁) (rep.ty point₁) (X, h)
  have hchallenge := sizes.prod_le (rep.ty point₁) (rep.ty (.pair point₁ point₁)) (g, X, h)
  have htail := sizes.prod_le (rep.ty (.list (.pair message (boundedNat qS))))
    (rep.ty (.list message)) (state.coins, state.signed)
  have hcaches := sizes.prod_le (rep.ty (.list (.pair message scalar)))
    (rep.ty (.pair (.list (.pair message (boundedNat qS))) (.list message)))
      (state.scalars, state.coins, state.signed)
  have hstore := sizes.prod_le (rep.ty (.pair point₁ (.pair point₁ point₁)))
    (rep.ty (.pair (.list (.pair message scalar))
      (.pair (.list (.pair message (boundedNat qS))) (.list message))))
        ((g, X, h), state.scalars, state.coins, state.signed)
  dsimp only [machineState, machineStore, LanguageRepresentation.ty, storeWidth] at *
  nlinarith

section Execution

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

omit sizes lists [C.HasOption] in
theorem backendReply_state_invariant (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (valid : M → Prop)
    (state : CacheState F M qS) (hm : valid m) (hs : state.Messages valid)
    (z : Run (G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((backendReply rep data samplingCode cost primitive qS signing).run
      control queryCost (m, machineState g X h state))) :
    ∃ state' : CacheState F M qS, z.value.2 = machineState g X h state' ∧
      state'.Messages valid ∧ state'.size ≤ state.size + 1 := by
  have hv := Code.value_mem_denote control queryCost
    (backendReply rep data samplingCode cost primitive qS signing) (m, machineState g X h state) z hz
  rw [backendReply_denote rep data samplingCode cost primitive sampling, support_map] at hv
  obtain ⟨r, hr, he⟩ := hv
  refine ⟨r.2, congrArg Prod.snd he.symm, ?_, ?_⟩
  · exact reply_messages cost (machineSampling sampling qS) g X h qS signing m valid state hm hs r hr
  · exact (reply_bound (G₂ := G₂) cost (machineSampling sampling qS) g X h qS signing m state r hr).1

theorem backendReply_encoded_size (sampling : Machine.SamplingCosts)
    (g X h : G₁) (qS : Nat) (signing : Bool) (m : M) (state : CacheState F M qS)
    (messageWidth scalarWidth coinWidth groupWidth cap : Nat)
    (hm : Q.size (rep.ty message) m ≤ messageWidth)
    (hs : state.Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth))
    (hf : ∀ x : F, Q.size (rep.ty scalar) x ≤ scalarWidth)
    (hc : ∀ x : Fin (qS + 1), Q.size (rep.ty (boundedNat qS)) x ≤ coinWidth)
    (hg : ∀ x : G₁, Q.size (rep.ty point₁) x ≤ groupWidth) (hn : state.size ≤ cap)
    (z : Run (G₁ × (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((backendReply rep data samplingCode cost primitive qS signing).run
      control queryCost (m, machineState g X h state))) :
    (machineCaches z.value.2).Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth) ∧
      Q.size (rep.ty (machineStore qS)) z.value.2 ≤
        storeWidth header messageWidth scalarWidth coinWidth groupWidth (cap + 1) ∧
      Q.size (StepClass.HasProd.prod (rep.ty point₁) (rep.ty (machineStore qS))) z.value ≤
        groupWidth + storeWidth header messageWidth scalarWidth coinWidth groupWidth (cap + 1) + header := by
  obtain ⟨state', he, hmessages, hcount⟩ := backendReply_state_invariant rep data samplingCode cost primitive
    control queryCost sampling g X h qS signing m _ state hm hs z hz
  have hsize := machineState_encoded_size rep sizes lists qS g X h state'
    messageWidth scalarWidth coinWidth groupWidth (cap + 1) hmessages hf hc (hg g) (hg X) (hg h) (by omega)
  have hp := sizes.prod_le (rep.ty point₁) (rep.ty (machineStore qS)) z.value
  have ho := hg z.value.1
  rw [he] at hp ⊢
  exact ⟨hmessages, hsize, by omega⟩

end Execution
end Signatures.Runtime.Coron

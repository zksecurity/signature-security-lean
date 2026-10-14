import Signatures.Runtime.BackendWeightedOracle
import Signatures.Runtime.BackendWeightedStateSize
import Signatures.Runtime.BackendWeightedSignInputs
import Signatures.Runtime.BackendLazyAGMExtractionState

/-! Capacities for every adaptive native weighted reply. Each remaining query
reserves a full term list in the private cache and one explicit reply token.
Stored keys/messages keep a fixed width bound independently of aggregate stores.
The challenge configuration is preserved, including on cache misses. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram Reply

def handlerStoreWidth (index : Index) (width cap : Nat) : Nat :=
  (32 * cap * (index.bound + 1) + 32) * width

theorem handlerStoreWidth_ge (index : Index) (width cap : Nat) :
    8 * width ≤ handlerStoreWidth index width cap :=
  Nat.mul_le_mul_right width (by omega)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)) (index : Index)

def ReservedState {value config : Ty CryptoAtom} (width cap remaining : Nat)
    (saved : (storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  State.Entries (fun k => Q.size (rep.ty index.ty) k ≤ 5 * width)
      (fun m => Q.size (rep.ty index.messageTy) m ≤ 5 * width) saved.2 ∧
    saved.2.1.length + remaining * (index.bound + 1) ≤ cap * (index.bound + 1) ∧
    saved.2.2.1.length + saved.2.2.2.length + remaining ≤ cap

omit [C.HasSum] in
theorem reserved_weaken {value config : Ty CryptoAtom} (width cap a b : Nat) (hab : a ≤ b)
    (saved : (storeTy index.ty index.messageTy value config).Value (cryptoBase F G₁ G₂ K M))
    (hs : ReservedState (Q := Q) rep index width cap b saved) :
    ReservedState (Q := Q) rep index width cap a saved := by
  have hmul := Nat.mul_le_mul_right (index.bound + 1) hab
  exact ⟨hs.1, by have := hs.2.1; omega, by have := hs.2.2; omega⟩

omit [C.HasSum] in
theorem reserved_empty {value config : Ty CryptoAtom} (width cap fuel : Nat) (h : fuel ≤ cap)
    (cfg : config.Value (cryptoBase F G₁ G₂ K M)) :
    ReservedState (Q := Q) rep index (value := value) width cap fuel (cfg, [], [], []) := by
  exact ⟨⟨by simp, by simp, by simp⟩, by simpa using Nat.mul_le_mul_right (index.bound + 1) h, by simpa using h⟩

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem goodReserved_size (width cap remaining : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (saved : (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hs : ReservedState (Q := Q) rep index width cap remaining saved) :
    Q.size (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy)) saved ≤ handlerStoreWidth index width cap := by
  have h := goodStore_encoded_size rep sizes lists saved.1.1 saved.1.2 saved.2
    (5 * width) width width (cap * (index.bound + 1)) cap hs.1 hf hg
    (by have := hs.2.1; omega) (by have := hs.2.2; omega)
  have hmul := Nat.mul_le_mul_left (cap * (index.bound + 1)) hh
  have hmul' := Nat.mul_le_mul_left cap hh
  dsimp only [handlerStoreWidth]
  nlinarith only [h, hmul, hmul', hh, Nat.zero_le (cap * index.bound * width)]

theorem badReserved_size (width cap remaining : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (saved : (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hs : ReservedState (Q := Q) rep index width cap remaining saved) :
    Q.size (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) saved ≤ handlerStoreWidth index width cap := by
  have h := badStore_encoded_size rep sizes lists saved.1.2.1 saved.1.2.2 saved.1.1 saved.2
    (5 * width) width width (cap * (index.bound + 1)) cap hs.1 hf hg
    (by have := hs.2.1; omega) (by have := hs.2.2; omega)
  have hmul := Nat.mul_le_mul_left (cap * (index.bound + 1)) hh
  have hmul' := Nat.mul_le_mul_left cap hh
  dsimp only [handlerStoreWidth]
  nlinarith only [h, hmul, hmul', hh, Nat.zero_le (cap * index.bound * width)]

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

omit sizes lists [C.HasOption] in
theorem goodHash_reserved (width cap remaining : Nat)
    (m : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hm : Q.size (rep.ty index.ty) m ≤ width)
    (hs : ReservedState (Q := Q) rep index width cap (remaining + 1) saved)
    (z : Run (G₁ × (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((Reply.goodHash rep data cost primitive sampling index).run control queryCost (m, saved))) :
    z.value.2.1 = saved.1 ∧ ReservedState (Q := Q) rep index width cap remaining z.value.2 := by
  have h := Code.value_mem_denote control queryCost (Reply.goodHash rep data cost primitive sampling index)
    (m, saved) z hz
  rw [Reply.goodHash_denote] at h
  simp only [support_map, Set.mem_image] at h
  obtain ⟨p, hp, he⟩ := h
  rw [← he]
  have hc := LazyAGM.privateRead_messages (fun k => Q.size (rep.ty index.ty) k ≤ 5 * width)
    m saved.2.1 (hm.trans (by omega)) hs.1.1 p hp
  have hgrow := (Model.LazyAGM.WeightedReduction.listLookup_preserves m saved.2.1 p hp).2.2
  refine ⟨rfl, ⟨hc, ?_, hs.1.2.2⟩, ?_, ?_⟩
  · intro entry he
    rcases List.mem_cons.mp he with he | he
    · subst entry; exact hm.trans (by omega)
    · exact hs.1.2.1 entry he
  · have hi := hs.2.1
    dsimp only
    nlinarith
  · have hi := hs.2.2
    simpa only [Reply.record, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

omit lists in
theorem goodSign_reserved (width cap remaining : Nat)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hs : ReservedState (Q := Q) rep index width cap (remaining + 1) saved)
    (z : Run (G₁ × (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((Reply.goodSign rep data cost primitive sampling index).run control queryCost (m, saved))) :
    z.value.2.1 = saved.1 ∧ ReservedState (Q := Q) rep index width cap remaining z.value.2 := by
  have h := Code.value_mem_denote control queryCost (Reply.goodSign rep data cost primitive sampling index)
    (m, saved) z hz
  rw [Reply.goodSign_denote] at h
  simp only [support_map, Set.mem_image] at h
  obtain ⟨p, hp, he⟩ := h
  rw [← he]
  have hrows := index.terms_rows_size rep cost sizes m width hh hm hf hj
  have hkeys : ∀ row ∈ index.sourceTerms cost m, Q.size (rep.ty index.ty) row.1 ≤ 5 * width := by
    intro row hr
    exact (sizes.fst_le (rep.ty index.ty) (rep.ty scalar) row).trans (hrows row hr)
  have hc := LazyAGM.privateTerms_state (fun k => Q.size (rep.ty index.ty) k ≤ 5 * width)
    (index.sourceTerms cost m) saved.2.1 hkeys hs.1.1 p hp
  have hlength := index.terms_length (G₁ := G₁) (G₂ := G₂) (M := M) cost m
  refine ⟨rfl, ⟨hc.2, hs.1.2.1, ?_⟩, ?_, ?_⟩
  · intro entry he
    rcases List.mem_cons.mp he with he | he
    · subst entry; exact hm.trans (by omega)
    · exact hs.1.2.2 entry he
  · have hgrow := hc.1
    have hi := hs.2.1
    dsimp only
    rw [hlength] at hgrow
    nlinarith
  · have hi := hs.2.2
    simpa only [Reply.record, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

omit sizes lists [C.HasOption] in
theorem badHash_reserved (width cap remaining : Nat)
    (m : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hm : Q.size (rep.ty index.ty) m ≤ width)
    (hs : ReservedState (Q := Q) rep index width cap (remaining + 1) saved)
    (z : Run (G₁ × (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((Reply.badHash rep data cost primitive sampling index).run control queryCost (m, saved))) :
    z.value.2.1 = saved.1 ∧ ReservedState (Q := Q) rep index width cap remaining z.value.2 := by
  have h := Code.value_mem_denote control queryCost (Reply.badHash rep data cost primitive sampling index)
    (m, saved) z hz
  rw [Reply.badHash_denote] at h
  simp only [support_map, Set.mem_image] at h
  obtain ⟨p, hp, he⟩ := h
  rw [← he]
  have hc := LazyAGM.privateRead_messages (fun k => Q.size (rep.ty index.ty) k ≤ 5 * width)
    m saved.2.1 (hm.trans (by omega)) hs.1.1 p hp
  have hgrow := (Model.LazyAGM.WeightedReduction.listLookup_preserves m saved.2.1 p hp).2.2
  refine ⟨rfl, ⟨hc, ?_, hs.1.2.2⟩, ?_, ?_⟩
  · intro entry he
    rcases List.mem_cons.mp he with he | he
    · subst entry; exact hm.trans (by omega)
    · exact hs.1.2.1 entry he
  · have hi := hs.2.1
    dsimp only
    nlinarith
  · have hi := hs.2.2
    simpa only [Reply.record, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

omit lists in
theorem badSign_reserved (width cap remaining : Nat)
    (m : index.messageTy.Value (cryptoBase F G₁ G₂ K M))
    (saved : (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M))
    (hm : Q.size (rep.ty index.messageTy) m ≤ width)
    (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hj : ∀ j : Fin (index.bound + 1), Q.size (rep.ty (boundedNat index.bound)) j ≤ width)
    (hs : ReservedState (Q := Q) rep index width cap (remaining + 1) saved)
    (z : Run (G₁ × (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((Reply.badSign rep data cost primitive sampling index).run control queryCost (m, saved))) :
    z.value.2.1 = saved.1 ∧ ReservedState (Q := Q) rep index width cap remaining z.value.2 := by
  have h := Code.value_mem_denote control queryCost (Reply.badSign rep data cost primitive sampling index)
    (m, saved) z hz
  rw [Reply.badSign_denote] at h
  simp only [support_map, Set.mem_image] at h
  obtain ⟨p, hp, he⟩ := h
  rw [← he]
  have hrows := index.terms_rows_size rep cost sizes m width hh hm hf hj
  have hkeys : ∀ row ∈ index.sourceTerms cost m, Q.size (rep.ty index.ty) row.1 ≤ 5 * width := by
    intro row hr
    exact (sizes.fst_le (rep.ty index.ty) (rep.ty scalar) row).trans (hrows row hr)
  have hc := LazyAGM.privateTerms_state (fun k => Q.size (rep.ty index.ty) k ≤ 5 * width)
    (index.sourceTerms cost m) saved.2.1 hkeys hs.1.1 p hp
  have hlength := index.terms_length (G₁ := G₁) (G₂ := G₂) (M := M) cost m
  refine ⟨rfl, ⟨hc.2, hs.1.2.1, ?_⟩, ?_, ?_⟩
  · intro entry he
    rcases List.mem_cons.mp he with he | he
    · subst entry; exact hm.trans (by omega)
    · exact hs.1.2.2 entry he
  · have hgrow := hc.1
    have hi := hs.2.1
    dsimp only
    rw [hlength] at hgrow
    nlinarith
  · have hi := hs.2.2
    simpa only [Reply.record, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

end Signatures.Runtime.WeightedAGM.NativeHandler

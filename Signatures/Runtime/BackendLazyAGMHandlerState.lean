import Signatures.Runtime.BackendLazyAGMHandler
import Signatures.Runtime.BackendLazyAGMStateSize

/-! Store invariants for adaptive native AGM dispatch. Cache and transcript
capacities each reserve space for remaining requests. Message widths stay fixed
while aggregate store widths grow only with encountered entries. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM.NativeHandler

open BackendProgram

def handlerStoreWidth (width cap : Nat) : Nat := (12 * cap + 16) * width

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))

def ReservedState {value config : Ty CryptoAtom} (width cap remaining : Nat)
    (saved : (storeTy value config).Value (cryptoBase F G₁ G₂ M M)) : Prop :=
  State.Messages (fun m => Q.size (rep.ty message) m ≤ width) saved.2 ∧
    saved.2.1.length + remaining ≤ cap ∧
    saved.2.2.1.length + saved.2.2.2.length + remaining ≤ cap

omit [C.HasSum] in
theorem reserved_weaken {value config : Ty CryptoAtom} (width cap a b : Nat) (hab : a ≤ b)
    (saved : (storeTy value config).Value (cryptoBase F G₁ G₂ M M))
    (hs : ReservedState (Q := Q) rep width cap b saved) :
    ReservedState (Q := Q) rep width cap a saved :=
  ⟨hs.1, by have := hs.2.1; omega, by have := hs.2.2; omega⟩

variable [C.HasOption] {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem goodReserved_size (width cap remaining : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (saved : (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hs : ReservedState (Q := Q) rep width cap remaining saved) :
    Q.size (rep.ty (storeTy scalar goodConfigTy)) saved ≤ handlerStoreWidth width cap := by
  have h := goodStore_encoded_size rep sizes lists saved.1.1 saved.1.2 saved.2
    width width width cap cap hs.1 hf hg (by have := hs.2.1; omega) (by have := hs.2.2; omega)
  have hmul := Nat.mul_le_mul_left cap hh
  dsimp only [handlerStoreWidth]
  nlinarith only [h, hmul, hh]

theorem badReserved_size (width cap remaining : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (saved : (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hs : ReservedState (Q := Q) rep width cap remaining saved) :
    Q.size (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) saved ≤ handlerStoreWidth width cap := by
  have h := badStore_encoded_size rep sizes lists saved.1.2.1 saved.1.2.2 saved.1.1 saved.2
    width width width cap cap hs.1 hf hg (by have := hs.2.1; omega) (by have := hs.2.2; omega)
  have hmul := Nat.mul_le_mul_left cap hh
  dsimp only [handlerStoreWidth]
  nlinarith only [h, hmul, hh]

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  [Field F] [SampleableType F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

omit sizes lists [C.HasOption] in
theorem goodReply_reserved (width cap remaining : Nat) (signing : Bool) (m : M)
    (saved : (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : ReservedState (Q := Q) rep width cap (remaining + 1) saved)
    (z : Run (G₁ × (storeTy scalar goodConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((backendGoodReply rep data cost primitive sampling signing).run control queryCost (m, saved))) :
    z.value.2.1 = saved.1 ∧ ReservedState (Q := Q) rep width cap remaining z.value.2 := by
  have h := backendReply_state rep data cost primitive sampling.scalar (sampling.scalar_denote ())
    (.op .zero .unit) (goodResponse signing) control queryCost signing m saved.1 saved.2
    (fun m => Q.size (rep.ty message) m ≤ width) hs.1 hm z (by rw [backendGoodReply] at hz; exact hz)
  exact ⟨h.1, h.2.1, by have := hs.2.1; have := h.2.2.1; omega,
    by have := hs.2.2; have := h.2.2.2; omega⟩

omit sizes lists [C.HasOption] in
theorem badReply_reserved (width cap remaining : Nat) (signing : Bool) (m : M)
    (saved : (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M))
    (hm : Q.size (rep.ty message) m ≤ width)
    (hs : ReservedState (Q := Q) rep width cap (remaining + 1) saved)
    (z : Run (G₁ × (storeTy (.pair scalar scalar) badConfigTy).Value (cryptoBase F G₁ G₂ M M)))
    (hz : z ∈ support ((backendBadReply rep data cost primitive sampling signing).run control queryCost (m, saved))) :
    z.value.2.1 = saved.1 ∧ ReservedState (Q := Q) rep width cap remaining z.value.2 := by
  have h := backendReply_state rep data cost primitive (pairSampler rep data sampling) (pairSampler_denote rep data sampling ())
    (.pair (.op .zero .unit) (.op .zero .unit)) (badResponse signing) control queryCost signing m saved.1 saved.2
    (fun m => Q.size (rep.ty message) m ≤ width) hs.1 hm z (by rw [backendBadReply] at hz; exact hz)
  exact ⟨h.1, h.2.1, by have := hs.2.1; have := h.2.2.1; omega,
    by have := hs.2.2; have := h.2.2.2; omega⟩

end Signatures.Runtime.LazyAGM.NativeHandler

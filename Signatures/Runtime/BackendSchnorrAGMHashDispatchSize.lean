import Signatures.Runtime.BackendSchnorrAGMHashDispatch

/-! Size contracts for all hash-request shapes. Both list lengths and every
coefficient row contribute to the retained input, including malformed data. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HashDispatch

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

structure Input (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  message_size : Q.size (rep.ty message) input.1 ≤ width
  group_size : ∀ g ∈ input.2.1, Q.size (rep.ty point₁) g ≤ width
  group_length : input.2.1.length ≤ groupCap
  row_length : input.2.2.1.length ≤ rowCap
  coefficient_length : ∀ row ∈ input.2.2.1, row.length ≤ coeffCap
  state : Read.StateBound (Q := Q) rep (3 * width) cap historyWidth input.2.2.2
  basis_length : input.2.2.2.2.1.length ≤ basisCap

def frameWidth (width cap historyWidth groupCap rowCap coeffCap : Nat) : Nat :=
  Read.frameWidth (3 * width) cap historyWidth +
    (4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128) * width

include sizes

theorem decoded_property [Field F] [Zero G₁]
    (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap (prepareValue input).2 := by
  have hgroup := ListSingleton.value_property (fun g => Q.size (rep.ty point₁) g ≤ width)
    (0 : G₁) input.2.1 hg hi.group_size
  have hrow := ListSingleton.value_property (fun row : List F => row.length ≤ coeffCap)
    [] input.2.2.1 (by simp) hi.coefficient_length
  refine ⟨?_, hi.state, hi.basis_length, hrow⟩
  have hp := sizes.prod_le (rep.ty message) (rep.ty point₁)
    (input.1, (ListSingleton.value (0 : G₁) input.2.1).2)
  have hm := hi.message_size
  dsimp only at hp
  exact hp.trans (by omega)

include lists

omit [C.HasSum] [C.HasOption] sizes in
theorem coefficient_size (width coeffCap : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (row : List F) (hr : row.length ≤ coeffCap) :
    Q.size (rep.ty (.list scalar)) row ≤ (2 * coeffCap + 1) * width := by
  have h := lists.size_le_cap (rep.ty scalar) row width coeffCap (fun f _ => hf f) hr
  have hh' := Nat.mul_le_mul_left coeffCap hh
  change Q.size (rep.ty (.list scalar)) row ≤ _ at h
  nlinarith

theorem input_size (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Q.size (rep.ty inputTy) input ≤ frameWidth width cap historyWidth groupCap rowCap coeffCap ∧
      Q.size (rep.env [inputTy]) (input, ()) ≤ frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have hgroups := lists.size_le_cap (rep.ty point₁) input.2.1 width groupCap hi.group_size hi.group_length
  have hrows := lists.size_le_cap (rep.ty (.list scalar)) input.2.2.1
    ((2 * coeffCap + 1) * width) rowCap
    (fun row hr => coefficient_size rep lists width coeffCap hh hf row (hi.coefficient_length row hr)) hi.row_length
  have hcache := CacheCompiler.list_size rep sizes lists input.2.2.2.1 (5 * (3 * width)) cap
    (by omega) hi.state.1 hi.state.2.1
  have hmeta := Read.history_size rep sizes width historyWidth hh hb input.2.2.2.2 hi.state.2.2
  have hm := hi.message_size
  have hgheader := Nat.mul_le_mul_left groupCap hh
  have hrheader := Nat.mul_le_mul_left rowCap hh
  have hprod := @sizes.prod_le
  dsimp only [frameWidth, Read.frameWidth, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  constructor <;> grind only

theorem prepare_size [Field F] [Zero G₁]
    (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Q.size (rep.ty preparedTy) (prepareValue input) ≤ frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have hd := decoded_property rep sizes width cap historyWidth basisCap groupCap rowCap coeffCap hh hg input hi
  have hp := (Hash.input_size rep sizes lists width cap historyWidth basisCap coeffCap hh hu hb hf _ hd).1
  have h := sizes.prod_le rep.data.bool (rep.ty Hash.inputTy) (prepareValue input)
  have hflag := hb (prepareValue input).1
  have hpadding := Nat.mul_le_mul_right width (show 4 * coeffCap + 66 ≤
    4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
  have hmargin : Hash.frameWidth width cap coeffCap historyWidth + 2 * width ≤
      frameWidth width cap historyWidth groupCap rowCap coeffCap := by
    dsimp only [frameWidth, Hash.frameWidth]
    nlinarith
  exact h.trans (by omega)

omit [C.HasSum] [C.HasOption] sizes lists in
theorem reject_property [Zero F] (width cap historyWidth basisCap coeffCap : Nat)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (input : Hash.inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap input) :
    Read.Output (Q := Q) rep (3 * width) (cap + 1) historyWidth (rejectValue input) ∧
      (rejectValue input).2.2.1.length ≤ basisCap := by
  exact ⟨⟨hz.trans (by omega), hi.2.1.1, hi.2.1.2.1.trans (by omega), hi.2.1.2.2⟩, hi.2.2.1⟩

end Signatures.Runtime.SchnorrAGM.Native.HashDispatch

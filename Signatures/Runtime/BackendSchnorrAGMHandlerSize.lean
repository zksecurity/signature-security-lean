import Signatures.Runtime.BackendSchnorrAGMHandlerComponents

/-! Shared invariants for the installed Schnorr AGM handlers. The original
request, every coefficient row and the fixed generator/public key are included.
History bounds count cells; conversion to the read invariant does not inflate
the bound each time a hash request is executed. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HandlerComponents

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure Config (width : Nat) (config : G₁ × G₁) : Prop where
  generator : Q.size (rep.ty point₁) config.1 ≤ width
  publicKey : Q.size (rep.ty point₁) config.2 ≤ width

structure StoreBound (width cap basisCap signedCap : Nat)
    (saved : (G₁ × G₁) × EncodedState F G₁ M) : Prop where
  config : Config (Q := Q) rep width saved.1
  state : Signing.StateBound (Q := Q) rep width cap basisCap signedCap saved.2

structure ArgsBound (value : Ty CryptoAtom) (width groupCap rowCap coeffCap : Nat)
    (args : (argsTy value).Value (cryptoBase F G₁ G₂ K M)) : Prop where
  data : Q.size (rep.ty value) args.1 ≤ width
  groups : args.2.1.length ≤ groupCap
  rows : args.2.2.length ≤ rowCap
  coefficients : ∀ row ∈ args.2.2, row.length ≤ coeffCap

def Input (value : Ty CryptoAtom) (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (input : (argsStoreTy (argsTy value)).Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  ArgsBound (Q := Q) rep value width groupCap rowCap coeffCap input.1 ∧
    StoreBound (Q := Q) rep width cap basisCap signedCap input.2

structure Output (value : Ty CryptoAtom) (width cap basisCap signedCap : Nat)
    (output : (resultTy (groupReplyTy value)).Value (cryptoBase F G₁ G₂ K M)) : Prop where
  data : Q.size (rep.ty value) output.1.1 ≤ width
  groups : ∀ g ∈ output.1.2, Q.size (rep.ty point₁) g ≤ width
  groupLength : output.1.2.length ≤ 1
  store : StoreBound (Q := Q) rep width cap basisCap signedCap output.2

def historyWidth (width basisCap signedCap : Nat) : Nat := (4 * basisCap + 2 * signedCap + 7) * width

def frameWidth (width cap basisCap signedCap groupCap rowCap coeffCap : Nat) : Nat :=
  HashDispatch.frameWidth width cap (historyWidth width basisCap signedCap) groupCap rowCap coeffCap +
    SigningDispatch.frameWidth width cap basisCap signedCap groupCap rowCap coeffCap + 128 * width

theorem store_mono (width cap basisCap signedCap cap' basisCap' signedCap' : Nat)
    (hc : cap ≤ cap') (hn : basisCap ≤ basisCap') (hs : signedCap ≤ signedCap')
    (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hi : StoreBound (Q := Q) rep width cap basisCap signedCap saved) :
    StoreBound (Q := Q) rep width cap' basisCap' signedCap' saved :=
  ⟨hi.config, hi.state.cache, hi.state.cacheLength.trans hc,
    hi.state.history.basisLength.trans hn, hi.state.history.signed, hi.state.history.signedLength.trans hs⟩

theorem random_input (width cap basisCap signedCap groupCap rowCap coeffCap arityCap : Nat)
    (input : (argsStoreTy randomArgsTy).Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep .nat width cap basisCap signedCap groupCap rowCap coeffCap input)
    (hn : input.1.1 ≤ arityCap) :
    Random.Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap
      (input.1.2.1, input.1.2.2, input.1.1, input.2.2) :=
  ⟨hn, hi.2.state, hi.1.groups, hi.1.rows, hi.1.coefficients⟩

theorem signing_input (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (input : (argsStoreTy groupArgsTy).Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap input) :
    SigningDispatch.Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap
      (input.1.2.1, input.1.2.2, input.2.1.1, input.2.1.2, input.1.1, input.2.2) :=
  ⟨⟨hi.2.config.generator, hi.2.config.publicKey, hi.1.data, hi.2.state⟩,
    hi.1.groups, hi.1.rows, hi.1.coefficients⟩

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem read_state (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (state : EncodedState F G₁ M) (hi : Signing.StateBound (Q := Q) rep width cap basisCap signedCap state) :
    Read.StateBound (Q := Q) rep (3 * width) cap (historyWidth width basisCap signedCap) state := by
  refine ⟨?_, hi.cacheLength, ?_, ?_⟩
  · simpa only [← Nat.mul_assoc, Nat.reduceMul] using hi.cache
  · exact (sizes.fst_le _ _ state.2).trans
      (Signing.history_size rep sizes lists width basisCap signedCap hh hb hf state.2 hi.history)
  · exact ((sizes.fst_le _ _ state.2.2).trans (sizes.snd_le _ _ state.2)).trans
      (Signing.history_size rep sizes lists width basisCap signedCap hh hb hf state.2 hi.history)

theorem hash_input (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (input : (argsStoreTy groupArgsTy).Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap input) :
    HashDispatch.Input (Q := Q) rep width cap (historyWidth width basisCap signedCap)
      basisCap groupCap rowCap coeffCap (input.1.1, input.1.2.1, input.1.2.2, input.2.2) :=
  ⟨hi.1.data, fun g _ => hg g, hi.1.groups, hi.1.rows, hi.1.coefficients,
    read_state rep sizes lists width cap basisCap signedCap hh hb hf input.2.2 hi.2.state,
    hi.2.state.history.basisLength⟩

omit lists in
theorem config_size (width : Nat) (hh : header ≤ width) (config : G₁ × G₁)
    (hi : Config (Q := Q) rep width config) : Q.size (rep.ty configTy) config ≤ 3 * width :=
  (sizes.prod_le (rep.ty point₁) (rep.ty point₁) config).trans (by have := hi.generator; have := hi.publicKey; omega)

theorem store_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hi : StoreBound (Q := Q) rep width cap basisCap signedCap saved) :
    Q.size (rep.ty storeTy) saved ≤ (60 * cap + 4 * basisCap + 2 * signedCap + 27) * width := by
  have hc := config_size rep sizes width hh saved.1 hi.config
  have hs := Signing.state_size rep sizes lists width cap basisCap signedCap hh hb hf saved.2 hi.state
  exact (sizes.prod_le (rep.ty configTy) (rep.ty stateTy) saved).trans (by nlinarith)

theorem args_size (value : Ty CryptoAtom) (width groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (args : (argsTy value).Value (cryptoBase F G₁ G₂ K M))
    (hi : ArgsBound (Q := Q) rep value width groupCap rowCap coeffCap args) :
    Q.size (rep.ty (argsTy value)) args ≤
      (2 * groupCap + 2 * rowCap * (coeffCap + 1) + 5) * width := by
  have hgroups := lists.size_le_cap (rep.ty point₁) args.2.1 width groupCap (fun g _ => hg g) hi.groups
  have hrows := lists.size_le_cap (rep.ty (.list scalar)) args.2.2 ((2 * coeffCap + 1) * width) rowCap
    (fun row hr => HashDispatch.coefficient_size rep lists width coeffCap hh hf row (hi.coefficients row hr)) hi.rows
  have hgheader := Nat.mul_le_mul_left groupCap hh
  have hrheader := Nat.mul_le_mul_left rowCap hh
  have hd := hi.data
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty] at *
  grind only

theorem input_size (value : Ty CryptoAtom) (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (input : (argsStoreTy (argsTy value)).Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep value width cap basisCap signedCap groupCap rowCap coeffCap input) :
    Q.size (rep.ty (argsStoreTy (argsTy value))) input ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap ∧
      Q.size (rep.env [argsStoreTy (argsTy value)]) (input, ()) ≤ frameWidth width cap basisCap signedCap groupCap rowCap coeffCap := by
  have ha := args_size rep sizes lists value width groupCap rowCap coeffCap hh hf hg input.1 hi.1
  have hs := store_size rep sizes lists width cap basisCap signedCap hh hb hf input.2 hi.2
  have hp := @sizes.prod_le
  have hsmall : Q.size (rep.env [argsStoreTy (argsTy value)]) (input, ()) ≤
      SigningDispatch.frameWidth width cap basisCap signedCap groupCap rowCap coeffCap := by
    dsimp only [SigningDispatch.frameWidth, Signing.frameWidth, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  have hinput := sizes.fst_le (rep.ty (argsStoreTy (argsTy value))) rep.data.unit (input, ())
  dsimp only [frameWidth]
  exact ⟨hinput.trans (hsmall.trans (by omega)), hsmall.trans (by omega)⟩

theorem output_size (value : Ty CryptoAtom) (width cap basisCap signedCap : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (output : (resultTy (groupReplyTy value)).Value (cryptoBase F G₁ G₂ K M))
    (ho : Output (Q := Q) rep value width (cap + 1) (basisCap + 1) (signedCap + 1) output) :
    Q.size (rep.ty (resultTy (groupReplyTy value))) output ≤ Signing.frameWidth width cap basisCap signedCap := by
  have hs := store_size rep sizes lists width (cap + 1) (basisCap + 1) (signedCap + 1) hh hb hf output.2 ho.store
  have hg := lists.size_le_cap (rep.ty point₁) output.1.2 width 1 ho.groups ho.groupLength
  have hd := ho.data
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, Signing.frameWidth] at *
  grind only

end Signatures.Runtime.SchnorrAGM.Native.HandlerComponents

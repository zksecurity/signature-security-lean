import Proofs.Runtime.BackendSchnorrAGMSigning

/-! Reachable representation bounds for accepted Schnorr signing. Capacity
parameters count encountered cache entries and chronological history cells;
there is no message-universe bound or constant-time list operation. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Signing

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

structure History (width basisCap signedCap : Nat) (metadata : Metadata F M) : Prop where
  basisLength : metadata.1.length ≤ basisCap
  signed : ∀ m ∈ metadata.2.1, Q.size (rep.ty message) m ≤ width
  signedLength : metadata.2.1.length ≤ signedCap

structure StateBound (width cap basisCap signedCap : Nat) (state : EncodedState F G₁ M) : Prop where
  cache : CacheCompiler.Entries (Q := Q) rep (key := cacheKeyTy) (val := entryTy) (15 * width) state.1
  cacheLength : state.1.length ≤ cap
  history : History (Q := Q) rep width basisCap signedCap state.2

structure Input (width cap basisCap signedCap : Nat)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  generator : Q.size (rep.ty point₁) input.1 ≤ width
  publicKey : Q.size (rep.ty point₁) input.2.1 ≤ width
  message : Q.size (rep.ty Signatures.Runtime.message) input.2.2.1 ≤ width
  state : StateBound (Q := Q) rep width cap basisCap signedCap input.2.2.2

structure Work (width cap basisCap signedCap : Nat)
    (input : workTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  cache : CacheCompiler.Input (Q := Q) rep (15 * width) cap input.1
  point : Q.size (rep.ty point₁) input.2.1.1 ≤ width
  scalar : Q.size (rep.ty Signatures.Runtime.scalar) input.2.1.2 ≤ width
  affine : Q.size (rep.ty affineTy) input.2.2.1 ≤ 3 * width
  message : Q.size (rep.ty Signatures.Runtime.message) input.2.2.2.1 ≤ width
  history : History (Q := Q) rep width basisCap signedCap input.2.2.2.2

structure Saved (width basisCap signedCap : Nat)
    (saved : savedTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  point : Q.size (rep.ty point₁) saved.1.1 ≤ width
  scalar : Q.size (rep.ty Signatures.Runtime.scalar) saved.1.2 ≤ width
  history : History (Q := Q) rep width basisCap signedCap saved.2

def ProgramInput (width cap basisCap signedCap : Nat)
    (input : programInputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  CacheCompiler.Input (Q := Q) rep (15 * width) cap input.1 ∧
    Saved (Q := Q) rep width (basisCap + 1) (signedCap + 1) input.2

def ProgramOutput (width cap basisCap signedCap : Nat)
    (input : programOutputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  (CacheCompiler.Entries (Q := Q) rep (15 * width) input.1 ∧ input.1.length ≤ cap + 1) ∧
    Saved (Q := Q) rep width (basisCap + 1) (signedCap + 1) input.2

structure Output (width cap basisCap signedCap : Nat)
    (input : outputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  point : Q.size (rep.ty point₁) input.1.1 ≤ width
  scalar : Q.size (rep.ty Signatures.Runtime.scalar) input.1.2 ≤ width
  state : StateBound (Q := Q) rep width (cap + 1) (basisCap + 1) (signedCap + 1) input.2

def frameWidth (width cap basisCap signedCap : Nat) : Nat :=
  (128 * cap + 16 * basisCap + 8 * signedCap + 256) * width

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes

theorem affine_size (width : Nat) (hh : header ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (a : F × F) :
    Q.size (rep.ty affineTy) a ≤ 3 * width := by
  exact (sizes.prod_le (rep.ty scalar) (rep.ty scalar) a).trans (by linarith [hf a.1, hf a.2])

include lists

theorem history_size (width basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (metadata : Metadata F M) (hi : History (Q := Q) rep width basisCap signedCap metadata) :
    Q.size (rep.ty metaTy) metadata ≤ (4 * basisCap + 2 * signedCap + 7) * width := by
  have ha := lists.size_le_cap (rep.ty affineTy) metadata.1 (3 * width) basisCap
    (fun a _ => affine_size rep sizes width hh hf a) hi.basisLength
  have hm := lists.size_le_cap (rep.ty message) metadata.2.1 width signedCap hi.signed hi.signedLength
  have ha' : Q.size (rep.ty (.list affineTy)) metadata.1 ≤ (4 * basisCap + 1) * width := by
    change Q.size (rep.ty (.list affineTy)) metadata.1 ≤ _ at ha
    nlinarith [Nat.mul_le_mul_left basisCap hh]
  have hm' : Q.size (rep.ty (.list message)) metadata.2.1 ≤ (2 * signedCap + 1) * width := by
    change Q.size (rep.ty (.list message)) metadata.2.1 ≤ _ at hm
    nlinarith [Nat.mul_le_mul_left signedCap hh]
  have hp := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, metaTy] at *
  grind only

theorem state_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (state : EncodedState F G₁ M) (hi : StateBound (Q := Q) rep width cap basisCap signedCap state) :
    Q.size (rep.ty stateTy) state ≤ (60 * cap + 4 * basisCap + 2 * signedCap + 23) * width := by
  have hc := CacheCompiler.list_size (key := cacheKeyTy) (val := entryTy)
    rep sizes lists state.1 (15 * width) cap (by omega) hi.cache hi.cacheLength
  have hm := history_size rep sizes lists width basisCap signedCap hh hb hf state.2 hi.history
  have hp := sizes.prod_le (rep.ty cacheTy) (rep.ty metaTy) state
  change Q.size (rep.ty stateTy) state ≤ _ at hp
  nlinarith

theorem input_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : Input (Q := Q) rep width cap basisCap signedCap input) :
    Q.size (rep.ty inputTy) input ≤ frameWidth width cap basisCap signedCap := by
  have hs := state_size rep sizes lists width cap basisCap signedCap hh hb hf input.2.2.2 hi.state
  have hp := @sizes.prod_le
  obtain ⟨hg, hk, hm, _⟩ := hi
  dsimp only [LanguageRepresentation.ty, inputTy, frameWidth] at *
  grind only

theorem sampled_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : sampledTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap input.2) :
    Q.size (rep.ty sampledTy) input ≤ frameWidth width cap basisCap signedCap := by
  have hs := state_size rep sizes lists width cap basisCap signedCap hh hb hf input.2.2.2.2 hi.state
  have ha := affine_size rep sizes width hh hf input.1
  have hp := @sizes.prod_le
  obtain ⟨hg, hk, hm, _⟩ := hi
  dsimp only [LanguageRepresentation.ty, sampledTy, inputTy, frameWidth] at *
  grind only

omit lists in
theorem arithmetic_property [Field F] [AddCommGroup G₁] [Module F G₁]
    (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (input : sampledTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap input.2) :
    Work (Q := Q) rep width cap basisCap signedCap (arithmeticValue input) := by
  have ha := affine_size rep sizes width hh hf (input.1.2, -input.1.1)
  have hp := @sizes.prod_le
  refine ⟨⟨?_, ?_, hi.state.cache, hi.state.cacheLength⟩, hg _, hf _, ha, hi.message, hi.state.history⟩
  · have hm := hi.message
    dsimp only [arithmeticValue, LanguageRepresentation.ty] at *
    grind only
  · dsimp only [arithmeticValue, LanguageRepresentation.ty, entryTy, affineTy] at *
    grind only

omit sizes lists [C.HasSum] [C.HasOption] in
theorem histories_property (width cap basisCap signedCap : Nat)
    (input : workTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Work (Q := Q) rep width cap basisCap signedCap input) :
    ProgramInput (Q := Q) rep width cap basisCap signedCap (historiesValue input) := by
  refine ⟨hi.cache, hi.point, hi.scalar, ?_, ?_, ?_⟩
  · simpa only [historiesValue, List.length_append, List.length_singleton] using Nat.add_le_add_right hi.history.basisLength 1
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hi.history.signed m hm
    · simpa only [List.mem_singleton.mp hm] using hi.message
  · simpa only [historiesValue, List.length_append, List.length_singleton] using Nat.add_le_add_right hi.history.signedLength 1

omit sizes lists [C.HasSum] [C.HasOption] in
theorem return_property (width cap basisCap signedCap : Nat)
    (input : programOutputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : ProgramOutput (Q := Q) rep width cap basisCap signedCap input) :
    Output (Q := Q) rep width cap basisCap signedCap (returnValue input) :=
  ⟨hi.2.point, hi.2.scalar, hi.1.1, hi.1.2, hi.2.history⟩

theorem work_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : workTy.Value (cryptoBase F G₁ G₂ K M)) (hi : Work (Q := Q) rep width cap basisCap signedCap input) :
    Q.size (rep.ty workTy) input ≤ frameWidth width cap basisCap signedCap := by
  have hc := CacheCompiler.input_size rep sizes lists (15 * width) cap (by omega) (hu.trans (by omega)) input.1 hi.cache
  have hm := history_size rep sizes lists width basisCap signedCap hh hb hf input.2.2.2.2 hi.history
  have hp := @sizes.prod_le
  obtain ⟨_, hR, hz, ha, hmsg, _⟩ := hi
  dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env, workTy, cacheArgsTy, replyTy, frameWidth] at *
  grind only

theorem saved_size (width basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (saved : savedTy.Value (cryptoBase F G₁ G₂ K M)) (hi : Saved (Q := Q) rep width basisCap signedCap saved) :
    Q.size (rep.ty savedTy) saved ≤ (4 * basisCap + 2 * signedCap + 11) * width := by
  have hm := history_size rep sizes lists width basisCap signedCap hh hb hf saved.2 hi.history
  have hp := @sizes.prod_le
  obtain ⟨hR, hz, _⟩ := hi
  dsimp only [LanguageRepresentation.ty, savedTy, replyTy] at *
  grind only

theorem programInput_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : programInputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : ProgramInput (Q := Q) rep width cap basisCap signedCap input) :
    Q.size (rep.ty programInputTy) input ≤ frameWidth width cap basisCap signedCap := by
  have hc := CacheCompiler.input_size rep sizes lists (15 * width) cap (by omega) (hu.trans (by omega)) input.1 hi.1
  have hs := saved_size rep sizes lists width (basisCap + 1) (signedCap + 1) hh hb hf input.2 hi.2
  have hp := sizes.prod_le (rep.ty cacheArgsTy) (rep.ty savedTy) input
  dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty, programInputTy, cacheArgsTy, frameWidth] at *
  nlinarith

theorem programOutput_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : programOutputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : ProgramOutput (Q := Q) rep width cap basisCap signedCap input) :
    Q.size (rep.ty programOutputTy) input ≤ frameWidth width cap basisCap signedCap := by
  have hc := CacheCompiler.list_size rep sizes lists input.1 (15 * width) (cap + 1) (by omega) hi.1.1 hi.1.2
  have hs := saved_size rep sizes lists width (basisCap + 1) (signedCap + 1) hh hb hf input.2 hi.2
  have hp := sizes.prod_le (rep.ty cacheTy) (rep.ty savedTy) input
  dsimp only [LanguageRepresentation.ty, programOutputTy, frameWidth] at *
  nlinarith

theorem output_size (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : outputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : Output (Q := Q) rep width cap basisCap signedCap input) :
    Q.size (rep.ty outputTy) input ≤ frameWidth width cap basisCap signedCap := by
  have hs := state_size rep sizes lists width (cap + 1) (basisCap + 1) (signedCap + 1) hh hb hf input.2 hi.state
  have hp := @sizes.prod_le
  obtain ⟨hR, hz, _⟩ := hi
  dsimp only [LanguageRepresentation.ty, outputTy, replyTy, frameWidth] at *
  grind only

end Signatures.Runtime.SchnorrAGM.Native.Signing

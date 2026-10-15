import Signatures.Runtime.BackendSchnorrAGMRead

/-! Read invariants bound the two unchanged histories separately. Reads preserve
these bounds exactly, so repeated access does not repeatedly inflate a bound on
the whole metadata tuple. All cache capacities count encountered keys. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Read

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

def History (historyWidth : Nat) (metadata : Metadata F M) : Prop :=
  Q.size (rep.ty (.list affineTy)) metadata.1 ≤ historyWidth ∧
    Q.size (rep.ty (.list message)) metadata.2.1 ≤ historyWidth

def StateBound (width cap historyWidth : Nat) (state : EncodedState F G₁ M) : Prop :=
  CacheCompiler.Entries (Q := Q) rep (key := cacheKeyTy) (val := entryTy) (5 * width) state.1 ∧
    state.1.length ≤ cap ∧ History (Q := Q) rep historyWidth state.2

def Input (width cap historyWidth : Nat) (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size (rep.ty cacheKeyTy) input.1 ≤ 5 * width ∧
    Q.size (rep.ty affineTy) input.2.1 ≤ width ∧ StateBound (Q := Q) rep width cap historyWidth input.2.2

def Output (width cap historyWidth : Nat) (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size (rep.ty scalar) output.1 ≤ width ∧ StateBound (Q := Q) rep width cap historyWidth output.2

def CoreInput (width cap : Nat) (input : coreInputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  CacheCompiler.Input (Q := Q) rep (5 * width) cap input.1 ∧ Q.size (rep.ty affineTy) input.2.1 ≤ width

def CoreOutput (width cap : Nat) (output : coreOutputTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  CacheCompiler.Output (Q := Q) rep (5 * width) cap output.1 ∧ Q.size (rep.ty affineTy) output.2.1 ≤ width

def frameWidth (width cap historyWidth : Nat) : Nat := (20 * cap + 200) * width + 4 * historyWidth

include sizes

theorem history_size (width historyWidth : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (metadata : Metadata F M)
    (hm : History (Q := Q) rep historyWidth metadata) :
    Q.size (rep.ty metaTy) metadata ≤ 2 * historyWidth + 5 * width := by
  obtain ⟨hr, hs⟩ := hm
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty] at *
  grind only

theorem pack_property [Zero F] (width cap historyWidth : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : Input (Q := Q) rep width cap historyWidth input) :
    CoreInput (Q := Q) rep width cap (packValue input).1 ∧
      History (Q := Q) rep historyWidth (packValue input).2 := by
  obtain ⟨hk, ha, he, hn, hm⟩ := hi
  have hd : Q.size (rep.ty entryTy) ((0 : F), false, input.2.1) ≤ 5 * width := by
    have hprod := @sizes.prod_le
    have hb' := hb false
    dsimp only [LanguageRepresentation.ty] at *
    grind only
  exact ⟨⟨⟨hk, hd, he, hn⟩, ha⟩, hm⟩

omit [C.HasSum] [C.HasOption] sizes in
theorem return_property (width cap historyWidth : Nat)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : retainedOutputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : CoreOutput (Q := Q) rep width cap input.1 ∧ History (Q := Q) rep historyWidth input.2) :
    Output (Q := Q) rep width cap historyWidth (returnValue input) :=
  ⟨hf _, hi.1.1.2.1, hi.1.1.2.2, hi.2⟩

include lists

theorem input_size (width cap historyWidth : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : Input (Q := Q) rep width cap historyWidth input) :
    Q.size (rep.ty inputTy) input ≤ frameWidth width cap historyWidth := by
  obtain ⟨hk, ha, he, hn, hm⟩ := hi
  have hc := CacheCompiler.list_size rep sizes lists input.2.2.1 (5 * width) cap (by omega) he hn
  have hm := history_size rep sizes width historyWidth hh hb input.2.2.2 hm
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, frameWidth] at *
  grind only

theorem coreInput_size (width cap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (input : coreInputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : CoreInput (Q := Q) rep width cap input) :
    Q.size (rep.ty coreInputTy) input ≤ (20 * cap + 40) * width := by
  have hc := CacheCompiler.input_size rep sizes lists (5 * width) cap (by omega) (by omega) input.1 hi.1
  have hs := readStore_size rep sizes input.2 width hh hb hi.2
  have hp := sizes.prod_le (rep.ty (.pair cacheKeyTy (.pair entryTy (.pair cacheTy .unit))))
    (rep.ty readStoreTy) input
  dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env] at *
  nlinarith

theorem coreOutput_size (width cap : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (input : coreOutputTy.Value (cryptoBase F G₁ G₂ K M)) (hi : CoreOutput (Q := Q) rep width cap input) :
    Q.size (rep.ty coreOutputTy) input ≤ (20 * cap + 20) * width := by
  have hc := CacheCompiler.output_size rep sizes lists (5 * width) cap (by omega) input.1 hi.1
  have hs := readStore_size rep sizes input.2 width hh hb hi.2
  have hp := sizes.prod_le (rep.ty (.pair entryTy cacheTy)) (rep.ty readStoreTy) input
  dsimp only [LanguageRepresentation.ty] at *
  nlinarith

theorem retainedInput_size (width cap historyWidth : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (input : retainedInputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : CoreInput (Q := Q) rep width cap input.1 ∧ History (Q := Q) rep historyWidth input.2) :
    Q.size (rep.ty retainedInputTy) input ≤ frameWidth width cap historyWidth := by
  have hc := coreInput_size rep sizes lists width cap hh hu hb input.1 hi.1
  have hm := history_size rep sizes width historyWidth hh hb input.2 hi.2
  have hp := sizes.prod_le (rep.ty coreInputTy) (rep.ty metaTy) input
  dsimp only [LanguageRepresentation.ty, frameWidth] at *
  nlinarith

theorem retainedOutput_size (width cap historyWidth : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (input : retainedOutputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : CoreOutput (Q := Q) rep width (cap + 1) input.1 ∧ History (Q := Q) rep historyWidth input.2) :
    Q.size (rep.ty retainedOutputTy) input ≤ frameWidth width cap historyWidth := by
  have hc := coreOutput_size rep sizes lists width (cap + 1) hh hb input.1 hi.1
  have hm := history_size rep sizes width historyWidth hh hb input.2 hi.2
  have hp := sizes.prod_le (rep.ty coreOutputTy) (rep.ty metaTy) input
  dsimp only [LanguageRepresentation.ty, frameWidth] at *
  nlinarith

theorem output_size (width cap historyWidth : Nat) (hh : header ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (output : outputTy.Value (cryptoBase F G₁ G₂ K M)) (ho : Output (Q := Q) rep width (cap + 1) historyWidth output) :
    Q.size (rep.ty outputTy) output ≤ frameWidth width cap historyWidth := by
  obtain ⟨hf, he, hn, hm⟩ := ho
  have hc := CacheCompiler.list_size rep sizes lists output.2.1 (5 * width) (cap + 1) (by omega) he hn
  have hm := history_size rep sizes width historyWidth hh hb output.2.2 hm
  have hprod := @sizes.prod_le
  dsimp only [LanguageRepresentation.ty, frameWidth] at *
  grind only

end Signatures.Runtime.SchnorrAGM.Native.Read

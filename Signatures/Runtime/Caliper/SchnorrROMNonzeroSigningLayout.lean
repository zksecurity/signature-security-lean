import Signatures.Runtime.Caliper.SchnorrROMEnumeratedSigning
import Signatures.Runtime.Caliper.GuardedBranchBounds

/-! Frames of the deterministic NONZERO signing suffix. After the three draws
the core receives `(a, ((c, z), g, pk, msg, managed))`; the commitment `R` is
prepended, the repaired reply `(R', z')` is prepended again, and the result is
routed into the managed-cache programming frame. Every projection and copy
below is an executed `ByteRoute`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

/-- Field addition, the only local primitive used by the nonzero signer beyond
the point operations `Handler.Operations` of full-field signing. -/
structure Arithmetic [Add F] where
  add : Implementation .unit config.handler.core.arithmetic.scalars config.handler.core.scalar (fun value => value.1 + value.2)
  slots : Nat
  addNames : NamesBound add.program.code slots
  reserve : slots + 3 < 2 ^ w

abbrev sw : Nat := config.handler.core.scalar.representation.encoding.words
abbrev pw : Nat := config.handler.core.point.representation.encoding.words
abbrev mw : Nat := config.handler.core.message.representation.encoding.words
abbrev tw : Nat := config.handler.core.table.representation.encoding.words

theorem input_words : config.handler.core.input.representation.encoding.words =
    2 * sw config + 2 * pw config + mw config + tw config :=
  Signing.Layouts.input_words _

theorem width_eq : config.handler.core.width = tw config + 3 * sw config + 3 * pw config + mw config := by
  unfold Signing.Layouts.width
  change 1 + (config.handler.core.capacityPred + 1) * (mw config + pw config + sw config) + 3 * sw config +
    3 * pw config + mw config = _
  have table : tw config = 1 + (config.handler.core.capacityPred + 1) * (mw config + pw config + sw config) :=
    Signing.Layouts.table_words _
  omega

theorem fits {words : Nat} (bound : words ≤ 64 * (tw config + 3 * sw config + 3 * pw config + mw config)) : words < 2 ^ w :=
  config.handler.core.fits_of_le (by rw [width_eq]; exact bound)

def nzInput : Layout w (F × Signing.Input M F G) :=
  config.handler.core.scalar.prod config.handler.core.input (fits config (by
    change sw config + config.handler.core.input.representation.encoding.words ≤ _; rw [input_words]; omega))
theorem nzInput_words : (nzInput config).representation.encoding.words =
    3 * sw config + 2 * pw config + mw config + tw config := by
  change sw config + _ = _; rw [input_words]; omega

def frame : Layout w (G × F × Signing.Input M F G) :=
  config.handler.core.point.prod (nzInput config) (fits config (by
    change pw config + (nzInput config).representation.encoding.words ≤ _; rw [nzInput_words]; omega))
theorem frame_words : (frame config).representation.encoding.words =
    3 * sw config + 3 * pw config + mw config + tw config := by
  change pw config + _ = _; rw [nzInput_words]; omega

def framed : Layout w ((G × F) × G × F × Signing.Input M F G) :=
  config.handler.core.reply.prod (frame config) (fits config (by
    change (pw config + sw config) + _ ≤ _; rw [frame_words]; omega))
theorem framed_words : (framed config).representation.encoding.words =
    4 * sw config + 4 * pw config + mw config + tw config := by
  change (pw config + sw config) + _ = _; rw [frame_words]; omega

theorem work_words [DecidableEq M] [DecidableEq G] : config.handler.core.work.representation.encoding.words =
    tw config + mw config + 4 * pw config + 2 * sw config := by
  change config.handler.core.cache.lookup.input.representation.encoding.words + ((pw config + sw config) + (pw config + pw config)) = _
  rw [LookupLayout.input_words]
  change (1 + (config.handler.core.capacityPred + 1) * (mw config + pw config + sw config) + (mw config + pw config) + sw config) +
    ((pw config + sw config) + (pw config + pw config)) = _
  have table : tw config = 1 + (config.handler.core.capacityPred + 1) * (mw config + pw config + sw config) :=
    Signing.Layouts.table_words _
  omega

/-! ### Accessors of a frame value -/

section Access
variable {config}
def commitmentOf (v : (frame config).Value) : config.handler.core.point.Value := ⟨v.val.1, v.property.1⟩
def nonceOf (v : (frame config).Value) : config.handler.core.scalar.Value := ⟨v.val.2.1, v.property.2.1⟩
def challengeOf (v : (frame config).Value) : config.handler.core.scalar.Value := ⟨v.val.2.2.1.1, v.property.2.2.1.1.1⟩
def responseOf (v : (frame config).Value) : config.handler.core.scalar.Value := ⟨v.val.2.2.1.2, v.property.2.2.1.1.2⟩
def generatorOf (v : (frame config).Value) : config.handler.core.point.Value := ⟨v.val.2.2.2.1, v.property.2.2.1.2.1⟩
def publicKeyOf (v : (frame config).Value) : config.handler.core.point.Value := ⟨v.val.2.2.2.2.1, v.property.2.2.1.2.2.1⟩
def messageOf (v : (frame config).Value) : config.handler.core.message.Value := ⟨v.val.2.2.2.2.2.1, v.property.2.2.1.2.2.2.1⟩
def tableOf (v : (frame config).Value) : config.handler.core.table.Value := ⟨v.val.2.2.2.2.2.2, v.property.2.2.1.2.2.2.2⟩
end Access

theorem frame_bytes (v : (frame config).Value) : (frame config).representation.encoding.encode v =
    config.handler.core.point.representation.encoding.encode (commitmentOf v) ++
      (config.handler.core.scalar.representation.encoding.encode (nonceOf v) ++
        ((config.handler.core.scalar.representation.encoding.encode (challengeOf v) ++
          config.handler.core.scalar.representation.encoding.encode (responseOf v)) ++
          (config.handler.core.point.representation.encoding.encode (generatorOf v) ++
            (config.handler.core.point.representation.encoding.encode (publicKeyOf v) ++
              (config.handler.core.message.representation.encoding.encode (messageOf v) ++
                config.handler.core.table.representation.encoding.encode (tableOf v)))))) := rfl

/-- One executed slice of a concatenated frame. -/
theorem take_drop_block {whole before block after : List (Word w)} {offset count : Nat}
    (shape : whole = before ++ (block ++ after)) (start : before.length = offset) (size : block.length = count) :
    (whole.drop offset).take count = block := by
  subst shape start size
  simp

/-- Build a source implementation from an executed byte route. -/
def route {A B : Type} (input : Layout w A) (output : Layout w B) (f : A → B)
    (preserves : ∀ value, input.valid value → output.valid (f value)) (parts : List (Part w))
    (bounded : Valid input.representation.encoding.words parts) (size : words parts = output.representation.encoding.words)
    (correct : ∀ value : input.Value, bytes (input.representation.encoding.encode value) parts =
      output.representation.encoding.encode ⟨f value.val, preserves value.val value.property⟩) :
    Implementation .unit input output f where
  preserves := preserves
  program := ByteRoute.realizer _ _ _ parts config.sampler.wordFits bounded size correct

theorem route_bounded {A B : Type} (input : Layout w A) (output : Layout w B) (f : A → B)
    (preserves : ∀ value, input.valid value → output.valid (f value)) (parts : List (Part w))
    (bounded : Valid input.representation.encoding.words parts) (size : words parts = output.representation.encoding.words)
    (correct : ∀ value : input.Value, bytes (input.representation.encoding.encode value) parts =
      output.representation.encoding.encode ⟨f value.val, preserves value.val value.property⟩) :
    (route config input output f preserves parts bounded size correct).BoundedBy
      (8 * output.representation.encoding.words) (26 * output.representation.encoding.words + 14) :=
  ⟨fun value => ByteRoute.time _ _ _ parts config.sampler.wordFits bounded size correct value,
    ByteRoute.codeWords _ _ _ parts config.sampler.wordFits bounded size correct⟩

theorem route_buffers {A B : Type} (input : Layout w A) (output : Layout w B) (f : A → B)
    (preserves : ∀ value, input.valid value → output.valid (f value)) (parts : List (Part w))
    (bounded : Valid input.representation.encoding.words parts) (size : words parts = output.representation.encoding.words)
    (correct : ∀ value : input.Value, bytes (input.representation.encoding.encode value) parts =
      output.representation.encoding.encode ⟨f value.val, preserves value.val value.property⟩) :
    (route config input output f preserves parts bounded size correct).program.code.memBound ≤ 2 :=
  ByteRoute.buffers _ _ _ parts config.sampler.wordFits bounded size correct

theorem route_names {A B : Type} (input : Layout w A) (output : Layout w B) (f : A → B)
    (preserves : ∀ value, input.valid value → output.valid (f value)) (parts : List (Part w))
    (bounded : Valid input.representation.encoding.words parts) (size : words parts = output.representation.encoding.words)
    (correct : ∀ value : input.Value, bytes (input.representation.encoding.encode value) parts =
      output.representation.encoding.encode ⟨f value.val, preserves value.val value.property⟩) (slots : Nat) :
    NamesAccounted (route config input output f preserves parts bounded size correct).program.code slots :=
  ByteRoute.names _ _ _ parts config.sampler.wordFits bounded size correct slots

end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning

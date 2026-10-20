import Signatures.Runtime.Caliper.SchnorrROMSigningHandlerLayout

/-! Executed frame permutations around private sampling and signing. The final
view changes only tuple grouping: it preserves every encoded byte. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
open Caliper BoundedSource ByteRoute SchnorrROMTape
variable {w : Nat} {M F G C : Type} (layout : Layouts w M F G C)

def message (value : layout.input.Value) : layout.message.Value := ⟨value.val.1, value.property.1.1⟩
def config (value : layout.input.Value) : layout.core.arithmetic.points.Value :=
  ⟨value.val.2.1.1, value.property.1.2.1.1⟩
def managed (value : layout.input.Value) : layout.core.table.Value :=
  ⟨value.val.2.1.2.1, value.property.1.2.1.2.1⟩
def live (value : layout.input.Value) : layout.core.table.Value :=
  ⟨value.val.2.1.2.2, value.property.1.2.1.2.2⟩
def tapes (value : layout.input.Value) : PrivateSampler.Store layout.sampler :=
  ⟨value.val.2.2, value.property.1.2.2⟩
def context (value : layout.input.Value) : layout.context.Value :=
  ⟨((value.val.2.1.1.1, value.val.2.1.1.2, value.val.1, value.val.2.1.2.1), value.val.2.1.2.2),
    ⟨⟨(config layout value).property.1, (config layout value).property.2,
      (message layout value).property, (managed layout value).property⟩, value.property.2⟩,
    (live layout value).property⟩
def prepareValue (value : layout.input.Value) := (tapes layout value, context layout value)

def prepareParts : List (Part w) :=
  [.slice (layout.message.representation.encoding.words + layout.core.arithmetic.points.representation.encoding.words +
      2 * layout.core.table.representation.encoding.words) (Read.tapes layout.sampler.tape).representation.encoding.words,
   .slice layout.message.representation.encoding.words layout.core.arithmetic.points.representation.encoding.words,
   .slice 0 layout.message.representation.encoding.words,
   .slice (layout.message.representation.encoding.words + layout.core.arithmetic.points.representation.encoding.words)
      (2 * layout.core.table.representation.encoding.words)]
theorem prepare_valid : Valid layout.input.representation.encoding.words (prepareParts layout) := by
  change Valid (_ + ((_ + (_ + _)) + _)) _
  simp only [prepareParts, Valid]
  exact ⟨by omega, by omega, by omega, by omega, trivial⟩
theorem prepare_size : words (prepareParts layout) = layout.prepared.encoding.words := by
  simp only [prepareParts, words]
  change (Read.tapes layout.sampler.tape).representation.encoding.words +
    ((layout.point.representation.encoding.words + layout.point.representation.encoding.words) +
      (layout.message.representation.encoding.words + (2 * layout.core.table.representation.encoding.words + 0))) =
    (Read.tapes layout.sampler.tape).representation.encoding.words +
      ((layout.point.representation.encoding.words + (layout.point.representation.encoding.words +
        (layout.message.representation.encoding.words + layout.core.table.representation.encoding.words))) +
        layout.core.table.representation.encoding.words)
  omega
theorem prepare_bytes (value : layout.input.Value) :
    bytes (layout.input.representation.encoding.encode value) (prepareParts layout) =
      layout.prepared.encoding.encode (prepareValue layout value) := by
  let m := layout.message.representation.encoding.encode (message layout value)
  let cfg := layout.core.arithmetic.points.representation.encoding.encode (config layout value)
  let cache := layout.core.table.representation.encoding.encode (managed layout value)
  let other := layout.core.table.representation.encoding.encode (live layout value)
  let tape := (Read.tapes layout.sampler.tape).representation.encoding.encode (tapes layout value)
  have hm : m.length = layout.message.representation.encoding.words := Encoding.encode_length _ _
  have hc : cfg.length = layout.core.arithmetic.points.representation.encoding.words := Encoding.encode_length _ _
  have ht : cache.length = layout.core.table.representation.encoding.words := Encoding.encode_length _ _
  have ho : other.length = layout.core.table.representation.encoding.words := Encoding.encode_length _ _
  have hp : tape.length = (Read.tapes layout.sampler.tape).representation.encoding.words := Encoding.encode_length _ _
  have first := slice_block [] m (cfg ++ cache ++ other ++ tape)
  have second := slice_block m cfg (cache ++ other ++ tape)
  have third := slice_block (m ++ cfg) (cache ++ other) tape
  have fourth := slice_block (m ++ cfg ++ cache ++ other) tape []
  simp only [List.length_nil, List.nil_append, List.length_append, List.append_nil, hm, hc, ht, ho, hp,
    List.append_assoc, ← Nat.add_assoc] at first second third fourth
  have two : layout.core.table.representation.encoding.words + layout.core.table.representation.encoding.words =
      2 * layout.core.table.representation.encoding.words := by omega
  have offset : layout.message.representation.encoding.words + layout.core.arithmetic.points.representation.encoding.words +
      layout.core.table.representation.encoding.words + layout.core.table.representation.encoding.words =
      layout.message.representation.encoding.words + layout.core.arithmetic.points.representation.encoding.words +
      2 * layout.core.table.representation.encoding.words := by omega
  rw [two] at third
  rw [offset] at fourth
  have output : layout.prepared.encoding.encode (prepareValue layout value) = tape ++ ((cfg ++ (m ++ cache)) ++ other) := by
    change tape ++ ((_ ++ (_ ++ (m ++ cache))) ++ other) = tape ++ (((_ ++ _) ++ (m ++ cache)) ++ other)
    simp only [List.append_assoc]
    rfl
  rw [output]
  change bytes (m ++ ((cfg ++ (cache ++ other)) ++ tape)) (prepareParts layout) = _
  simp only [prepareParts, bytes, List.append_nil, List.append_assoc]
  rw [fourth, second, first, third]

def prepare : Realizer .unit layout.input.representation layout.prepared (prepareValue layout) :=
  ByteRoute.realizer _ _ _ (prepareParts layout) layout.sampler.tape.wordFits
    (prepare_valid layout) (prepare_size layout) (prepare_bytes layout)
theorem prepare_time (value) : (prepare layout).time value ≤ 8 * layout.prepared.encoding.words :=
  ByteRoute.time _ _ _ _ _ _ _ _ value
theorem prepare_words : descriptionWords (prepare layout).code ≤ 26 * layout.prepared.encoding.words + 14 :=
  ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem prepare_buffers : (prepare layout).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots

def coreValue (value : (PrivateSampler.Pair.output layout.sampler).Value × layout.context.Value) :
    layout.core.input.Value × layout.saved.Value :=
  (⟨((value.1.val.1, value.1.val.2.1), value.2.val.1),
    ⟨⟨value.1.property.1, value.1.property.2.1⟩, value.2.property.1.1⟩, value.2.property.1.2⟩,
   ⟨(value.2.val.2, value.1.val.2.2), value.2.property.2, value.1.property.2.2⟩)
def coreParts : List (Part w) :=
  [.slice 0 (2 * layout.sampler.tape.scalar.representation.encoding.words),
   .slice (2 * layout.sampler.tape.scalar.representation.encoding.words + (Read.tapes layout.sampler.tape).representation.encoding.words)
      layout.context.representation.encoding.words,
   .slice (2 * layout.sampler.tape.scalar.representation.encoding.words) (Read.tapes layout.sampler.tape).representation.encoding.words]
theorem core_valid : Valid layout.sampled.encoding.words (coreParts layout) := by
  change Valid ((_ + (_ + _)) + _) _
  simp only [coreParts, Valid]
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem core_size : words (coreParts layout) = layout.work.encoding.words := by
  simp only [coreParts, words]
  change 2 * layout.sampler.tape.scalar.representation.encoding.words +
    (((layout.point.representation.encoding.words + (layout.point.representation.encoding.words +
      (layout.message.representation.encoding.words + layout.core.table.representation.encoding.words))) +
      layout.core.table.representation.encoding.words) + ((Read.tapes layout.sampler.tape).representation.encoding.words + 0)) =
    ((layout.sampler.tape.scalar.representation.encoding.words + layout.sampler.tape.scalar.representation.encoding.words) +
      (layout.point.representation.encoding.words + (layout.point.representation.encoding.words +
        (layout.message.representation.encoding.words + layout.core.table.representation.encoding.words)))) +
      (layout.core.table.representation.encoding.words + (Read.tapes layout.sampler.tape).representation.encoding.words)
  omega
theorem core_bytes (value : (PrivateSampler.Pair.output layout.sampler).Value × layout.context.Value) :
    bytes (layout.sampled.encoding.encode value) (coreParts layout) = layout.work.encoding.encode (coreValue layout value) := by
  let first := layout.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.1, value.1.property.1⟩
  let second := layout.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.2.1, value.1.property.2.1⟩
  let tape := (Read.tapes layout.sampler.tape).representation.encoding.encode ⟨value.1.val.2.2, value.1.property.2.2⟩
  let ctx := layout.context.representation.encoding.encode value.2
  have hf : first.length = layout.sampler.tape.scalar.representation.encoding.words := Encoding.encode_length _ _
  have hs : second.length = layout.sampler.tape.scalar.representation.encoding.words := Encoding.encode_length _ _
  have ht : tape.length = (Read.tapes layout.sampler.tape).representation.encoding.words := Encoding.encode_length _ _
  have hc : ctx.length = layout.context.representation.encoding.words := Encoding.encode_length _ _
  have one := slice_block [] (first ++ second) (tape ++ ctx)
  have two := slice_block (first ++ second) tape ctx
  have three := slice_block (first ++ second ++ tape) ctx []
  simp only [List.length_nil, List.nil_append, List.length_append, List.append_nil, hf, hs, ht, hc,
    List.append_assoc, ← Nat.add_assoc] at one two three
  have twice : layout.sampler.tape.scalar.representation.encoding.words + layout.sampler.tape.scalar.representation.encoding.words =
      2 * layout.sampler.tape.scalar.representation.encoding.words := by omega
  rw [twice] at one two three
  change bytes ((first ++ (second ++ tape)) ++ ctx) (coreParts layout) =
    ((first ++ second) ++ layout.core.base.representation.encoding.encode ⟨value.2.val.1, value.2.property.1.1⟩) ++
      (layout.core.table.representation.encoding.encode ⟨value.2.val.2, value.2.property.2⟩ ++ tape)
  simp only [coreParts, bytes, List.append_nil, List.append_assoc]
  rw [one, three, two]
  have contextBytes : ctx = layout.core.base.representation.encoding.encode ⟨value.2.val.1, value.2.property.1.1⟩ ++
      layout.core.table.representation.encoding.encode ⟨value.2.val.2, value.2.property.2⟩ := rfl
  rw [contextBytes]
  simp only [List.append_assoc]

def prepareCore : Realizer .unit layout.sampled layout.work (coreValue layout) :=
  ByteRoute.realizer _ _ _ (coreParts layout) layout.sampler.tape.wordFits (core_valid layout) (core_size layout) (core_bytes layout)
theorem core_time (value) : (prepareCore layout).time value ≤ 8 * layout.work.encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ value
theorem core_words : descriptionWords (prepareCore layout).code ≤ 26 * layout.work.encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem core_buffers : (prepareCore layout).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem core_names (slots : Nat) : NamesAccounted (prepareCore layout).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots

def finishValue (value : layout.core.output.Value × layout.saved.Value) : layout.output.Value :=
  ⟨(value.1.val.1, (value.1.val.2.1, value.1.val.2.2, value.2.val.1), value.2.val.2),
    value.1.property.1, ⟨value.1.property.2.1, value.1.property.2.2, value.2.property.1⟩, value.2.property.2⟩
theorem finish_bytes (value : layout.core.output.Value × layout.saved.Value) :
    layout.output.representation.encoding.encode (finishValue layout value) = layout.finished.encoding.encode value := by
  change _ ++ ((_ ++ (_ ++ _)) ++ _) = (_ ++ (_ ++ _)) ++ (_ ++ _)
  simp only [List.append_assoc]
  rfl

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler

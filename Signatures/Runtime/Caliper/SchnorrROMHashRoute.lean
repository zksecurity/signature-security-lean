import Signatures.Runtime.Caliper.SchnorrROMHashLayout

/-! Executed routing into the managed cache and out of its returned frame.
The shared store copied into the miss routine is ordinary charged runtime data. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Hash
open Caliper BoundedSource ByteRoute SchnorrROMTape
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def prepareParts : List (Part w) :=
  [.slice 0 config.handler.core.key.representation.encoding.words,
   .literal (config.handler.sampler.tape.scalar.representation.encoding.encode ⟨0, trivial⟩),
   .slice (config.handler.core.key.representation.encoding.words + config.handler.core.arithmetic.points.representation.encoding.words)
     config.handler.core.table.representation.encoding.words,
   .slice 0 (input config).representation.encoding.words]

theorem prepare_valid : Valid (input config).representation.encoding.words (prepareParts config) := by
  change (0 + _ ≤ _ + (((_ + _) + (_ + _)) + _)) ∧
    (_ + (_ + _) + _ ≤ _ + (((_ + _) + (_ + _)) + _)) ∧ (0 + _ ≤ _) ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩
theorem prepare_size : words (prepareParts config) = (model config).input.encoding.words := by
  simp only [prepareParts, words, Encoding.encode_length]
  let k := config.handler.core.key.representation.encoding.words
  let t := config.handler.core.table.representation.encoding.words
  let s := (input config).representation.encoding.words
  change k + (1 + (t + (s + 0))) = (k + (1 + (t + 0))) + s
  omega
theorem prepare_bytes (value : (input config).Value) :
    bytes ((input config).representation.encoding.encode value) (prepareParts config) =
      (model config).input.encoding.encode (prepareValue config value) := by
  let key := config.handler.core.key.representation.encoding.encode ⟨value.val.1, value.property.1.1⟩
  let zero := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨0, trivial⟩
  let cfg := config.handler.core.arithmetic.points.representation.encoding.encode ⟨value.val.2.1.1, value.property.1.2.1.1⟩
  let managed := config.handler.core.table.representation.encoding.encode ⟨value.val.2.1.2.1, value.property.1.2.1.2.1⟩
  let tail := config.handler.core.table.representation.encoding.encode ⟨value.val.2.1.2.2, value.property.1.2.1.2.2⟩ ++
    (Read.tapes config.handler.sampler.tape).representation.encoding.encode ⟨value.val.2.2, value.property.1.2.2⟩
  let raw := (input config).representation.encoding.encode value
  have hk : key.length = config.handler.core.key.representation.encoding.words := Encoding.encode_length _ _
  have hc : cfg.length = config.handler.core.arithmetic.points.representation.encoding.words := Encoding.encode_length _ _
  have hm : managed.length = config.handler.core.table.representation.encoding.words := Encoding.encode_length _ _
  have hr : raw.length = (input config).representation.encoding.words := Encoding.encode_length _ _
  have split : raw = key ++ (cfg ++ (managed ++ tail)) := by
    change _ ++ ((_ ++ (_ ++ _)) ++ _) = _ ++ (_ ++ (_ ++ (_ ++ _)))
    simp only [List.append_assoc]
    rfl
  have first := slice_block [] key (cfg ++ (managed ++ tail))
  have second := slice_block (key ++ cfg) managed tail
  have third := slice_block [] raw []
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append, hk, hc, hm, hr,
    List.append_assoc, ← split] at first second third
  have out : (model config).input.encoding.encode (prepareValue config value) = key ++ (zero ++ (managed ++ raw)) := by
    change (_ ++ (_ ++ (_ ++ []))) ++ _ = _
    simp only [List.append_assoc, List.append_nil]
    rfl
  rw [out]
  change (raw.drop 0).take _ ++ (zero ++ ((raw.drop (_ + _)).take _ ++ ((raw.drop 0).take _ ++ []))) = _
  rw [first, second, third, List.append_nil]

def prepare : Realizer .unit (input config).representation (model config).input (prepareValue config) :=
  ByteRoute.realizer _ _ _ (prepareParts config) config.sampler.wordFits
    (prepare_valid config) (prepare_size config) (prepare_bytes config)

def finishParts : List (Part w) :=
  [.slice 0 1,
   .slice (1 + config.handler.core.table.representation.encoding.words + config.handler.core.key.representation.encoding.words)
     config.handler.core.arithmetic.points.representation.encoding.words,
   .slice 1 config.handler.core.table.representation.encoding.words,
   .slice (1 + config.handler.core.table.representation.encoding.words + config.handler.core.key.representation.encoding.words +
     config.handler.core.store.representation.encoding.words)
     (config.handler.core.table.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words)]

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_valid : Valid (model config).output.encoding.words (finishParts config) := by
  let k := config.handler.core.key.representation.encoding.words
  let c := config.handler.core.arithmetic.points.representation.encoding.words
  let t := config.handler.core.table.representation.encoding.words
  let r := (Read.tapes config.handler.sampler.tape).representation.encoding.words
  change (0 + 1 ≤ (1 + t) + (k + ((c + (t + t)) + r))) ∧
    (1 + t + k + c ≤ (1 + t) + (k + ((c + (t + t)) + r))) ∧
    (1 + t ≤ (1 + t) + (k + ((c + (t + t)) + r))) ∧
    (1 + t + k + (c + t) + (t + r) ≤ (1 + t) + (k + ((c + (t + t)) + r))) ∧ True
  exact ⟨by omega, by omega, by omega, by omega, trivial⟩
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_size : words (finishParts config) = (output config).representation.encoding.words := by
  let c := config.handler.core.arithmetic.points.representation.encoding.words
  let t := config.handler.core.table.representation.encoding.words
  let r := (Read.tapes config.handler.sampler.tape).representation.encoding.words
  change 1 + (c + (t + ((t + r) + 0))) = 1 + ((c + (t + t)) + r)
  omega
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_bytes (value : (CacheRead.output (model config).cache).Value × (HashMiss.input config).Value) :
    bytes ((model config).output.encoding.encode value) (finishParts config) =
      (output config).representation.encoding.encode (finishValue config value) := by
  let scalar := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨value.1.val.1, value.1.property.1⟩
  let managed := config.handler.core.table.representation.encoding.encode ⟨value.1.val.2, value.1.property.2⟩
  let key := config.handler.core.key.representation.encoding.encode ⟨value.2.val.1, value.2.property.1⟩
  let cfg := config.handler.core.arithmetic.points.representation.encoding.encode ⟨value.2.val.2.1.1, value.2.property.2.1.1⟩
  let old := config.handler.core.table.representation.encoding.encode ⟨value.2.val.2.1.2.1, value.2.property.2.1.2.1⟩
  let tail := config.handler.core.table.representation.encoding.encode ⟨value.2.val.2.1.2.2, value.2.property.2.1.2.2⟩ ++
    (Read.tapes config.handler.sampler.tape).representation.encoding.encode ⟨value.2.val.2.2, value.2.property.2.2⟩
  have hs : scalar.length = 1 := Encoding.encode_length _ _
  have hm : managed.length = config.handler.core.table.representation.encoding.words := Encoding.encode_length _ _
  have hk : key.length = config.handler.core.key.representation.encoding.words := Encoding.encode_length _ _
  have hc : cfg.length = config.handler.core.arithmetic.points.representation.encoding.words := Encoding.encode_length _ _
  have ho : old.length = config.handler.core.table.representation.encoding.words := Encoding.encode_length _ _
  have ht : tail.length = config.handler.core.table.representation.encoding.words +
      (Read.tapes config.handler.sampler.tape).representation.encoding.words := by simp only [tail, List.length_append, Encoding.encode_length]
  have first := slice_block [] scalar (managed ++ (key ++ (cfg ++ (old ++ tail))))
  have second := slice_block (scalar ++ managed ++ key) cfg (old ++ tail)
  have third := slice_block scalar managed (key ++ (cfg ++ (old ++ tail)))
  have fourth := slice_block (scalar ++ managed ++ key ++ cfg ++ old) tail []
  simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append, hs, hm, hk, hc, ho, ht,
    List.append_assoc] at first second third fourth
  have inp : (model config).output.encoding.encode value = scalar ++ (managed ++ (key ++ (cfg ++ (old ++ tail)))) := by
    change (_ ++ _) ++ (_ ++ ((_ ++ (_ ++ _)) ++ _)) = _ ++ (_ ++ (_ ++ (_ ++ (_ ++ (_ ++ _)))))
    simp only [List.append_assoc]
    rfl
  have out : (output config).representation.encoding.encode (finishValue config value) = scalar ++ (cfg ++ (managed ++ tail)) := by
    change _ ++ ((_ ++ (_ ++ _)) ++ _) = _ ++ (_ ++ (_ ++ (_ ++ _)))
    simp only [List.append_assoc]
    rfl
  rw [inp, out]
  simp only [finishParts, bytes, List.append_nil]
  simp only [Nat.add_assoc] at second fourth ⊢
  rw [first, second, third]
  exact congrArg (fun t => scalar ++ (cfg ++ (managed ++ t))) fourth

def finish : Realizer .unit (model config).output (output config).representation (finishValue config) :=
  ByteRoute.realizer _ _ _ (finishParts config) config.sampler.wordFits
    (finish_valid config) (finish_size config) (finish_bytes config)

theorem prepare_time (value) : (prepare config).time value ≤ 8 * (model config).input.encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_time (value) : (finish config).time value ≤ 8 * (output config).representation.encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ _
theorem prepare_words : descriptionWords (prepare config).code ≤ 26 * (model config).input.encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_words : descriptionWords (finish config).code ≤ 26 * (output config).representation.encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem prepare_buffers : (prepare config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_buffers : (finish config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem prepare_names (slots : Nat) : NamesAccounted (prepare config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ _
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_names (slots : Nat) : NamesAccounted (finish config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ _

end Signatures.Runtime.CaliperBackend.SchnorrROM.Hash

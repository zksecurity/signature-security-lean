import Signatures.Runtime.Caliper.SchnorrROMFinalHashLayout

/-! Executed routing before and after final hashing. The default scalar is
encoded by the chosen scalar representation; its index need not be zero. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash
open Caliper BoundedSource ByteRoute SchnorrROMTape
variable {w : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G)

def prepareParts : List (Part w) :=
  [.slice 0 config.handler.core.key.representation.encoding.words,
   .literal (config.handler.sampler.tape.scalar.representation.encoding.encode ⟨0, trivial⟩),
   .slice (config.handler.core.key.representation.encoding.words + config.handler.core.store.representation.encoding.words)
     (config.handler.core.table.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words),
   .slice config.handler.core.key.representation.encoding.words config.handler.core.store.representation.encoding.words]

theorem prepare_valid : Valid (input config).representation.encoding.words (prepareParts config) := by
  change Valid (_ + (((_ + _) + (_ + _)) + _)) _
  simp only [prepareParts, Valid]
  change _ ∧ (_ + ((_ + _) + _)) + (_ + _) ≤ _ ∧ _ + ((_ + _) + _) ≤ _ ∧ True
  exact ⟨by omega, by omega, by omega, trivial⟩

theorem prepare_size : words (prepareParts config) = (prepared config).encoding.words := by
  simp only [prepareParts, words, Encoding.encode_length]
  let k := config.handler.core.key.representation.encoding.words
  let t := config.handler.core.table.representation.encoding.words
  let r := (Read.tapes config.handler.sampler.tape).representation.encoding.words
  let c := config.handler.core.store.representation.encoding.words
  change k + (1 + ((t + r) + (c + 0))) = ((k + (1 + (t + 0))) + r) + c
  omega

theorem prepare_bytes (value : (input config).Value) :
    bytes ((input config).representation.encoding.encode value) (prepareParts config) =
      (prepared config).encoding.encode (prepareValue config value) := by
  let key := config.handler.core.key.representation.encoding.encode ⟨value.val.1, value.property.1.1⟩
  let zero := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨0, trivial⟩
  let ctx := config.handler.core.store.representation.encoding.encode (context config value)
  let live := config.handler.core.table.representation.encoding.encode ⟨value.val.2.1.2.2, value.property.1.2.1.2.2⟩
  let tape := (Read.tapes config.handler.sampler.tape).representation.encoding.encode (tapes config value)
  have hk : key.length = config.handler.core.key.representation.encoding.words := Encoding.encode_length _ _
  have hc : ctx.length = config.handler.core.store.representation.encoding.words := Encoding.encode_length _ _
  have hl : live.length = config.handler.core.table.representation.encoding.words := Encoding.encode_length _ _
  have ht : tape.length = (Read.tapes config.handler.sampler.tape).representation.encoding.words := Encoding.encode_length _ _
  have inputBytes : (input config).representation.encoding.encode value = key ++ (ctx ++ (live ++ tape)) := by
    change _ ++ (((_ ++ _) ++ (_ ++ _)) ++ _) = _ ++ (((_ ++ _) ++ _) ++ (_ ++ _))
    simp only [List.append_assoc]
    rfl
  have outputBytes : (prepared config).encoding.encode (prepareValue config value) = key ++ (zero ++ (live ++ (tape ++ ctx))) := by
    change ((_ ++ (_ ++ (_ ++ []))) ++ _) ++ _ = _
    simp only [List.append_nil, List.append_assoc]
    rfl
  have first := slice_block [] key (ctx ++ (live ++ tape))
  have second := slice_block (key ++ ctx) (live ++ tape) []
  have third := slice_block key ctx (live ++ tape)
  simp only [List.length_nil, List.nil_append, List.length_append, List.append_nil, hk, hc, hl, ht,
    List.append_assoc] at first second third
  rw [inputBytes, outputBytes]
  simp only [prepareParts, bytes, List.append_nil]
  rw [first, second, third]
  simp only [List.append_assoc]
  rfl

def prepare : Realizer .unit (input config).representation (prepared config) (prepareValue config) :=
  ByteRoute.realizer _ _ _ (prepareParts config) config.sampler.wordFits
    (prepare_valid config) (prepare_size config) (prepare_bytes config)

def finishParts : List (Part w) :=
  [.slice 0 1,
   .slice (1 + config.handler.core.table.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words)
      config.handler.core.store.representation.encoding.words,
   .slice 1 (config.handler.core.table.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words)]

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_valid : Valid (finished config).encoding.words (finishParts config) := by
  change Valid ((1 + config.handler.core.table.representation.encoding.words +
    (Read.tapes config.handler.sampler.tape).representation.encoding.words) + config.handler.core.store.representation.encoding.words) _
  simp only [finishParts, Valid]
  exact ⟨by omega, by omega, by omega, trivial⟩

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_size : words (finishParts config) = (output config).representation.encoding.words := by
  simp only [finishParts, words]
  change 1 + (((_ + _) + _) + ((_ + _) + 0)) = 1 + (((_ + _) + (_ + _)) + _)
  omega

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_bytes (value : ((CacheRead.output (HashCache.model config).cache).Value ×
    (Read.tapes config.handler.sampler.tape).Value) × config.handler.core.store.Value) :
    bytes ((finished config).encoding.encode value) (finishParts config) =
      (output config).representation.encoding.encode (finishValue config value) := by
  let challenge := config.handler.sampler.tape.scalar.representation.encoding.encode ⟨value.1.1.val.1, value.1.1.property.1⟩
  let live := config.handler.core.table.representation.encoding.encode ⟨value.1.1.val.2, value.1.1.property.2⟩
  let tape := (Read.tapes config.handler.sampler.tape).representation.encoding.encode value.1.2
  let ctx := config.handler.core.store.representation.encoding.encode value.2
  have hs : challenge.length = 1 := Encoding.encode_length _ _
  have hl : live.length = config.handler.core.table.representation.encoding.words := Encoding.encode_length _ _
  have ht : tape.length = (Read.tapes config.handler.sampler.tape).representation.encoding.words := Encoding.encode_length _ _
  have hc : ctx.length = config.handler.core.store.representation.encoding.words := Encoding.encode_length _ _
  have outputBytes : (output config).representation.encoding.encode (finishValue config value) =
      challenge ++ (ctx ++ (live ++ tape)) := by
    change _ ++ (((_ ++ _) ++ (_ ++ _)) ++ _) = _ ++ (((_ ++ _) ++ _) ++ (_ ++ _))
    simp only [List.append_assoc]
    rfl
  have first := slice_block [] challenge (live ++ tape ++ ctx)
  have second := slice_block (challenge ++ live ++ tape) ctx []
  have third := slice_block challenge (live ++ tape) ctx
  simp only [List.length_nil, List.nil_append, List.length_append, List.append_nil, hs, hl, ht, hc,
    List.append_assoc, ← Nat.add_assoc] at first second third
  rw [outputBytes]
  change bytes (((challenge ++ live) ++ tape) ++ ctx) (finishParts config) = _
  simp only [finishParts, bytes, List.append_nil, List.append_assoc]
  rw [first, second, third]

def finish : Realizer .unit (finished config) (output config).representation (finishValue config) :=
  ByteRoute.realizer _ _ _ (finishParts config) config.sampler.wordFits
    (finish_valid config) (finish_size config) (finish_bytes config)

theorem prepare_time (value) : (prepare config).time value ≤ 8 * (prepared config).encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ value
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_time (value) : (finish config).time value ≤ 8 * (output config).representation.encoding.words := ByteRoute.time _ _ _ _ _ _ _ _ value
theorem prepare_words : descriptionWords (prepare config).code ≤ 26 * (prepared config).encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_words : descriptionWords (finish config).code ≤ 26 * (output config).representation.encoding.words + 14 := ByteRoute.codeWords _ _ _ _ _ _ _ _
theorem prepare_buffers : (prepare config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_buffers : (finish config).code.memBound ≤ 2 := ByteRoute.buffers _ _ _ _ _ _ _ _
theorem prepare_names (slots : Nat) : NamesAccounted (prepare config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots
omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finish_names (slots : Nat) : NamesAccounted (finish config).code slots := ByteRoute.names _ _ _ _ _ _ _ _ slots

end Signatures.Runtime.CaliperBackend.SchnorrROM.FinalHash

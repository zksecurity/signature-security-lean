import Signatures.Runtime.Caliper.SchnorrROMReplayForkResult

/-! Both failure padding and successful result copies are charged, as are the
stored Boolean dispatch and the payload copy selected by that dispatch. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G X : Type} (config : Signing.Enumerated.Configuration w M F G)

theorem reject_time (input : Representation w X) (value : X) : (reject config input).time value ≤ 8 * (output config).encoding.words :=
  ByteRoute.time input (output config) (fun _ => .inl ()) (rejectParts config) config.sampler.wordFits trivial (reject_size config) (reject_bytes config input) value
theorem reject_words (input : Representation w X) : descriptionWords (reject config input).code ≤ 26 * (output config).encoding.words + 14 :=
  ByteRoute.codeWords input (output config) (fun _ => .inl ()) (rejectParts config) config.sampler.wordFits trivial (reject_size config) (reject_bytes config input)
theorem reject_names (input : Representation w X) (slots : Nat) : NamesAccounted (reject config input).code slots :=
  ByteRoute.names input (output config) (fun _ => .inl ()) (rejectParts config) config.sampler.wordFits trivial (reject_size config) (reject_bytes config input) slots
theorem reject_buffers (input : Representation w X) : (reject config input).code.memBound ≤ 2 :=
  ByteRoute.buffers input (output config) (fun _ => .inl ()) (rejectParts config) config.sampler.wordFits trivial (reject_size config) (reject_bytes config input)
theorem accept_time (value : ReplayMatch.Frame config) : (accept config).time value ≤ 8 * (output config).encoding.words :=
  ByteRoute.time _ _ _ _ _ (accept_valid config) (accept_size config) (accept_bytes config) value
theorem accept_words : descriptionWords (accept config).code ≤ 26 * (output config).encoding.words + 14 :=
  ByteRoute.codeWords _ _ _ _ _ (accept_valid config) (accept_size config) (accept_bytes config)
theorem accept_names (slots : Nat) : NamesAccounted (accept config).code slots :=
  ByteRoute.names _ _ _ _ _ (accept_valid config) (accept_size config) (accept_bytes config) slots
theorem accept_buffers : (accept config).code.memBound ≤ 2 :=
  ByteRoute.buffers _ _ _ _ _ (accept_valid config) (accept_size config) (accept_bytes config)

def finishTime := 8 * (ReplayMatch.frame config).encoding.words + 8 * (output config).encoding.words + 5
def finishWords := 52 * (ReplayMatch.frame config).encoding.words + 52 * (output config).encoding.words + 65

theorem finish_time (value : (Selection.boolean config).Value × ReplayMatch.Frame config) : (finish config).time value ≤ finishTime config := by
  have rejected := reject_time config (ReplayMatch.frame config) value.2
  have accepted := accept_time config value.2
  rcases value with ⟨⟨flag, valid⟩, frame⟩
  simp only at rejected accepted
  cases flag
  all_goals
    change 1 + (1 + ((selectSlice (w := w) 1 (ReplayMatch.frame config).encoding.words).staticTime .unit + _)) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    unfold finishTime
    omega

theorem finish_words : descriptionWords (finish config).code ≤ finishWords config := by
  have rejected := reject_words config (ReplayMatch.frame config)
  have accepted := accept_words config
  change descriptionWords (Dispatch.code (reject config (ReplayMatch.frame config)).code (accept config).code _ _) ≤ _
  rw [Dispatch.code_descriptionWords]
  unfold finishWords
  omega

theorem finish_names (slots : Nat) : NamesAccounted (finish config).code slots :=
  Dispatch.names (reject_names config (ReplayMatch.frame config) slots) (accept_names config slots) _ _
theorem finish_buffers : (finish config).code.memBound ≤ 2 := by
  have rejected := reject_buffers config (ReplayMatch.frame config)
  have accepted := accept_buffers config
  exact (Dispatch.buffers _ _ _ _).trans (by omega)

end Signatures.Runtime.CaliperBackend.SchnorrROM.ReplayFork

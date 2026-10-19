import Signatures.Runtime.Caliper.UniformSampling
import Signatures.Runtime.Caliper.Within

/-! Fixed-range uniform sampling has constant local overhead. The numerical
range may occupy the whole word domain; it does not bound a table or an unrolled
loop. These bounds count local instructions and the priced oracle interface. -/
namespace Signatures.Runtime.CaliperBackend.UniformSampling
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w)
    (n : Fin (bound + 1))

theorem prepare_time (value : (input (w := w)).Value) : (prepare bound hw fits n).time value ≤ 8 := by
  change (Assembly.code [.literal (BitVec.ofNat w n.val)]).staticTime .unit ≤ 8
  exact Assembly.code_time_unit_le _

theorem finish_time (value : Reply bound n) : (finish bound hw fits n).time value ≤ 8 :=
  Assembly.code_time_unit_le _

theorem prepare_words : descriptionWords (prepare bound hw fits n).code ≤ 40 :=
  Assembly.code_descriptionWords_le _
theorem finish_words : descriptionWords (finish bound hw fits n).code ≤ 40 :=
  Assembly.code_descriptionWords_le _

theorem time_bound : Interactive.TimeBound (UniformQuery.port bound hw fits) .unit
    (input (w := w)).representation (code bound hw fits n) 26 := by
  have prepared := Interactive.Refines.compute (UniformQuery.port bound hw fits) .unit (prepare bound hw fits n)
  have first := Interactive.TimeBound.compute (port := UniformQuery.port bound hw fits) (cost := .unit)
    (prepare bound hw fits n) 8 (prepare_time bound hw fits n)
  have request := first.seq prepared (UniformQuery.time_bound bound hw fits)
  have last := Interactive.TimeBound.compute (port := UniformQuery.port bound hw fits) (cost := .unit)
    (finish bound hw fits n) 8 (finish_time bound hw fits n)
  exact request.seq (prefix_refines bound hw fits n) last

theorem code_words : ((code bound hw fits n).lower (UniformQuery.port bound hw fits)).descriptionWords ≤ 125 := by
  have first := prepare_words bound hw fits n
  have last := finish_words bound hw fits n
  have query := UniformQuery.code_words bound hw fits
  simp only [Interactive.Code.lower] at query
  simp only [code, requestCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq,
    WordIO.Code.descriptionWords_compute]
  omega

theorem names : WordIO.NamesBound ((code bound hw fits n).lower (UniformQuery.port bound hw fits)) 3 := by
  have first : registerSlots (prepare bound hw fits n).code ≤ 3 ∧ (prepare bound hw fits n).code.memBound ≤ 2 := by
    change registerSlots (Assembly.code [.literal (BitVec.ofNat w n.val)]) ≤ 3 ∧ _
    exact Assembly.code_names _ 1 (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])
  have last : registerSlots (finish bound hw fits n).code ≤ 3 ∧ (finish bound hw fits n).code.memBound ≤ 2 := by
    exact Assembly.code_names _ 1 (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])
  have query := UniformQuery.names bound hw fits
  have registers := query.registers
  have buffers := query.buffers
  simp only [Interactive.Code.lower] at registers buffers
  constructor <;>
    simp only [code, requestCode, Interactive.Code.lower, WordIO.Code.registerSlots, WordIO.Code.memBound] <;>
    omega

theorem descriptionFits : ((code bound hw fits n).lower (UniformQuery.port bound hw fits)).DescriptionFits :=
  .seq hw (.seq hw (.compute (prepare bound hw fits n).description_fits) (UniformQuery.descriptionFits bound hw fits))
    (.compute (finish bound hw fits n).description_fits)

/-- Complete code, time and total-memory certificate for the actual sampler. -/
theorem within : Interactive.Within (UniformQuery.port bound hw fits)
    (input (w := w)) (output bound hw fits n) 125 166 26
    (fun _ => ($ᵗ (Fin (n.val + 1)) : ProbComp _)) := by
  have bounded := Interactive.within_of_refines (refines bound hw fits n) (time_bound bound hw fits n)
    (code_words bound hw fits n) (names bound hw fits n) (descriptionFits bound hw fits n)
  exact bounded.congr (fun _ => uniform bound hw fits n)

end Signatures.Runtime.CaliperBackend.UniformSampling

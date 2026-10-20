import Signatures.Runtime.Caliper.InteractiveAcceptance
import Signatures.Runtime.Caliper.InteractiveNames
import Signatures.Runtime.Caliper.InteractiveControlBounds

/-! Retain a represented input prefix across an interactive call. The prefix is
copied into the argument suffix and saved in an actual buffer beyond the callee's
footprint. The resulting bytes contain the callee output and original prefix. -/
namespace Signatures.Runtime.CaliperBackend.Interactive.Prefix
open Caliper Assembly OracleComp OracleSpec
variable {w : Nat} {A B R I : Type} {spec : OracleSpec I}
    (input : Representation w A) (request : Representation w R)
    (view : A → R)
    (samePrefix : ∀ value, (input.encoding.encode value).take request.encoding.words = request.encoding.encode (view value))
    (hw : 16 < 2 ^ w) (fits : input.encoding.words + request.encoding.words < 2 ^ w)

def operands : List (Operand w) := reads 0 0 input.encoding.words ++ reads 0 0 request.encoding.words
theorem operands_length : (operands input request).length = input.encoding.words + request.encoding.words := by
  simp only [operands, List.length_append, reads_length]
theorem operands_sources : SourcesBound (operands input request) 1 := by
  rw [operands, sourcesBound_append]
  exact ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩

def prepare : Realizer .unit input (input.prod request fits) (fun value => (value, view value)) :=
  Assembly.realizer .unit (by decide) _ _ _ (operands input request) hw (operands_length input request)
    (by
      intro operand member
      rcases List.mem_append.mp member with member | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have length := congrArg List.length (samePrefix value)
      simp only [List.length_take, input.encoding.encode_length, request.encoding.encode_length] at length
      have size := represented_size input represented
      have fits := input.fits
      rcases List.mem_append.mp member with member | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) (by omega) operand member)
    (by
      intro value before represented
      have length := congrArg List.length (samePrefix value)
      simp only [List.length_take, input.encoding.encode_length, request.encoding.encode_length] at length
      have size := represented_size input represented
      have entire := reads_values 0 0 input.encoding.words before (by omega)
      have saved := reads_values 0 0 request.encoding.words before (by omega)
      simp only [List.drop_zero, represented.2.1] at entire saved
      rw [samePrefix] at saved
      rw [← input.encoding.encode_length value, List.take_length] at entire
      simp only [input.encoding.encode_length] at entire
      change values (reads 0 0 _ ++ reads 0 0 _) before = _
      simp only [values, List.map_append] at *
      rw [entire, saved]
      rfl)

variable (output : Representation w B) (outputFits : output.encoding.words + request.encoding.words < 2 ^ w)
    (port : Port w spec)

def code (body : Code w) : Code w :=
  .seq (.compute (prepare input request view samePrefix hw fits).code)
    (retain body (savedBuffer port body) input.encoding.words output.encoding.words request.encoding.words)

theorem refines {source : A → OracleComp spec B} {body : Code w}
    (correct : Refines port .unit input output source body) :
    Refines port .unit input (output.prod request outputFits)
      (fun value => (fun answer => (answer, view value)) <$> source value)
      (code input request view samePrefix hw fits output port body) := by
  have combined := (Refines.compute port .unit (prepare input request view samePrefix hw fits)).seq
    (correct.retain (by decide) request hw fits outputFits)
  simpa only [pure_bind, code] using combined

theorem time_bound {source : A → OracleComp spec B} {body : Code w} {budget : Nat}
    (correct : Refines port .unit input output source body)
    (bounded : TimeBound port .unit input body budget) :
    TimeBound port .unit input (code input request view samePrefix hw fits output port body)
      (budget + 16 * input.encoding.words + 8 * output.encoding.words + 20 * request.encoding.words) := by
  have preparing : ∀ value, (prepare input request view samePrefix hw fits).time value ≤
      8 * (input.encoding.words + request.encoding.words) := by
    intro value
    have bound := code_time_unit_le (operands input request)
    rw [operands_length] at bound
    exact bound
  have held := (TimeBound.retain correct bounded (by decide) request hw fits).mono (retain_time_unit_le _ _ _ _ _)
  have combined := (TimeBound.compute (port := port) (cost := .unit) _ _ preparing).seq
    (Refines.compute port .unit (prepare input request view samePrefix hw fits)) held
  exact combined.mono (by omega)

theorem code_bound (body : Code w) {budget : Nat} (bounded : (body.lower port).descriptionWords ≤ budget) :
    ((code input request view samePrefix hw fits output port body).lower port).descriptionWords ≤
      budget + 52 * input.encoding.words + 26 * output.encoding.words + 65 * request.encoding.words + 57 := by
  have preparation := code_descriptionWords_le (operands input request)
  rw [operands_length] at preparation
  have held := retain_descriptionWords_le port body (savedBuffer port body)
    input.encoding.words output.encoding.words request.encoding.words
  simp only [code, Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  change descriptionWords (prepare input request view samePrefix hw fits).code ≤ _ at preparation
  omega

theorem names (body : Code w) {slots : Nat} (bound : WordIO.NamesAccounted (body.lower port) slots) :
    WordIO.NamesAccounted ((code input request view samePrefix hw fits output port body).lower port) slots :=
  (WordIO.NamesAccounted.compute (code_namesAccounted _ _ (operands_sources input request))).seq
    (retain_names port bound _ _ _)

theorem buffers (body : Code w) :
    ((code input request view samePrefix hw fits output port body).lower port).memBound ≤
      max 2 (body.lower port).memBound + 1 := by
  have prepared := (code_names (operands input request) 1 (operands_sources input request)).2
  have held := retain_buffers port body input.encoding.words output.encoding.words request.encoding.words
  exact max_le (prepared.trans (by omega)) held

include outputFits in
theorem descriptionFits (body : Code w) (bodyFits : (body.lower port).DescriptionFits)
    (reserve : savedBuffer port body < 2 ^ w) :
    ((code input request view samePrefix hw fits output port body).lower port).DescriptionFits :=
  .seq hw (.compute (prepare input request view samePrefix hw fits).description_fits)
    (retain_descriptionFits port body _ _ _ _ hw bodyFits reserve input.fits request.fits outputFits)

end Signatures.Runtime.CaliperBackend.Interactive.Prefix

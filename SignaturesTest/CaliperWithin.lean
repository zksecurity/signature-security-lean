import Signatures.Runtime.Caliper.Within
import Signatures.Runtime.Caliper.UniformQuery
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperWithin
private def valueLayout : Layout 8 (Word 8) := Layout.all (wordRepresentation 8 (by decide))
private def port := UniformQuery.port (w := 8) 255 (by decide) (by decide)
private def identity : Implementation .unit valueLayout valueLayout id := Implementation.identity valueLayout (by decide)
private def code : Interactive.Code 8 := .compute identity.program.code
private def algorithm (value : valueLayout.Value) : ProbComp (Word 8) := pure value.val

-- Online time is zero, but the two instruction-description words, one buffer
-- descriptor (three words) and the one input word are all charged.
private theorem identity_within : Interactive.Within port valueLayout valueLayout 2 6 0 algorithm := by
  have refined := Interactive.Refines.compute port .unit identity.program
  have timed : Interactive.TimeBound port .unit valueLayout.representation code 0 :=
    Interactive.TimeBound.compute (port := port) (cost := .unit) identity.program 0 (fun _ => le_rfl)
  have named : WordIO.NamesBound (code.lower port) 0 := by constructor <;> decide
  have bounded := Interactive.within_of_refines refined timed (show (code.lower port).descriptionWords ≤ 2 by decide)
    named (WordIO.Code.DescriptionFits.compute identity.program.description_fits)
  exact bounded.congr (fun _ => by rw [map_pure]; rfl)

private theorem larger_budget : Interactive.Within port valueLayout valueLayout 10 20 30 algorithm :=
  identity_within.mono (by decide) (by decide) (by decide)

private theorem zero_memory_impossible (words time : Nat) :
    ¬ Interactive.Within port valueLayout valueLayout words 0 time algorithm := by
  intro bounded
  have charged := bounded.input_memory_le ⟨7, trivial⟩ 7 (by simp [algorithm])
  change 1 ≤ 0 at charged
  omega

open Lean in
run_cmd do
  let before := valueLayout.representation.initial ⟨7, trivial⟩
  let observed := (WordIO.run .unit RandomTape.zero 2 (code.lower port) before []).map
    (fun finished => (finished.state.bufs 0, finished.time, finished.trace, finished.remaining))
  unless observed == some (#[7], 0, [], []) do
    throwError "zero-time identity execution changed its input or queried randomness"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Interactive.Within.mono, ``Interactive.Within.congr, ``Interactive.Within.input_memory_le,
      ``Interactive.within_of_refines, ``Interactive.within_of_refines_accounted,
      ``identity_within, ``larger_budget, ``zero_memory_impossible] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"
end SignaturesTest.CaliperWithin

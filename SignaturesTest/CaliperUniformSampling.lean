import Proofs.Runtime.Caliper.CoronSampling
import Lean

/-! Execute the constructed sampler at both ends of the full Word8 domain.
Check its uniform law, complete resource certificate and proof axioms. -/
namespace SignaturesTest.CaliperUniformSampling
open Caliper OracleComp OracleSpec Signatures.Runtime.CaliperBackend

private def port := UniformQuery.port (w := 8) 255 (by decide) (by decide)
private def sampler (n : Fin 256) := UniformSampling.code (w := 8) 255 (by decide) (by decide) n

private def execute (active : Interactive.Code 8) (timeLimit : Nat) (replies : List (Word 8)) :=
  let initial := (UniformSampling.input (w := 8)).representation.initial ⟨(), trivial⟩
  let before := { initial with
    bufs := fun b => if b = 200 then #[91] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 200 then 99 else initial.regs r
    tapePos := 9 }
  (WordIO.run .unit RandomTape.zero 1000 (active.lower port) before replies).map
    (fun result => (result.state.bufs 0, result.trace, result.remaining,
      result.state.bufs 200, result.state.caps 200, result.state.regs 200, result.state.tapePos,
      decide (result.time ≤ timeLimit)))

example (n : Fin 256) : Interactive.Within port (UniformSampling.input (w := 8))
    (UniformSampling.output 255 (by decide) (by decide) n) 125 166 26
    (fun _ => ($ᵗ (Fin (n.val + 1)) : ProbComp _)) :=
  UniformSampling.within 255 (by decide) (by decide) n

private def scalar := UniformSampling.output (w := 8) 255 (by decide) (by decide) (3 : Fin 256)
private def coron := CoronSampling.code scalar 255 (by decide) (by decide) (1 : Fin 256) (by decide) (sampler 3)

private theorem coron_within : Interactive.Within port (UniformSampling.input (w := 8))
    (CoronSampling.output scalar 255 (by decide) (by decide) (1 : Fin 256) (by decide)) 425 532 88
    (fun _ => ($ᵗ (Fin 4 × Fin 2) : ProbComp _)) :=
  CoronSampling.within scalar 255 (by decide) (by decide) (1 : Fin 256) (by decide)
    (UniformSampling.refines 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.uniform 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.time_bound 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.code_words 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.names 255 (by decide) (by decide) (3 : Fin 256))
    (UniformSampling.descriptionFits 255 (by decide) (by decide) (3 : Fin 256))

open Lean in
run_cmd do
  unless execute (sampler 0) 26 [0, 0, 42] == some (#[0], [.output 0, .invoke, .input 0, .input 0], [42], #[91], 4, 99, 9, true) do
    throwError "zero-range sampler failed to produce its only possible coin"
  unless execute (sampler 255) 26 [255, 255, 42] == some (#[255], [.output 255, .invoke, .input 255, .input 255], [42], #[91], 4, 99, 9, true) do
    throwError "full-word-range sampler wrapped its range or lost the maximal answer"
  unless execute (sampler 3) 26 [3, 2, 42] == some (#[2], [.output 3, .invoke, .input 3, .input 2], [42], #[91], 4, 99, 9, true) do
    throwError "sampler did not return the actual sampled coin"
  unless execute coron 88 [3, 2, 1, 0, 42] == some (#[2, 0],
      [.output 3, .invoke, .input 3, .input 2, .output 1, .invoke, .input 1, .input 0], [42], #[91], 4, 99, 9, true) do
    throwError "Coron pair sampler lost the scalar, reordered queries, or changed private state"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Interactive.Refines.viewOutputOnSupport, ``UniformSampling.refines,
      ``UniformSampling.uniform, ``UniformSampling.time_bound, ``UniformSampling.code_words,
      ``UniformSampling.names, ``UniformSampling.descriptionFits, ``UniformSampling.within,
      ``CoronSampling.refines, ``CoronSampling.uniform, ``CoronSampling.time_bound, ``CoronSampling.code_words,
      ``CoronSampling.names, ``CoronSampling.descriptionFits, ``CoronSampling.within, ``coron_within] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperUniformSampling

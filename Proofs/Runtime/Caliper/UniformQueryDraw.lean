import Proofs.Runtime.Caliper.UniformQuery
import Proofs.Runtime.Caliper.ConstructedStorage
import Proofs.Runtime.Caliper.InteractiveMemory

/-! Executed runtime uniform draws returning the sampled natural. The range
is runtime data, and extracting the reply from its dependent packet is an
actual Caliper copy. No table indexed by all possible ranges is constructed. -/

namespace Signatures.Runtime.CaliperBackend.UniformQueryDraw
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w)

def value : Layout w Nat := Layout.counter w (bound + 1) (width_pos hw) fits
def packet := (value bound hw fits).prod (value bound hw fits) (by change 1 + 1 < 2 ^ w; omega)

def requestView : (value bound hw fits).Value ≃ Fin (bound + 1) where
  toFun request := ⟨request.val, request.property⟩
  invFun request := ⟨request.val, request.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

def finish : Constructed (UniformQuery.packet bound hw fits) (value bound hw fits) Prod.snd :=
  (Constructed.forget (packet bound hw fits) (fun pair => pair.2 ≤ pair.1) (width_pos hw)).then
    (Constructed.second (value bound hw fits) (value bound hw fits) hw (packet bound hw fits).representation.fits)

def code : Interactive.Code w := .seq .query (.compute (finish bound hw fits).implementation.program.code)

def source (request : (value bound hw fits).Value) : ProbComp (value bound hw fits).Value :=
  (fun answer => (⟨answer.val, by
    change answer.val < bound + 1
    have := answer.isLt
    have valid : request.val < bound + 1 := request.property
    omega⟩ :
    (value bound hw fits).Value)) <$> unifSpec.query request.val

theorem query_refines :
    Interactive.Refines (UniformQuery.port bound hw fits) .unit (value bound hw fits).representation
      (UniformQuery.packet bound hw fits).representation
      (fun request => UniformQuery.replyView bound hw fits <$> UniformQuery.source bound (requestView bound hw fits request))
      .query :=
  ((UniformQuery.refines bound hw fits).viewInput (value bound hw fits).representation
    (requestView bound hw fits) (fun _ => rfl)).viewOutput (UniformQuery.packet bound hw fits).representation
      (UniformQuery.replyView bound hw fits) (fun _ => rfl)

theorem refines : Interactive.Refines (UniformQuery.port bound hw fits) .unit
    (value bound hw fits).representation (value bound hw fits).representation
    (source bound hw fits) (code bound hw fits) := by
  convert (query_refines bound hw fits).seq
    (Interactive.Refines.compute (UniformQuery.port bound hw fits) .unit (finish bound hw fits).implementation.program) using 1
  · funext request
    simp only [bind_pure_comp, Functor.map_map, UniformQuery.source, source]
    rfl
  · rfl

theorem time_bound : Interactive.TimeBound (UniformQuery.port bound hw fits) .unit
    (value bound hw fits).representation (code bound hw fits) 18 := by
  have queried := (UniformQuery.time_bound bound hw fits).viewInput (value bound hw fits).representation
    (requestView bound hw fits) (fun _ => rfl)
  exact queried.seq (query_refines bound hw fits)
    (Interactive.TimeBound.compute (port := UniformQuery.port bound hw fits) (cost := .unit)
      (finish bound hw fits).implementation.program _ (finish bound hw fits).bounded.time_le)

theorem code_bound : ((code bound hw fits).lower (UniformQuery.port bound hw fits)).descriptionWords ≤ 85 := by
  have queried := UniformQuery.code_words bound hw fits
  have copied := (finish bound hw fits).bounded.code_le
  change descriptionWords (finish bound hw fits).implementation.program.code ≤ 42 at copied
  change (WordIO.exchange (w := w) 1 2).descriptionWords = 41 at queried
  change (WordIO.exchange (w := w) 1 2).descriptionWords +
    (descriptionWords (finish bound hw fits).implementation.program.code + 1) + 1 ≤ 85
  omega

theorem names : WordIO.NamesBound ((code bound hw fits).lower (UniformQuery.port bound hw fits)) 3 := by
  constructor
  · change 3 ≤ 3; decide
  · change 2 ≤ 3; decide

theorem buffers : ((code bound hw fits).lower (UniformQuery.port bound hw fits)).memBound ≤ 2 := by
  change 2 ≤ 2
  rfl

theorem descriptionFits : ((code bound hw fits).lower (UniformQuery.port bound hw fits)).DescriptionFits :=
  .seq hw (UniformQuery.descriptionFits bound hw fits) (.compute (finish bound hw fits).implementation.program.description_fits)

theorem source_value (request : (value bound hw fits).Value) :
    Subtype.val <$> source bound hw fits request =
      Fin.val <$> (unifSpec.query request.val : ProbComp (Fin (request.val + 1))) := by
  simp only [source, Functor.map_map]

/-- Complete cost and memory for the same actual draw and returned index. -/
theorem resources (tape : RandomTape w) (request : (value bound hw fits).Value) (before : State w)
    (holds : (value bound hw fits).representation.Holds request before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code bound hw fits).execute (UniformQuery.port bound hw fits) .unit tape before)) :
    finished.time ≤ 18 ∧
    ∃ answer ∈ support (source bound hw fits request), (value bound hw fits).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code bound hw fits).lower (UniformQuery.port bound hw fits)) before finished.state
          finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code bound hw fits).lower (UniformQuery.port bound hw fits)).registerSlots) ∧
          between.SupportBound (max buffers ((code bound hw fits).lower (UniformQuery.port bound hw fits)).memBound) ∧ between.WellFormed ∧
          (((code bound hw fits).lower (UniformQuery.port bound hw fits)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code bound hw fits).lower (UniformQuery.port bound hw fits)).memBound) ≤
              115 + registers + 3 * buffers + before.liveMem buffers := by
  have result := (refines bound hw fits).resources (time_bound bound hw fits) (code_bound bound hw fits)
    (names bound hw fits) tape request before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := result
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by omega⟩

end Signatures.Runtime.CaliperBackend.UniformQueryDraw

import Proofs.Runtime.Caliper.GeneratedWeighted

/-! Stored code, names, address bounds and total intermediate-state memory for
the actual generate-and-evaluate program. Retained private state is charged. -/
namespace Signatures.Runtime.CaliperBackend.GeneratedWeighted
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {F M : Type}
    [DecidableEq (key.Value base)]
    (layout : CacheAccumulate.Layouts w (key.Value base) F (val.Value base))
    (domain : Layout w M) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout).representation.encoding.words +
      (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit domain (terms layout capacity countFits storageFits) generate)
    {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (default : layout.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.combine layout.cache.value combine)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
    (draw : Interactive.Code w)

def codeBudget (generatorWords drawWords updateWords : Nat) : Nat :=
  prepareWords layout domain capacity countFits storageFits generatorWords +
    RowFold.codeBudget (WeightedRows.rows layout) capacity drawWords updateWords + 1

theorem code_bound {generatorTime generatorWords drawWords updateTime updateWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords) :
    ((code layout domain capacity countFits storageFits generator port default P comparison correct
      update updateBuffers reserve draw).lower port).descriptionWords ≤
      codeBudget layout domain capacity countFits storageFits generatorWords drawWords updateWords := by
  have generated := prepare_words layout domain capacity countFits storageFits generator port generatorBound
  have evaluated := RowFold.code_bound (base := base) (key := key) (val := val) (WeightedRows.rows layout)
    default P comparison correct update updateBuffers reserve port capacity draw drawBound updateBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, codeBudget]
  exact Nat.add_le_add_right (Nat.add_le_add generated evaluated) 1

theorem names {generatorNames drawNames updateNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames) :
    WordIO.NamesAccounted ((code layout domain capacity countFits storageFits generator port
      default P comparison correct update updateBuffers reserve draw).lower port)
      (max generatorNames (max (max 5 drawNames) updateNames)) :=
  ((prepare_names layout domain capacity countFits storageFits generator port generatorBound).mono
    (Nat.le_max_left _ _)).seq
    ((RowFold.names (base := base) (key := key) (val := val) (WeightedRows.rows layout) default P comparison
      correct update updateBuffers reserve port capacity draw drawBound updateBound).mono (Nat.le_max_right _ _))

theorem descriptionFits
    (generatorReserve : generator.program.savedBuffer < 2 ^ w)
    (drawFits : (draw.lower port).DescriptionFits) {drawNames : Nat}
    (drawBound : WordIO.NamesBound (draw.lower port) drawNames) (namesFit : drawNames + 2 < 2 ^ w) :
    ((code layout domain capacity countFits storageFits generator port default P comparison correct
      update updateBuffers reserve draw).lower port).DescriptionFits :=
  WordIO.Code.DescriptionFits.seq layout.cache.wordFits
    (Interactive.retain_descriptionFits port (.compute generator.program.code) _ _ _ _ layout.cache.wordFits
      (.compute generator.program.description_fits) generatorReserve domain.representation.fits
      (WeightedRows.rows layout).state.representation.fits storageFits)
    (RowFold.descriptionFits (base := base) (key := key) (val := val) (WeightedRows.rows layout)
      default P comparison correct update updateBuffers reserve port capacity countFits
      (by simpa only [WeightedRows.row_words] using storageFits) draw drawFits drawBound namesFit)

variable {source : OracleComp spec layout.cache.value.Value}
    (drawCorrect : Interactive.Refines port .unit layout.cache.lookup.unit.representation
      layout.cache.value.representation (fun _ => source) draw)
    (inputFits : domain.representation.encoding.words +
      (WeightedRows.rows layout).state.representation.encoding.words < 2 ^ w)

include drawCorrect in
theorem resources {generatorTime generatorWords drawTime drawWords updateTime updateWords
      generatorNames drawNames updateNames : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound port .unit layout.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower port) drawNames)
    (updateNamesBound : NamesAccounted update.program.code updateNames)
    (tape : RandomTape w) (value : Input layout domain) (admitted : valid layout domain (generate := generate) value)
    (before : State w) (holds : (input layout domain inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout domain capacity countFits storageFits generator port
      default P comparison correct update updateBuffers reserve draw).execute port .unit tape before)) :
    finished.time ≤ prepareTime layout domain capacity countFits storageFits generatorTime +
      RowFold.timeBudget (WeightedRows.rows layout) capacity drawTime updateTime ∧
    ∃ answer ∈ support (denote layout domain capacity countFits storageFits generator
        default P comparison correct update updateBuffers reserve source value),
      (WeightedRows.rows layout).state.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout domain capacity countFits storageFits generator port
          default P comparison correct update updateBuffers reserve draw).lower port)
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout domain capacity countFits storageFits generator port
            default P comparison correct update updateBuffers reserve draw).lower port).registerSlots) ∧
          between.SupportBound (max buffers ((code layout domain capacity countFits storageFits generator port
            default P comparison correct update updateBuffers reserve draw).lower port).memBound) ∧ between.WellFormed ∧
          ((((code layout domain capacity countFits storageFits generator port default P comparison correct
              update updateBuffers reserve draw).lower port).staticWords registers buffers : Nat) : Int) +
            between.liveMem (max buffers ((code layout domain capacity countFits storageFits generator port
              default P comparison correct update updateBuffers reserve draw).lower port).memBound) ≤
            5 * codeBudget layout domain capacity countFits storageFits generatorWords drawWords updateWords +
              4 * max generatorNames (max (max 5 drawNames) updateNames) + registers + 3 * buffers +
              before.liveMem buffers + (prepareTime layout domain capacity countFits storageFits generatorTime +
                RowFold.timeBudget (WeightedRows.rows layout) capacity drawTime updateTime) := by
  have stored := code_bound layout domain capacity countFits storageFits generator port default P comparison correct
    update updateBuffers reserve draw generatorBound drawWordsBound updateBound
  have named := names layout domain capacity countFits storageFits generator port default P comparison correct
    update updateBuffers reserve draw generatorNamesBound drawNamesBound updateNamesBound
  have result := (refines layout domain capacity countFits storageFits generator port inputFits default P comparison
    correct update updateBuffers reserve drawCorrect).resources
    (time_bound layout domain capacity countFits storageFits generator port inputFits default P comparison correct
      update updateBuffers reserve drawCorrect generatorBound drawTimeBound updateBound)
    stored named tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := result
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨hr, hb, hw, hm⟩ := memory between visited
  refine ⟨hr, hb, hw, ?_⟩
  omega

end Signatures.Runtime.CaliperBackend.GeneratedWeighted

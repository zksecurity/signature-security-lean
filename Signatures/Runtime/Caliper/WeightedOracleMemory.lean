import Signatures.Runtime.Caliper.WeightedOracleBounds

/-! Names, address acceptance and total memory for the same weighted service
execution. All stored branches, initial capacities and visited states count. -/
namespace Signatures.Runtime.CaliperBackend.WeightedOracle
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term layout.evaluation).representation.encoding.words +
      layout.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.message
      (GeneratedWeighted.terms layout.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.evaluation.combine layout.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.responseInput layout.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)


def namesBudget (generatorNames drawNames updateNames responseNames : Nat) : Nat :=
  max (max generatorNames (max (max 5 drawNames) updateNames)) responseNames

theorem group_names {generatorNames drawNames updateNames responseNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (responseBound : ∀ signing, NamesAccounted (response signing).program.code responseNames) :
    WordIO.NamesAccounted ((groupCode layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits))
      (namesBudget generatorNames drawNames updateNames responseNames) := by
  have hashed := (WeightedHash.names layout.hashing P comparison correct _ draw (response false) (responseBuffers false)
    responseReserve drawBound (responseBound false)).mono (show max (max 5 drawNames) responseNames ≤
      namesBudget generatorNames drawNames updateNames responseNames by unfold namesBudget; omega)
  have signed := WeightedSign.names layout.signing layout.zero capacity countFits storageFits generator layout.default
    P comparison correct update updateBuffers updateReserve _ draw (response true) (responseBuffers true) responseReserve
    generatorBound drawBound updateBound (responseBound true)
  exact Interactive.dispatch_names _ hashed signed _ _

theorem names {generatorNames drawNames updateNames responseNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (responseBound : ∀ signing, NamesAccounted (response signing).program.code responseNames) :
    WordIO.NamesAccounted ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits))
      (namesBudget generatorNames drawNames updateNames responseNames) := by
  have small : 3 ≤ namesBudget generatorNames drawNames updateNames responseNames := by unfold namesBudget; omega
  have leftTag := (WordIO.NamesAccounted.compute (inl_names (layout.randomOutput randomBound randomFits)
    layout.groupOutput.representation layout.evaluation.cache.wordFits (layout.output randomBound randomFits).fits).accounted).mono small
  have rightTag := (WordIO.NamesAccounted.compute (inr_names (layout.randomOutput randomBound randomFits)
    layout.groupOutput.representation layout.evaluation.cache.wordFits (layout.output randomBound randomFits).fits).accounted).mono small
  have random := (UniformQuery.forward_names randomBound layout.evaluation.cache.wordFits randomFits layout.store.representation).accounted.mono small
  have group := group_names layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBound drawBound updateBound responseBound
  exact Interactive.dispatch_names (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)
    (left := randomCode layout randomBound randomFits)
    (right := taggedGroup layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve)
    (random.seq leftTag) (group.seq rightTag) _ _

theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (drawFits : (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)) drawSlots)
    (drawReserve : drawSlots + 3 < 2 ^ w) :
    ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).DescriptionFits := by
  have hashed := WeightedHash.descriptionFits layout.hashing P comparison correct _ draw (response false) (responseBuffers false)
    responseReserve drawFits drawBound (by omega)
  have signed := WeightedSign.descriptionFits_of_components layout.signing layout.zero capacity countFits storageFits generator layout.default
    P comparison correct update updateBuffers updateReserve _ draw (response true) (responseBuffers true) responseReserve
    generatorBound generatorReserve drawFits drawBound drawReserve
  have group := Interactive.dispatch_descriptionFits _ _ _ _ _ layout.evaluation.cache.wordFits hashed signed
    layout.hashing.input.representation.fits layout.signing.input.representation.fits
  exact Interactive.dispatch_descriptionFits _ _ _ _ _ layout.evaluation.cache.wordFits
    (.seq layout.evaluation.cache.wordFits
      (UniformQuery.forward_descriptionFits randomBound layout.evaluation.cache.wordFits randomFits layout.store.representation
        (layout.randomOutput randomBound randomFits).fits)
      (.compute (layout.randomTag randomBound randomFits).description_fits))
    (.seq layout.evaluation.cache.wordFits group (.compute (layout.groupTag randomBound randomFits).description_fits))
    (layout.randomInput randomBound randomFits).fits layout.groupInput.fits

theorem resources {source : ProbComp layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation layout.evaluation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime drawWords updateTime updateWords generatorNames drawNames updateNames responseNames : Nat}
    {responseTime responseWords : Bool → Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))
    (generatorNamesBound : NamesAccounted generator.program.code generatorNames)
    (drawNamesBound : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)) drawNames)
    (updateNamesBound : NamesAccounted update.program.code updateNames)
    (responseNamesBound : ∀ signing, NamesAccounted (response signing).program.code responseNames)
    (tape : RandomTape w) (value : Input layout randomBound) (admitted : valid layout (generate := generate) randomBound value)
    (before : State w) (holds : (layout.input randomBound randomFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).execute
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit tape before)) :
    finished.time ≤ timeBudget layout capacity countFits storageFits randomBound randomFits generatorTime drawTime updateTime responseTime ∧
    ∃ answer ∈ support (denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source value),
      (layout.output randomBound randomFits).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape
          ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
            update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
              (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits))
          before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          (((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
              update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
                (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
              update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
                (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).memBound) ≤
              5 * codeBudget layout capacity countFits storageFits randomBound randomFits generatorWords drawWords updateWords responseWords +
                4 * namesBudget generatorNames drawNames updateNames responseNames + registers + 3 * buffers + before.liveMem buffers +
                timeBudget layout capacity countFits storageFits randomBound randomFits generatorTime drawTime updateTime responseTime := by
  have stored := code_bound layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBound drawWordsBound updateBound responseBound
  have named := names layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve generatorNamesBound drawNamesBound updateNamesBound responseNamesBound
  obtain ⟨elapsed, answer, supported, represented, execution, memory⟩ :=
    (refines layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect).resources
      (time_bound layout capacity countFits storageFits generator randomBound randomFits P comparison correct
        update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect generatorBound drawTimeBound updateBound responseBound)
      stored named tape value admitted before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, represented, execution, ?_⟩
  intro between visited
  have bound := (memory between visited).2.2.2
  omega

end Signatures.Runtime.CaliperBackend.WeightedOracle

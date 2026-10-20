import Signatures.Runtime.Caliper.WeightedCallerHandler

/-! Derived resources for the caller-facing weighted service, including packet
conversion, all stored branches, accepted addresses and every visited state. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerHandler
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G : Type}
    [DecidableEq (key.Value base)]
    (layout : WeightedOracle.Layouts w (key.Value base) M F (val.Value base) C G)
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

def timeBudget (generatorTime drawTime updateTime : Nat) (responseTime : Bool → Nat) : Nat :=
  WeightedOracle.timeBudget layout capacity countFits storageFits randomBound randomFits
    generatorTime drawTime updateTime responseTime + 108 * width layout + 8

def codeBudget (generatorWords drawWords updateWords : Nat) (responseWords : Bool → Nat) : Nat :=
  WeightedOracle.codeBudget layout capacity countFits storageFits randomBound randomFits
    generatorWords drawWords updateWords responseWords + 710 * width layout + 420

theorem time_bound {source : ProbComp layout.evaluation.cache.value.Value}
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation layout.evaluation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime updateTime updateWords : Nat} {responseTime responseWords : Bool → Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : Interactive.TimeBound (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      layout.evaluation.cache.lookup.unit.representation draw drawTime)
    (updateBound : update.BoundedBy updateTime updateWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing)) :
    Interactive.TimeBoundOn (ready layout randomBound generate)
      (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
      (input layout randomBound randomFits)
      (code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
        update updateBuffers updateReserve draw response responseBuffers responseReserve)
      (timeBudget layout capacity countFits storageFits randomBound randomFits generatorTime drawTime updateTime responseTime) := by
  have prepared := (Interactive.Refines.compute (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit
    (prepareService layout randomBound randomFits generate)).on (fun _ => True)
  have service := WeightedOracle.refines layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect
  have preparedTime := (Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)
    (cost := .unit) (prepareService layout randomBound randomFits generate) (64 * width layout + 6)
    (fun value => prepare_time layout randomBound randomFits value.val)).on (fun _ => True)
  have serviceTime := WeightedOracle.time_bound layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect generatorBound drawBound updateBound responseBound
  have convertedTime := (Interactive.TimeBound.compute (port := UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)
    (cost := .unit) (finish layout randomBound randomFits) (44 * width layout + 2)
    (finish_time layout randomBound randomFits)).on (fun _ => True)
  have composed := (Interactive.TimeBoundOn.seq prepared preparedTime (Interactive.TimeBoundOn.seq service serviceTime convertedTime (fun _ _ _ _ => trivial)) (by
    intro value _ answer supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst answer
    exact request_valid layout randomBound value.val value.property))
  have bounded := composed.mono (larger := timeBudget layout capacity countFits storageFits randomBound randomFits
    generatorTime drawTime updateTime responseTime) (by unfold timeBudget; omega)
  intro tape value accepted before holds result reached
  exact bounded tape ⟨value, accepted⟩ trivial before holds result reached

theorem code_bound {generatorTime generatorWords drawWords updateTime updateWords : Nat}
    {responseTime responseWords : Bool → Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawBound : (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing)) :
    ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).descriptionWords ≤
      codeBudget layout capacity countFits storageFits randomBound randomFits generatorWords drawWords updateWords responseWords := by
  have prepared := prepare_words layout randomBound randomFits
  have converted := finish_words layout randomBound randomFits
  have service := WeightedOracle.code_bound layout capacity countFits storageFits generator randomBound randomFits P comparison correct
    update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBound drawBound updateBound responseBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names {generatorNames drawNames updateNames responseNames : Nat}
    (generatorBound : NamesAccounted generator.program.code generatorNames)
    (drawBound : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)) drawNames)
    (updateBound : NamesAccounted update.program.code updateNames)
    (responseBound : ∀ signing, NamesAccounted (response signing).program.code responseNames) :
    WordIO.NamesAccounted ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits))
      (WeightedOracle.namesBudget generatorNames drawNames updateNames responseNames) := by
  have small : 3 ≤ WeightedOracle.namesBudget generatorNames drawNames updateNames responseNames := by
    unfold WeightedOracle.namesBudget; omega
  exact ((WordIO.NamesAccounted.compute (prepare_names layout randomBound randomFits)).mono small).seq
    ((WeightedOracle.names layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBound drawBound updateBound responseBound).seq
      ((WordIO.NamesAccounted.compute (finish_names layout randomBound randomFits)).mono small))

theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBound : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (drawFits : (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).DescriptionFits)
    (drawBound : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)) drawSlots)
    (drawReserve : drawSlots + 3 < 2 ^ w) :
    ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).lower
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits)).DescriptionFits :=
  .seq layout.evaluation.cache.wordFits (.compute (prepare layout randomBound randomFits).description_fits)
    (.seq layout.evaluation.cache.wordFits
      (WeightedOracle.descriptionFits layout capacity countFits storageFits generator randomBound randomFits P comparison correct
        update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBound generatorReserve drawFits drawBound drawReserve)
      (.compute (finish layout randomBound randomFits).description_fits))

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
    (tape : RandomTape w) (value : Packet layout randomBound) (admitted : ready layout randomBound generate value)
    (before : State w) (holds : (input layout randomBound randomFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout capacity countFits storageFits generator randomBound randomFits P comparison correct
      update updateBuffers updateReserve draw response responseBuffers responseReserve).execute
        (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits) .unit tape before)) :
    finished.time ≤ timeBudget layout capacity countFits storageFits randomBound randomFits generatorTime drawTime updateTime responseTime ∧
    ∃ answer ∈ support (denote layout capacity countFits storageFits generator randomBound P comparison correct
        update updateBuffers updateReserve response source value),
      (output layout randomBound randomFits).Holds answer finished.state ∧
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
                4 * WeightedOracle.namesBudget generatorNames drawNames updateNames responseNames + registers + 3 * buffers + before.liveMem buffers +
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

end Signatures.Runtime.CaliperBackend.WeightedCallerHandler

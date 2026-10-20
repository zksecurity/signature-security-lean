import Signatures.Runtime.Caliper.WeightedCallerExecution
import Signatures.Runtime.Caliper.WeightedCallerBounds

/-! Weighted caller resources derived from the actual primitive and local caller
routines. Stored code includes every unrolled body; memory includes initial
capacity and every intermediate state of the same execution. -/

namespace Signatures.Runtime.CaliperBackend.WeightedCaller
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G A B U : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (service : WeightedOracle.Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term service.evaluation).representation.encoding.words +
      service.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit service.message
      (GeneratedWeighted.terms service.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit service.evaluation.combine service.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit service.responseInput service.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : service.zero.val = 0)
    (source : ProbComp service.evaluation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit
      service.evaluation.cache.lookup.unit.representation service.evaluation.cache.value.representation (fun _ => source) draw)
    (domain : Nat → Request service randomBound × A → Prop)
    (advance : A × Reply service randomBound → B ⊕ (Request service randomBound × A))
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, WeightedCallerHandler.replyMatches service randomBound q represented original →
        HeadValid service randomBound domain remaining (advance (c, represented)))
variable (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service randomBound randomFits).encoding.words +
      (reply service randomBound randomFits).encoding.words + result.encoding.words + service.store.representation.encoding.words) < 2 ^ w)

variable (continuation : Realizer .unit (CallerStep.resume (layout service randomBound randomFits state result fits))
      (CallerStep.next (layout service randomBound randomFits state result fits)) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → B ⊕ (Request service randomBound × A))
    (initialCode : Realizer .unit input (CallerStep.next (layout service randomBound randomFits state result fits)) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + service.store.representation.encoding.words < 2 ^ w)

def timeBudget (inputWords callerWidth generatorTime drawTime updateTime : Nat) (responseTime : Bool → Nat)
    (localTime initialTime fuel : Nat) : Nat :=
  CallerControl.timeBudget inputWords callerWidth
    (WeightedCallerHandler.timeBudget service capacity countFits storageFits randomBound randomFits generatorTime drawTime updateTime responseTime) localTime initialTime fuel

def codeBudget (inputWords callerWidth generatorWords drawWords updateWords : Nat) (responseWords : Bool → Nat)
    (localWords initialWords fuel : Nat) : Nat :=
  initialWords + 26 * inputWords + 507 * callerWidth + 286 +
    fuel * (WeightedCallerHandler.codeBudget service capacity countFits storageFits randomBound randomFits generatorWords drawWords updateWords responseWords +
      localWords + 742 * callerWidth + 389)

variable {generatorTime generatorWords drawTime drawWords updateTime updateWords localTime initialTime localWords initialWords : Nat}
    {responseTime responseWords : Bool → Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (drawTimeBound : Interactive.TimeBound (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit service.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))
    (localTimeBound : ∀ value, continuation.time value ≤ localTime)
    (initialTimeBound : ∀ value, initialCode.time value ≤ initialTime)
    (localWordsBound : descriptionWords continuation.code ≤ localWords)
    (initialWordsBound : descriptionWords initialCode.code ≤ initialWords)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include generatorBound updateBound drawWordsBound responseBound localWordsBound initialWordsBound in
theorem words (fuel : Nat) :
    ((program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).descriptionWords ≤
      codeBudget service capacity countFits storageFits randomBound randomFits input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) generatorWords drawWords updateWords responseWords localWords initialWords fuel := by
  have generated := CallerControl.program_words (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) advance continuation localNameFits (WeightedCallerHandler.code service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve)
    input initial initialCode initialNameFits inputFits fuel
  have primitive := WeightedCallerHandler.code_bound service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBound drawWordsBound updateBound responseBound
  apply generated.trans
  unfold CallerControl.programWords CallerControl.iterationWords codeBudget
  exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left fuel (by omega))

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
theorem names {generatorNamesCount drawNamesCount updateNamesCount responseNamesCount callerSlots : Nat}
    (room : 5 ≤ callerSlots)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)) drawNamesCount)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (generatorRoom : generatorNamesCount ≤ callerSlots) (drawRoom : drawNamesCount ≤ callerSlots)
    (updateRoom : updateNamesCount ≤ callerSlots) (responseRoom : responseNamesCount ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots)
    (initialNames : NamesAccounted initialCode.code callerSlots) (fuel : Nat) :
    WordIO.NamesAccounted ((program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance state result fits continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).lower
        (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)) callerSlots :=
  CallerControl.program_names (layout service randomBound randomFits state result fits)
    (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) advance continuation localNameFits
    (WeightedCallerHandler.code service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve) input initial initialCode initialNameFits inputFits (by omega)
    ((WeightedCallerHandler.names service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve generatorNames drawNames updateNames responseNames).mono
      (by unfold WeightedOracle.namesBudget; omega)) localNames initialNames fuel

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
theorem descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBuffers : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (drawFits : (draw.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)) drawSlots)
    (drawReserve : drawSlots + 3 < 2 ^ w)
    (handlerNameFits : Interactive.savedBuffer (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)
      (WeightedCallerHandler.code service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve) < 2 ^ w) (fuel : Nat) :
    ((program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower
      (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).DescriptionFits :=
  CallerControl.program_descriptionFits (layout service randomBound randomFits state result fits)
    (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) advance continuation localNameFits
    (WeightedCallerHandler.code service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve) input initial initialCode initialNameFits inputFits
    (WeightedCallerHandler.descriptionFits service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve generatorBuffers generatorReserve drawFits drawNames drawReserve) handlerNameFits fuel

variable (fuel : Nat) (admissible : U × service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → HeadValid service randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → WeightedOracle.Reserved service capacity fuel value.2.val)

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved generatorBound updateBound drawTimeBound responseBound localTimeBound initialTimeBound in
theorem time : Interactive.TimeBoundOn admissible (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit (input.prod service.store.representation inputFits)
    (program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel) (timeBudget service capacity countFits storageFits randomBound randomFits input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) generatorTime drawTime updateTime responseTime localTime initialTime fuel) :=
  CallerControl.program_time (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) advance continuation localNameFits (Invariant service capacity randomBound domain)
    (ready service randomBound generate)
    (WeightedCallerHandler.refines service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect)
    (fun _ packet valid => WeightedCallerHandler.ready_of_reserved service capacity countFits storageFits generator randomBound (packet.1.1, packet.2) valid.2)
    (WeightedCallerHandler.time_bound service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect generatorBound drawTimeBound updateBound responseBound) localTimeBound
    (preserves service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response combineLaw zeroLaw source uniform domain advance advanceValid)
    input initial initialCode initialNameFits inputFits fuel admissible (initial_invariant service capacity randomBound domain initial fuel admissible initialValid initialReserved) initialTime initialTimeBound

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved generatorBound updateBound drawTimeBound drawWordsBound responseBound
  localTimeBound initialTimeBound localWordsBound initialWordsBound in
/-- Time, source result, and whole memory refer to the same supported execution.
All initial buffer capacity remains charged, including storage outside the caller. -/
theorem resources {generatorNamesCount drawNamesCount updateNamesCount responseNamesCount callerSlots : Nat}
    (room : 5 ≤ callerSlots)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)) drawNamesCount)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (generatorRoom : generatorNamesCount ≤ callerSlots) (drawRoom : drawNamesCount ≤ callerSlots)
    (updateRoom : updateNamesCount ≤ callerSlots) (responseRoom : responseNamesCount ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots)
    (initialNames : NamesAccounted initialCode.code callerSlots)
    (tape : RandomTape w) (value : U × service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.store.representation inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).execute (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit tape before)) :
    let code := (program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel)
    let stored := codeBudget service capacity countFits storageFits randomBound randomFits input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) generatorWords drawWords updateWords responseWords localWords initialWords fuel
    let elapsed := timeBudget service capacity countFits storageFits randomBound randomFits input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) generatorTime drawTime updateTime responseTime localTime initialTime fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (CallerControl.start advance
      (WeightedCallerHandler.denote service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source)
      fuel (initial value.1, value.2)),
      (CallerStep.output (layout service randomBound randomFits state result fits)).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).registerSlots) ∧
          between.SupportBound (max buffers (code.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).memBound) ∧ between.WellFormed ∧
          ((code.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits)).memBound) ≤
            stored + 4 * (callerSlots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve combineLaw zeroLaw source uniform drawCorrect domain advance advanceValid state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  have bounded := time service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve combineLaw zeroLaw source uniform drawCorrect domain advance advanceValid state result fits continuation localNameFits
    input initial initialCode initialNameFits inputFits generatorBound updateBound drawTimeBound responseBound localTimeBound initialTimeBound
    fuel admissible initialValid initialReserved
  have stored := words service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    generatorBound updateBound drawWordsBound responseBound localWordsBound initialWordsBound fuel
  have named := names service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    room generatorNames drawNames updateNames responseNames generatorRoom drawRoom updateRoom responseRoom localNames initialNames fuel
  exact refined.resources bounded stored
    ⟨named.registers.trans (Nat.add_le_add_left stored callerSlots), named.buffers.trans (Nat.add_le_add_left stored callerSlots)⟩
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.WeightedCaller

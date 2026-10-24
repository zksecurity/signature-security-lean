import Proofs.Runtime.Caliper.BLSCallerExecution

/-! BLS caller resources derived from the actual primitive and local caller
routines. Stored code includes every unrolled body; memory includes initial
capacity and every intermediate state of the same execution. -/

namespace Signatures.Runtime.CaliperBackend.BLSCaller
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets

variable {w : Nat} {C G A B U : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (service : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : service.cache.value.Value) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit service.responseInput service.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)
    (drawSource : ProbComp service.cache.value.Value)
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit
      service.cache.lookup.unit.representation service.cache.value.representation (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (domain : Nat → Request service randomBound × A → Prop)
    (advance : A × Reply service randomBound → B ⊕ (Request service randomBound × A))
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, BLSCallerHandler.replyMatches service randomBound q represented original →
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

def timeBudget (inputWords callerWidth drawTime : Nat) (responseTime : Bool → Nat)
    (localTime initialTime fuel : Nat) : Nat :=
  CallerControl.timeBudget inputWords callerWidth
    (BLSOracle.timeBudget service (BLSDispatch.timeBudget service drawTime responseTime) + 108 * width service + 8)
    localTime initialTime fuel

def codeBudget (inputWords callerWidth drawWords : Nat) (responseWords : Bool → Nat)
    (localWords initialWords fuel : Nat) : Nat :=
  initialWords + 26 * inputWords + 507 * callerWidth + 286 +
    fuel * (BLSOracle.codeBudget service (BLSDispatch.codeBudget service drawWords responseWords) +
      710 * width service + 420 + localWords + 742 * callerWidth + 389)

variable {drawTime drawWords localTime initialTime localWords initialWords : Nat}
    {responseTime responseWords : Bool → Nat}
    (drawTimeBound : Interactive.TimeBound (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit service.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).descriptionWords ≤ drawWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))
    (localTimeBound : ∀ value, continuation.time value ≤ localTime)
    (initialTimeBound : ∀ value, initialCode.time value ≤ initialTime)
    (localWordsBound : descriptionWords continuation.code ≤ localWords)
    (initialWordsBound : descriptionWords initialCode.code ≤ initialWords)

omit [SampleableType (val.Value base)] in
include drawWordsBound responseBound localWordsBound initialWordsBound in
theorem words (fuel : Nat) :
    ((program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).descriptionWords ≤
      codeBudget service input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) drawWords responseWords localWords initialWords fuel := by
  have generated := CallerControl.program_words (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.cache.wordFits randomFits) advance continuation localNameFits (BLSCallerHandler.code service default randomBound randomFits P comparison correct response responseBuffers reserve draw)
    input initial initialCode initialNameFits inputFits fuel
  have primitive := BLSCallerHandler.words service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawWordsBound responseBound
  apply generated.trans
  unfold CallerControl.programWords CallerControl.iterationWords codeBudget
  exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left fuel (by omega))

omit [SampleableType (val.Value base)] in
theorem names {drawSlots responseSlots callerSlots : Nat} (room : 5 ≤ callerSlots)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots)
    (drawRoom : drawSlots ≤ callerSlots) (responseRoom : responseSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots)
    (initialNames : NamesAccounted initialCode.code callerSlots) (fuel : Nat) :
    WordIO.NamesAccounted ((program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower (UniformQuery.port randomBound service.cache.wordFits randomFits)) callerSlots :=
  CallerControl.program_names (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.cache.wordFits randomFits) advance continuation localNameFits (BLSCallerHandler.code service default randomBound randomFits P comparison correct response responseBuffers reserve draw)
    input initial initialCode initialNameFits inputFits (by omega)
    ((BLSCallerHandler.names service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawNames responseNames).mono (by omega)) localNames initialNames fuel

omit [SampleableType (val.Value base)] in
theorem descriptionFits {drawSlots : Nat}
    (drawFits : (draw.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)) drawSlots) (drawReserve : drawSlots + 1 < 2 ^ w)
    (handlerNameFits : Interactive.savedBuffer (UniformQuery.port randomBound service.cache.wordFits randomFits) (BLSCallerHandler.code service default randomBound randomFits P comparison correct response responseBuffers reserve draw) < 2 ^ w) (fuel : Nat) :
    ((program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).DescriptionFits :=
  CallerControl.program_descriptionFits (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.cache.wordFits randomFits) advance continuation localNameFits (BLSCallerHandler.code service default randomBound randomFits P comparison correct response responseBuffers reserve draw)
    input initial initialCode initialNameFits inputFits
    (BLSCallerHandler.descriptionFits service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawFits drawNames drawReserve) handlerNameFits fuel

variable (fuel : Nat) (admissible : U × service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → HeadValid service randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → BLSReply.Reserved service fuel value.2.val)

include drawCorrect drawLaw advanceValid initialValid initialReserved drawTimeBound responseBound localTimeBound initialTimeBound in
theorem time : Interactive.TimeBoundOn admissible (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit (input.prod service.store.representation inputFits)
    (program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel) (timeBudget service input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) drawTime responseTime localTime initialTime fuel) :=
  CallerControl.program_time (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.cache.wordFits randomFits) advance continuation localNameFits (Invariant service randomBound domain)
    (ready service default randomBound)
    (BLSCallerHandler.refines service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawCorrect)
    (fun _ packet valid => BLSCallerHandler.ready_of_reserved service default randomBound (packet.1.1, packet.2) valid.2)
    (BLSCallerHandler.time service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawCorrect drawTimeBound responseBound) localTimeBound
    (preserves service default randomBound P comparison correct response responseBuffers reserve drawSource drawLaw domain advance advanceValid)
    input initial initialCode initialNameFits inputFits fuel admissible (initial_invariant service randomBound domain initial fuel admissible initialValid initialReserved) initialTime initialTimeBound

include drawCorrect drawLaw advanceValid initialValid initialReserved drawTimeBound drawWordsBound responseBound
  localTimeBound initialTimeBound localWordsBound initialWordsBound in
/-- Time, source result, and whole memory refer to the same supported execution.
All initial buffer capacity remains charged, including storage outside the caller. -/
theorem resources {drawSlots responseSlots callerSlots : Nat} (room : 5 ≤ callerSlots)
    (drawNames : WordIO.NamesBound (draw.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots)
    (drawRoom : drawSlots ≤ callerSlots) (responseRoom : responseSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots)
    (initialNames : NamesAccounted initialCode.code callerSlots)
    (tape : RandomTape w) (value : U × service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.store.representation inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support ((program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).execute (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit tape before)) :
    let code := (program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel)
    let stored := codeBudget service input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) drawWords responseWords localWords initialWords fuel
    let elapsed := timeBudget service input.encoding.words (CallerStep.width (layout service randomBound randomFits state result fits)) drawTime responseTime localTime initialTime fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (CallerControl.start advance
      (BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource)
      fuel (initial value.1, value.2)),
      (CallerStep.output (layout service randomBound randomFits state result fits)).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).registerSlots) ∧
          between.SupportBound (max buffers (code.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).memBound) ∧ between.WellFormed ∧
          ((code.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower (UniformQuery.port randomBound service.cache.wordFits randomFits)).memBound) ≤
            stored + 4 * (callerSlots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawSource drawCorrect drawLaw domain advance advanceValid state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  have bounded := time service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawSource drawCorrect drawLaw domain advance advanceValid state result fits continuation localNameFits
    input initial initialCode initialNameFits inputFits drawTimeBound responseBound localTimeBound initialTimeBound
    fuel admissible initialValid initialReserved
  have stored := words service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    drawWordsBound responseBound localWordsBound initialWordsBound fuel
  have named := names service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    room drawNames responseNames drawRoom responseRoom localNames initialNames fuel
  exact refined.resources bounded stored
    ⟨named.registers.trans (Nat.add_le_add_left stored callerSlots), named.buffers.trans (Nat.add_le_add_left stored callerSlots)⟩
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.BLSCaller

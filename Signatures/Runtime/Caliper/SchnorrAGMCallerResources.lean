import Signatures.Runtime.Caliper.SchnorrAGMCallerExecution

/-! Whole generated caller costs derived from the actual handler and local
caller routines. Stored unrolled bodies and every intermediate buffer capacity
are included in the same source-correct execution's memory bound. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
variable {w qH qS randomBound : Nat} {M F G A B U : Type} [Field F]
    (service : Handler.Layouts w M F G qH qS randomBound)
variable [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F]
    (ops : Handler.Operations service) (sampler : Interactive.Code w) (sampleSource : ProbComp service.scheme.scalar.Value)
    (sampleCorrect : Interactive.Refines service.random.port .unit (PairSampling.input w).representation service.scheme.scalar.representation
      (fun _ => sampleSource) sampler)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (domain : Nat → Nat → Nat → Request service × A → Prop)
    (allowed : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      CallerHandler.Allowed service hashes signatures q)
    (advance : A × Reply service → B ⊕ (Request service × A))
    (advanceValid : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      ∀ represented original, CallerHandler.replyMatches service q represented original →
        HeadValid service domain remaining (hashes - CallerHandler.hashCharge service q) (signatures - CallerHandler.signCharge service q)
          (advance (c, represented)))

variable (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service).encoding.words + (reply service).encoding.words +
      result.encoding.words + service.scheme.store.representation.encoding.words) < 2 ^ w)
    (continuation : Realizer .unit (CallerStep.resume (layout service state result fits))
      (CallerStep.next (layout service state result fits)) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → B ⊕ (Request service × A))
    (initialCode : Realizer .unit input (CallerStep.next (layout service state result fits)) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + service.scheme.store.representation.encoding.words < 2 ^ w)

variable (budget : Handler.Budget service ops)
def timeBudget (inputWords callerWidth sampleTime localTime initialTime fuel : Nat) : Nat :=
  CallerControl.timeBudget inputWords callerWidth (CallerHandler.timeBudget service ops budget sampleTime) localTime initialTime fuel
def codeBudget (inputWords callerWidth sampleWords localWords initialWords fuel : Nat) : Nat :=
  initialWords + 26 * inputWords + 507 * callerWidth + 286 +
    fuel * (CallerHandler.codeBudget service ops budget sampleWords + localWords + 742 * callerWidth + 389)

variable {sampleTime sampleWords localTime initialTime localWords initialWords : Nat}
    (sampleBound : Interactive.TimeBound service.random.port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower service.random.port).descriptionWords ≤ sampleWords)
    (localBound : ∀ value, continuation.time value ≤ localTime)
    (initialBound : ∀ value, initialCode.time value ≤ initialTime)
    (localStored : descriptionWords continuation.code ≤ localWords)
    (initialStored : descriptionWords initialCode.code ≤ initialWords)

omit [SampleableType F] in
include sampleStored localStored initialStored in
theorem words (fuel : Nat) :
    ((program service ops sampler advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower
      service.random.port).descriptionWords ≤ codeBudget service ops budget input.encoding.words
        (CallerStep.width (layout service state result fits)) sampleWords localWords initialWords fuel := by
  have generated := CallerControl.program_words (layout service state result fits) service.random.port advance continuation localNameFits
    (CallerHandler.code service ops sampler) input initial initialCode initialNameFits inputFits fuel
  have handler := CallerHandler.code_bound service ops budget sampleStored
  apply generated.trans
  unfold CallerControl.programWords CallerControl.iterationWords codeBudget
  exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left fuel (by omega))

omit [SampleableType F] in
theorem names {sampleSlots callerSlots : Nat}
    (sampleNames : WordIO.NamesBound (sampler.lower service.random.port) sampleSlots)
    (handlerRoom : Handler.nameBudget service ops sampleSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots) (fuel : Nat) :
    WordIO.NamesAccounted ((program service ops sampler advance state result fits continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).lower service.random.port) callerSlots :=
  CallerControl.program_names (layout service state result fits) service.random.port advance continuation localNameFits
    (CallerHandler.code service ops sampler) input initial initialCode initialNameFits inputFits
    (by unfold Handler.nameBudget at handlerRoom; omega)
    ((CallerHandler.names service ops sampleNames).mono handlerRoom) localNames initialNames fuel

omit [SampleableType F] in
theorem descriptionFits {sampleSlots : Nat} (sampleFits : (sampler.lower service.random.port).DescriptionFits)
    (sampleNames : WordIO.NamesBound (sampler.lower service.random.port) sampleSlots)
    (reserve : max ops.slots sampleSlots + 5 < 2 ^ w)
    (handlerNameFits : Interactive.savedBuffer service.random.port (CallerHandler.code service ops sampler) < 2 ^ w) (fuel : Nat) :
    ((program service ops sampler advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower
      service.random.port).DescriptionFits :=
  CallerControl.program_descriptionFits (layout service state result fits) service.random.port advance continuation localNameFits
    (CallerHandler.code service ops sampler) input initial initialCode initialNameFits inputFits
    (CallerHandler.descriptionFits service ops sampleFits sampleNames reserve) handlerNameFits fuel

variable    (fuel : Nat) (admissible : U × service.scheme.store.Value → Prop)
    (initialValid : ∀ value, admissible value → HeadValid service domain fuel qH qS (initial value.1))
    (initialReserved : ∀ value, admissible value → CallerHandler.Reserved service qH qS value.2)

include sampleCorrect uniform allowed advanceValid initialValid initialReserved sampleBound localBound initialBound in
theorem time : Interactive.TimeBoundOn admissible service.random.port .unit (input.prod service.scheme.store.representation inputFits)
    (program service ops sampler advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel)
    (timeBudget service ops budget input.encoding.words (CallerStep.width (layout service state result fits)) sampleTime localTime initialTime fuel) :=
  CallerControl.program_time (layout service state result fits) service.random.port advance continuation localNameFits
    (Invariant service domain) (ready service) (CallerHandler.refines service ops sampleCorrect)
    (available service domain allowed) (CallerHandler.time_bound service ops sampleCorrect budget sampleBound) localBound
    (preserves service ops sampleSource uniform domain allowed advance advanceValid)
    input initial initialCode initialNameFits inputFits fuel admissible
    (initial_invariant service domain initial fuel admissible initialValid initialReserved) initialTime initialBound

include sampleCorrect uniform allowed advanceValid initialValid initialReserved sampleBound sampleStored
  localBound initialBound localStored initialStored in
theorem resources {sampleSlots callerSlots : Nat}
    (sampleNames : WordIO.NamesBound (sampler.lower service.random.port) sampleSlots)
    (handlerRoom : Handler.nameBudget service ops sampleSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (tape : RandomTape w) (value : U × service.scheme.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.scheme.store.representation inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program service ops sampler advance state result fits continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).execute service.random.port .unit tape before)) :
    let code := program service ops sampler advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel
    let stored := codeBudget service ops budget input.encoding.words (CallerStep.width (layout service state result fits)) sampleWords localWords initialWords fuel
    let elapsed := timeBudget service ops budget input.encoding.words (CallerStep.width (layout service state result fits)) sampleTime localTime initialTime fuel
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (CallerControl.start advance (CallerHandler.source service ops sampleSource) fuel (initial value.1, value.2)),
      (CallerStep.output (layout service state result fits)).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower service.random.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower service.random.port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower service.random.port).memBound) ∧ between.WellFormed ∧
          ((code.lower service.random.port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower service.random.port).memBound) ≤
            stored + 4 * (callerSlots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines service ops sampler sampleSource sampleCorrect uniform domain allowed advance advanceValid state result fits
    continuation localNameFits input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  have bounded := time service ops sampler sampleSource sampleCorrect uniform domain allowed advance advanceValid state result fits
    continuation localNameFits input initial initialCode initialNameFits inputFits budget sampleBound localBound initialBound
    fuel admissible initialValid initialReserved
  have stored := words service ops sampler advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    budget sampleStored localStored initialStored fuel
  have named := names service ops sampler advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    sampleNames handlerRoom localNames initialNames fuel
  exact refined.resources bounded stored
    ⟨named.registers.trans (Nat.add_le_add_left stored callerSlots), named.buffers.trans (Nat.add_le_add_left stored callerSlots)⟩
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller

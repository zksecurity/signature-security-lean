import Signatures.Runtime.Caliper.SchnorrAGMCallerExtractionSource

/-! Complete caller/terminal costs derived from local caller routines and
primitive implementations. Both return/cutoff branches and every intermediate
copy are charged; correctness and total memory refer to the same execution. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G A U : Type} [Field F]
    (layout : Layouts w M F G qH qS randomBound A)
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations layout.service)
    (sub : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 / value.2))
    (subBuffers : sub.program.code.memBound ≤ ops.slots) (divBuffers : divide.program.code.memBound ≤ ops.slots)
    (sampler : Interactive.Code w)
    (advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A))
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → layout.forgery.Value ⊕ (layout.Request × A))
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.scheme.store.representation.encoding.words < 2 ^ w)
    (fuel : Nat) (budget : Handler.Budget layout.service ops)

def timeBudget (inputWords sampleTime localTime initialTime fuel subTime divTime : Nat) : Nat :=
  Caller.timeBudget layout.service ops budget inputWords (CallerStep.width layout.control) sampleTime localTime initialTime fuel +
    CallerFinish.timeBudget layout.service.hash layout.pending layout.exitFits
      (Extraction.timeBudget layout.service.hash budget.mulTime budget.addTime subTime divTime sampleTime)
def codeBudget (inputWords sampleWords localWords initialWords fuel subWords divWords : Nat) : Nat :=
  Caller.codeBudget layout.service ops budget inputWords (CallerStep.width layout.control) sampleWords localWords initialWords fuel +
    CallerFinish.codeBudget layout.service.hash layout.pending layout.exitFits
      (Extraction.codeBudget layout.service.hash budget.mulWords budget.addWords subWords divWords sampleWords) + 1

variable {sampleTime sampleWords localTime initialTime localWords initialWords subTime subWords divTime divWords : Nat}
    (subBound : sub.BoundedBy subTime subWords) (divBound : divide.BoundedBy divTime divWords)
    (sampleBound : Interactive.TimeBound layout.service.random.port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower layout.service.random.port).descriptionWords ≤ sampleWords)
    (localBound : ∀ value, continuation.time value ≤ localTime) (initialBound : ∀ value, initialCode.time value ≤ initialTime)
    (localStored : descriptionWords continuation.code ≤ localWords) (initialStored : descriptionWords initialCode.code ≤ initialWords)

include subBound divBound sampleStored localStored initialStored in
theorem words :
    ((program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).lower layout.service.random.port).descriptionWords ≤
      codeBudget layout ops budget input.encoding.words sampleWords localWords initialWords fuel subWords divWords := by
  have invoked := Caller.words layout.service ops sampler advance layout.state layout.forgery.representation layout.callerFits
    continuation localNameFits input initial initialCode initialNameFits inputFits budget sampleStored localStored initialStored fuel
  have extracted := Extraction.code_bound layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers divBuffers ops.reserve budget.mul budget.add subBound divBound
    layout.service.random.port sampleStored
  have finished := CallerFinish.code_bound layout.service.hash layout.pending layout.exitFits layout.service.random.port extracted ⟨0, ops.zeroValid⟩
  simp only [program, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, codeBudget]
  exact Nat.add_le_add_right (Nat.add_le_add invoked finished) 1

theorem names {sampleSlots callerSlots : Nat} (sampleNames : WordIO.NamesBound (sampler.lower layout.service.random.port) sampleSlots)
    (handlerRoom : Handler.nameBudget layout.service ops sampleSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (subNames : NamesAccounted sub.program.code ops.slots) (divNames : NamesAccounted divide.program.code ops.slots) :
    WordIO.NamesAccounted ((program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).lower layout.service.random.port) callerSlots := by
  have invoked := Caller.names layout.service ops sampler advance layout.state layout.forgery.representation layout.callerFits
    continuation localNameFits input initial initialCode initialNameFits inputFits sampleNames handlerRoom localNames initialNames fuel
  have extracted := Extraction.names layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers divBuffers ops.reserve layout.service.random.port
    ops.mulNames ops.addNames subNames divNames sampleNames
  have room : Extraction.nameBudget ops.slots sampleSlots ≤ callerSlots := by
    unfold Extraction.nameBudget Handler.nameBudget at *
    omega
  exact invoked.seq (CallerFinish.names layout.service.hash layout.pending layout.exitFits layout.service.random.port
    (extracted.mono room) ⟨0, ops.zeroValid⟩)

theorem descriptionFits {sampleSlots : Nat} (sampleFits : (sampler.lower layout.service.random.port).DescriptionFits)
    (sampleNames : WordIO.NamesBound (sampler.lower layout.service.random.port) sampleSlots)
    (reserve : max ops.slots sampleSlots + 5 < 2 ^ w)
    (handlerNameFits : Interactive.savedBuffer layout.service.random.port (CallerHandler.code layout.service ops sampler) < 2 ^ w) :
    ((program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).lower layout.service.random.port).DescriptionFits := by
  have invoked := Caller.descriptionFits layout.service ops sampler advance layout.state layout.forgery.representation layout.callerFits
    continuation localNameFits input initial initialCode initialNameFits inputFits sampleFits sampleNames reserve handlerNameFits fuel
  have extracted := Extraction.descriptionFits layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers divBuffers ops.reserve layout.service.random.port
    sampleFits ops.addNames sampleNames (by omega)
  exact .seq layout.service.scheme.wordFits invoked
    (CallerFinish.descriptionFits layout.service.hash layout.pending layout.exitFits layout.service.random.port ⟨0, ops.zeroValid⟩ extracted)

variable [SampleableType F] (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (sampleCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input w).representation
      layout.service.scheme.scalar.representation (fun _ => sampleSource) sampler)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (domain : Nat → Nat → Nat → layout.Request × A → Prop)
    (allowed : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      CallerHandler.Allowed layout.service hashes signatures q)
    (advanceValid : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      ∀ represented original, CallerHandler.replyMatches layout.service q represented original →
        Caller.HeadValid layout.service domain remaining
          (hashes - CallerHandler.hashCharge layout.service q) (signatures - CallerHandler.signCharge layout.service q)
          (advance (c, represented)))
    (admissible : U × layout.service.scheme.store.Value → Prop)
    (initialValid : ∀ value, admissible value → Caller.HeadValid layout.service domain fuel qH qS (initial value.1))
    (initialReserved : ∀ value, admissible value → CallerHandler.Reserved layout.service qH qS value.2)

include subBound divBound sampleCorrect uniform allowed advanceValid initialValid initialReserved sampleBound localBound initialBound in
theorem time : Interactive.TimeBoundOn admissible layout.service.random.port .unit
    (input.prod layout.service.scheme.store.representation inputFits)
    (program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel)
    (timeBudget layout ops budget input.encoding.words sampleTime localTime initialTime fuel subTime divTime) := by
  have invoked := Caller.refines layout.service ops sampler sampleSource sampleCorrect uniform domain allowed advance advanceValid
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits
    inputFits fuel admissible initialValid initialReserved
  have callerBound := Caller.time layout.service ops sampler sampleSource sampleCorrect uniform domain allowed advance advanceValid
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits
    inputFits budget sampleBound localBound initialBound fuel admissible initialValid initialReserved
  have extracted := Extraction.refines layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers divBuffers ops.reserve layout.service.random.port sampleCorrect
  have extractTime := Extraction.time_bound layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers divBuffers ops.reserve budget.mul budget.add subBound divBound
    layout.service.random.port sampleCorrect sampleBound
  have finished := (CallerFinish.time_bound layout.service.hash layout.pending layout.exitFits layout.service.random.port
    extracted extractTime ⟨0, ops.zeroValid⟩).viewInput (CallerStep.output layout.control) id layout.packet_bytes
  exact Interactive.TimeBoundOn.seq invoked callerBound finished (called_ready layout ops sampleSource uniform domain allowed advance advanceValid
    initial fuel admissible initialValid initialReserved)

include subBound divBound sampleCorrect uniform allowed advanceValid initialValid initialReserved sampleBound sampleStored
  localBound initialBound localStored initialStored in
theorem resources {sampleSlots callerSlots : Nat} (sampleNames : WordIO.NamesBound (sampler.lower layout.service.random.port) sampleSlots)
    (handlerRoom : Handler.nameBudget layout.service ops sampleSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (subNames : NamesAccounted sub.program.code ops.slots) (divNames : NamesAccounted divide.program.code ops.slots)
    (tape : RandomTape w) (value : U × layout.service.scheme.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.scheme.store.representation inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).execute layout.service.random.port .unit tape before)) :
    let code := program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel
    let stored := codeBudget layout ops budget input.encoding.words sampleWords localWords initialWords fuel subWords divWords
    let elapsed := timeBudget layout ops budget input.encoding.words sampleTime localTime initialTime fuel subTime divTime
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (denote layout ops sub divide subBuffers advance initial fuel sampleSource value),
      layout.service.scheme.scalar.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower layout.service.random.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower layout.service.random.port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower layout.service.random.port).memBound) ∧ between.WellFormed ∧
          ((code.lower layout.service.random.port).staticWords registers buffers : Int) +
            between.liveMem (max buffers (code.lower layout.service.random.port).memBound) ≤
              stored + 4 * (callerSlots + stored) + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines layout ops sub divide subBuffers divBuffers sampleSource uniform domain allowed advance advanceValid
    initial fuel admissible initialValid initialReserved sampler sampleCorrect continuation localNameFits input initialCode initialNameFits inputFits
  have bounded := time layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits input initial initialCode
    initialNameFits inputFits fuel budget subBound divBound sampleBound localBound initialBound sampleSource sampleCorrect uniform domain allowed
    advanceValid admissible initialValid initialReserved
  have stored := words layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits input initial initialCode
    initialNameFits inputFits fuel budget subBound divBound sampleStored localStored initialStored
  have named := names layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits input initial initialCode
    initialNameFits inputFits fuel sampleNames handlerRoom localNames initialNames subNames divNames
  exact refined.resources bounded stored
    ⟨named.registers.trans (Nat.add_le_add_left stored callerSlots), named.buffers.trans (Nat.add_le_add_left stored callerSlots)⟩
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction

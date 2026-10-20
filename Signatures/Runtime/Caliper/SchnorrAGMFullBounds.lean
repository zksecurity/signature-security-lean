import Signatures.Runtime.Caliper.SchnorrAGMFullSource
import Signatures.Runtime.Caliper.Within

/-! Derived resource bounds for the complete Schnorr solver. The actual setup,
caller and extraction programs witness one fixed Caliper implementation for
every represented challenge. Stored code and initial data are included. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Full
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G A : Type}
    (layout : CallerExtraction.Layouts w M F G qH qS randomBound A)
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (routines : Routines layout) (caller : Caller layout)

structure Routines.Bounds where
  handler : Handler.Budget layout.service routines.handler
  subTime : Nat
  subWords : Nat
  divTime : Nat
  divWords : Nat
  sub : routines.sub.BoundedBy subTime subWords
  divide : routines.divide.BoundedBy divTime divWords

structure Caller.Limits where
  localTime : Nat
  localWords : Nat
  initialTime : Nat
  initialWords : Nat
  names : Nat

structure Caller.Bounds (limits : Caller.Limits) : Prop where
  localTime : ∀ value, caller.continuation.time value ≤ limits.localTime
  localWords : descriptionWords caller.continuation.code ≤ limits.localWords
  initialTime : ∀ value, caller.initialCode.time value ≤ limits.initialTime
  initialWords : descriptionWords caller.initialCode.code ≤ limits.initialWords
  localNames : NamesAccounted caller.continuation.code limits.names
  initialNames : NamesAccounted caller.initialCode.code limits.names

variable (bound : Routines.Bounds layout routines) (limits : Caller.Limits)
def timeBudget (sampleTime fuel : Nat) : Nat :=
  8 * layout.service.scheme.initialized.representation.encoding.words +
    CallerExtraction.timeBudget layout routines.handler bound.handler layout.service.scheme.config.representation.encoding.words
      sampleTime limits.localTime limits.initialTime fuel bound.subTime bound.divTime
def codeBudget (sampleWords fuel : Nat) : Nat :=
  26 * layout.service.scheme.initialized.representation.encoding.words + 14 +
    CallerExtraction.codeBudget layout routines.handler bound.handler layout.service.scheme.config.representation.encoding.words
      sampleWords limits.localWords limits.initialWords fuel bound.subWords bound.divWords + 2
def nameBudget (sampleSlots : Nat) : Nat :=
  max (Handler.nameBudget layout.service routines.handler sampleSlots) limits.names
def memoryBudget (sampleTime sampleWords sampleSlots fuel : Nat) : Nat :=
  5 * codeBudget layout routines bound limits sampleWords fuel + 4 * nameBudget layout routines limits sampleSlots +
    3 + layout.service.scheme.config.representation.encoding.words + timeBudget layout routines bound limits sampleTime fuel

/-- Numeric address conditions refer only to component allowances. The saved
handler buffer bound is derived from its generated code below. -/
structure AddressBounds (sampleSlots sampleWords : Nat) : Prop where
  sampler : max routines.handler.slots sampleSlots + 5 < 2 ^ w
  handler : Handler.nameBudget layout.service routines.handler sampleSlots +
    CallerHandler.codeBudget layout.service routines.handler bound.handler sampleWords < 2 ^ w

variable (bounded : Caller.Bounds layout caller limits) (sampler : Interactive.Code w) (fuel : Nat)
    {sampleTime sampleWords sampleSlots : Nat}
    (sampleBound : Interactive.TimeBound layout.service.random.port .unit (PairSampling.input w).representation sampler sampleTime)
    (sampleStored : (sampler.lower layout.service.random.port).descriptionWords ≤ sampleWords)
    (sampleNames : WordIO.NamesBound (sampler.lower layout.service.random.port) sampleSlots)
    (sampleFits : (sampler.lower layout.service.random.port).DescriptionFits)
    (addresses : AddressBounds layout routines bound sampleSlots sampleWords)

include bounded sampleStored in
theorem words : ((program layout routines caller sampler fuel).lower layout.service.random.port).descriptionWords ≤
    codeBudget layout routines bound limits sampleWords fuel := by
  have setup := (Setup.bounded layout.service.scheme routines.handler.zeroValid routines.oneValid).code_le
  have invoked := CallerExtraction.words layout routines.handler routines.sub routines.divide routines.subNames.buffers routines.divNames.buffers
    sampler caller.advance caller.continuation caller.localNameFits layout.service.scheme.config.representation caller.initial caller.initialCode
    caller.initialNameFits (inputFits layout) fuel bound.handler bound.sub bound.divide sampleStored bounded.localWords bounded.initialWords
  change descriptionWords (Setup.code layout.service.scheme routines.handler.zeroValid routines.oneValid).code ≤ _ at setup
  change ((tail layout routines caller sampler fuel).lower layout.service.random.port).descriptionWords ≤ _ at invoked
  simp only [program, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute, codeBudget]
  omega

include bounded sampleNames in
theorem names : WordIO.NamesAccounted ((program layout routines caller sampler fuel).lower layout.service.random.port)
    (nameBudget layout routines limits sampleSlots) := by
  have room : 3 ≤ nameBudget layout routines limits sampleSlots := by
    unfold nameBudget Handler.nameBudget
    omega
  have setup := (WordIO.NamesAccounted.compute
    (Setup.names layout.service.scheme routines.handler.zeroValid routines.oneValid).accounted).mono room
  have invoked := CallerExtraction.names layout routines.handler routines.sub routines.divide routines.subNames.buffers routines.divNames.buffers
    sampler caller.advance caller.continuation caller.localNameFits layout.service.scheme.config.representation caller.initial caller.initialCode
    caller.initialNameFits (inputFits layout) fuel sampleNames (Nat.le_max_left _ _)
    (bounded.localNames.mono (Nat.le_max_right _ _)) (bounded.initialNames.mono (Nat.le_max_right _ _))
    routines.subNames.accounted routines.divNames.accounted
  exact setup.seq invoked

include sampleStored sampleNames sampleFits addresses in
theorem descriptionFits : ((program layout routines caller sampler fuel).lower layout.service.random.port).DescriptionFits := by
  have handlerWords := CallerHandler.code_bound layout.service routines.handler bound.handler sampleStored
  have handlerNames := (CallerHandler.names layout.service routines.handler sampleNames).buffers
  have handlerFits : Interactive.savedBuffer layout.service.random.port (CallerHandler.code layout.service routines.handler sampler) < 2 ^ w := by
    have width := layout.service.scheme.wordFits
    have address := addresses.handler
    unfold Interactive.savedBuffer
    omega
  exact .seq layout.service.scheme.wordFits
    (.compute (Setup.code layout.service.scheme routines.handler.zeroValid routines.oneValid).description_fits)
    (CallerExtraction.descriptionFits layout routines.handler routines.sub routines.divide routines.subNames.buffers routines.divNames.buffers
      sampler caller.advance caller.continuation caller.localNameFits layout.service.scheme.config.representation caller.initial caller.initialCode
      caller.initialNameFits (inputFits layout) fuel sampleFits sampleNames addresses.sampler handlerFits)

variable [SampleableType F] (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (sampleCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input w).representation
      layout.service.scheme.scalar.representation (fun _ => sampleSource) sampler)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (invariant : Caller.Invariant layout caller fuel)

include bounded sampleBound sampleCorrect uniform invariant in
theorem time : Interactive.TimeBound layout.service.random.port .unit layout.service.scheme.config.representation
    (program layout routines caller sampler fuel) (timeBudget layout routines bound limits sampleTime fuel) := by
  have setup := Interactive.TimeBound.compute (port := layout.service.random.port) (cost := .unit)
    (Setup.code layout.service.scheme routines.handler.zeroValid routines.oneValid) _
    (Setup.bounded layout.service.scheme routines.handler.zeroValid routines.oneValid).time_le
  have invoked := CallerExtraction.time layout routines.handler routines.sub routines.divide routines.subNames.buffers routines.divNames.buffers
    sampler caller.advance caller.continuation caller.localNameFits layout.service.scheme.config.representation caller.initial caller.initialCode
    caller.initialNameFits (inputFits layout) fuel bound.handler bound.sub bound.divide sampleBound bounded.localTime bounded.initialTime
    sampleSource sampleCorrect uniform invariant.domain invariant.allowed invariant.advance (admitted layout routines)
    (fun value _ => invariant.initial value.1) (admitted_reserved layout routines)
  have composed := Interactive.TimeBoundOn.seq ((setup_refines layout routines).on (fun _ => True))
    (setup.on (fun _ => True)) invoked (by
      intro value _ answer reached
      obtain rfl : answer = start layout routines value := by
        simpa only [support_pure, Set.mem_singleton_iff] using reached
      rfl)
  exact fun tape value before holds => composed tape value trivial before holds

include bounded sampleBound sampleStored sampleNames sampleFits addresses sampleCorrect uniform invariant in
theorem within :
    Interactive.Within layout.service.random.port layout.service.scheme.config layout.service.scheme.scalar
      (codeBudget layout routines bound limits sampleWords fuel)
      (memoryBudget layout routines bound limits sampleTime sampleWords sampleSlots fuel)
      (timeBudget layout routines bound limits sampleTime fuel)
      (fun value => Subtype.val <$> source layout routines caller sampleSource fuel value) :=
  Interactive.within_of_refines_accounted
    (refines layout routines caller sampler sampleSource sampleCorrect uniform fuel invariant)
    (time layout routines caller bound limits bounded sampler fuel sampleBound sampleSource sampleCorrect uniform invariant)
    (words layout routines caller bound limits bounded sampler fuel sampleStored)
    (names layout routines caller limits bounded sampler fuel sampleNames)
    (descriptionFits layout routines caller bound sampler fuel sampleStored sampleNames sampleFits addresses)

variable (witness : Caller.Source layout caller fuel invariant)
    (adversary : _root_.Schnorr.AGM.Adversary F G M)
    (same : ∀ value, (fun answer => Signatures.Runtime.SchnorrAGM.Native.Interface.decodeForgery answer.val) <$>
      witness.program (witness.inputView value) = adversary.main (_root_.Schnorr.AGM.initial value.val.1 value.val.2))

include bounded sampleBound sampleStored sampleNames sampleFits addresses sampleCorrect uniform same in
theorem within_original :
    Interactive.Within layout.service.random.port layout.service.scheme.config layout.service.scheme.scalar
      (codeBudget layout routines bound limits sampleWords fuel)
      (memoryBudget layout routines bound limits sampleTime sampleWords sampleSlots fuel)
      (timeBudget layout routines bound limits sampleTime fuel)
      (fun value => Signatures.Runtime.SchnorrAGM.dlogReduction adversary value.val.1 value.val.2) :=
  (within layout routines caller bound limits bounded sampler fuel sampleBound sampleStored sampleNames sampleFits addresses
    sampleSource sampleCorrect uniform invariant).congr
      (source_original layout routines caller fuel invariant sampleSource uniform witness adversary same)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Full

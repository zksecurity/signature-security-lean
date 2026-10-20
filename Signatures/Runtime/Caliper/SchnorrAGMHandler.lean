import Signatures.Runtime.Caliper.SchnorrAGMHandlerDispatchBounds
import Signatures.Runtime.Caliper.SchnorrAGMHandlerHashMemory
import Signatures.Runtime.Caliper.SchnorrAGMHandlerSigningMemory

/-! The complete Caliper Schnorr service is constructed from five arithmetic
implementations and a scalar sampler. No whole-handler implementation or resource
contract is supplied: random/hash/sign code and dispatch are composed here. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G : Type}
    [Zero F] [Mul F] [Add F] [Neg F] [SMul F G] [Sub G]
    [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS randomBound)

structure Operations where
  zeroValid : layout.scheme.scalar.valid 0
  mul : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 * value.2)
  add : Implementation .unit layout.scheme.affine layout.scheme.scalar (fun value => value.1 + value.2)
  scale : Implementation .unit layout.arithmetic.arithmetic.scaleArgs layout.scheme.point (fun value => value.1 • value.2)
  sub : Implementation .unit layout.arithmetic.arithmetic.points layout.scheme.point (fun value => value.1 - value.2)
  negate : Implementation .unit layout.scheme.scalar layout.scheme.scalar Neg.neg
  slots : Nat
  mulNames : NamesBound mul.program.code slots
  addNames : NamesBound add.program.code slots
  scaleNames : NamesBound scale.program.code slots
  subNames : NamesBound sub.program.code slots
  negateNames : NamesBound negate.program.code slots
  reserve : slots + 4 < 2 ^ w

variable (ops : Operations layout)
def hashCode (sampler : Interactive.Code w) : Interactive.Code w :=
  HashComponent.code layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve layout.random.port sampler
def signingCode (sampler : Interactive.Code w) : Interactive.Code w :=
  SigningComponent.code layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers ops.negateNames.buffers
    ops.reserve layout.random.port sampler
def code (sampler : Interactive.Code w) : Interactive.Code w :=
  Dispatch.code layout (hashCode layout ops sampler) (signingCode layout ops sampler)
def hashSource (sampler : ProbComp layout.scheme.scalar.Value) :=
  HashComponent.source layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve sampler
def signingSource (sampler : ProbComp layout.scheme.scalar.Value) :=
  SigningComponent.source layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers ops.negateNames.buffers
    ops.reserve sampler
def source (sampler : ProbComp layout.scheme.scalar.Value) :=
  Dispatch.source layout (hashSource layout ops sampler) (signingSource layout ops sampler)

variable {sampler : Interactive.Code w} {sampleSource : ProbComp layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines layout.random.port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler)
include sampleCorrect

theorem hash_refines : Interactive.Refines layout.random.port .unit layout.hashInput.representation layout.scalarOutput.representation
    (hashSource layout ops sampleSource) (hashCode layout ops sampler) :=
  HashComponent.refines layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve layout.random.port sampleCorrect
omit [DecidableEq F] in
theorem signing_refines : Interactive.Refines layout.random.port .unit layout.signingInput.representation layout.scalarOutput.representation
    (signingSource layout ops sampleSource) (signingCode layout ops sampler) :=
  SigningComponent.refines layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers ops.negateNames.buffers
    ops.reserve layout.random.port sampleCorrect
theorem refines : Interactive.Refines layout.random.port .unit (Dispatch.input layout) (Dispatch.output layout)
    (source layout ops sampleSource) (code layout ops sampler) :=
  Dispatch.refines layout (hash_refines layout ops sampleCorrect) (signing_refines layout ops sampleCorrect)
omit sampleCorrect

structure Budget where
  mulTime : Nat
  mulWords : Nat
  addTime : Nat
  addWords : Nat
  scaleTime : Nat
  scaleWords : Nat
  subTime : Nat
  subWords : Nat
  negateTime : Nat
  negateWords : Nat
  mul : ops.mul.BoundedBy mulTime mulWords
  add : ops.add.BoundedBy addTime addWords
  scale : ops.scale.BoundedBy scaleTime scaleWords
  sub : ops.sub.BoundedBy subTime subWords
  negate : ops.negate.BoundedBy negateTime negateWords

variable (budget : Budget layout ops)
def timeBudget (sampleTime : Nat) := Dispatch.timeBudget layout
  (HashComponent.timeBudget layout budget.mulTime budget.addTime sampleTime)
  (SigningComponent.timeBudget layout budget.scaleTime budget.subTime budget.negateTime sampleTime)
def codeBudget (sampleWords : Nat) := Dispatch.codeBudget layout
  (HashComponent.codeBudget layout budget.mulWords budget.addWords sampleWords)
  (SigningComponent.codeBudget layout budget.scaleWords budget.subWords budget.negateWords sampleWords)

include sampleCorrect in
theorem time_bound {sampleTime : Nat}
    (sampleBound : Interactive.TimeBound layout.random.port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBound layout.random.port .unit (Dispatch.input layout) (code layout ops sampler) (timeBudget layout ops budget sampleTime) :=
  Dispatch.time_bound layout (hash_refines layout ops sampleCorrect) (signing_refines layout ops sampleCorrect)
    (HashComponent.time_bound layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve layout.random.port
      sampleCorrect budget.mul budget.add sampleBound)
    (SigningComponent.time_bound layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers ops.negateNames.buffers
      ops.reserve layout.random.port sampleCorrect budget.scale budget.sub budget.negate sampleBound)

theorem code_bound {sampleWords : Nat} (sampleBound : (sampler.lower layout.random.port).descriptionWords ≤ sampleWords) :
    ((code layout ops sampler).lower layout.random.port).descriptionWords ≤ codeBudget layout ops budget sampleWords :=
  Dispatch.code_bound layout _ _
    (HashComponent.code_bound layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve layout.random.port sampler
      budget.mul budget.add sampleBound)
    (SigningComponent.code_bound layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers ops.negateNames.buffers
      ops.reserve layout.random.port sampler budget.scale budget.sub budget.negate sampleBound)

def nameBudget (sampleSlots : Nat) := max 5 (max (max 5 (Fresh.nameBudget ops.slots sampleSlots))
  (Signing.Sampling.nameBudget ops.slots sampleSlots))

theorem names {sampleSlots : Nat} (sampleNames : WordIO.NamesBound (sampler.lower layout.random.port) sampleSlots) :
    WordIO.NamesAccounted ((code layout ops sampler).lower layout.random.port) (nameBudget layout ops sampleSlots) :=
  Dispatch.names layout _ _
    ((HashComponent.names layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve layout.random.port sampler
      ops.mulNames ops.addNames sampleNames).mono (Nat.le_max_left _ _))
    ((SigningComponent.names layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers ops.negateNames.buffers
      ops.reserve layout.random.port sampler ops.scaleNames.accounted ops.subNames.accounted ops.negateNames.accounted sampleNames).mono
        (Nat.le_max_right _ _))

theorem descriptionFits {sampleSlots : Nat} (sampleFits : (sampler.lower layout.random.port).DescriptionFits)
    (sampleNames : WordIO.NamesBound (sampler.lower layout.random.port) sampleSlots)
    (reserve : max ops.slots sampleSlots + 5 < 2 ^ w) :
    ((code layout ops sampler).lower layout.random.port).DescriptionFits := by
  have hashed := HashComponent.descriptionFits layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve
    layout.random.port sampler sampleFits ops.addNames sampleNames (by omega)
  have signed := SigningComponent.descriptionFits layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers
    ops.negateNames.buffers ops.reserve layout.random.port sampler sampleFits sampleNames (by omega)
  have hashBuffers := HashComponent.buffers layout ops.zeroValid ops.mul ops.add ops.mulNames.buffers ops.addNames.buffers ops.reserve
    layout.random.port sampler ops.addNames sampleNames
  have signBuffers := SigningComponent.buffers layout ops.zeroValid ops.scale ops.sub ops.negate ops.scaleNames.buffers ops.subNames.buffers
    ops.negateNames.buffers ops.reserve layout.random.port sampler sampleNames
  have words := layout.scheme.wordFits
  apply Dispatch.descriptionFits layout _ _ hashed signed
  · change Interactive.savedBuffer layout.random.port (hashCode layout ops sampler) < 2 ^ w
    unfold Interactive.savedBuffer
    unfold Fresh.nameBudget at hashBuffers
    change ((hashCode layout ops sampler).lower layout.random.port).memBound ≤ _ at hashBuffers
    omega
  · change Interactive.savedBuffer layout.random.port (signingCode layout ops sampler) < 2 ^ w
    unfold Interactive.savedBuffer
    change ((signingCode layout ops sampler).lower layout.random.port).memBound ≤ _ at signBuffers
    omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler

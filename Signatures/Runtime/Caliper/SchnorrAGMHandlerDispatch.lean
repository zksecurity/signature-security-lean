import Signatures.Runtime.Caliper.SchnorrAGMHandlerDispatchLayout
import Signatures.Runtime.Caliper.SchnorrAGMHandlerRandomMemory

/-! Executed three-way Schnorr dispatch. Original requests are copied and held
across each component, then the reply tag and padding are constructed in words.
Hash/signing component realizers are composed by the refinement theorem. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.Dispatch
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Handler.Layouts w M F G qH qS randomBound)

def randomHeld : Interactive.Code w :=
  Interactive.Prefix.code layout.randomInput.representation layout.randomArgs.representation
    (randomRequest layout) (random_prefix layout) layout.scheme.wordFits (random_input_fits layout)
    layout.randomOutput.representation layout.random.port (RandomComponent.code layout)
def hashHeld (body : Interactive.Code w) : Interactive.Code w :=
  Interactive.Prefix.code layout.hashInput.representation layout.groupArgs.representation
    (hashRequest layout) (hash_prefix layout) layout.scheme.wordFits (hash_input_fits layout)
    layout.scalarOutput.representation layout.random.port body
def signingHeld (body : Interactive.Code w) : Interactive.Code w :=
  Interactive.Prefix.code layout.signingInput.representation layout.groupArgs.representation
    (signingRequest layout) (signing_prefix layout) layout.scheme.wordFits (signing_input_fits layout)
    layout.scalarOutput.representation layout.random.port body

def randomCode : Interactive.Code w := .seq (randomHeld layout) (.compute (randomTag layout).code)
def hashCode (body : Interactive.Code w) : Interactive.Code w := .seq (hashHeld layout body) (.compute (hashTag layout).code)
def signingCode (body : Interactive.Code w) : Interactive.Code w := .seq (signingHeld layout body) (.compute (signingTag layout).code)
def groupCode (hashBody signingBody : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (hashCode layout hashBody) (signingCode layout signingBody)
    layout.hashInput.representation.encoding.words layout.signingInput.representation.encoding.words
def code (hashBody signingBody : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (randomCode layout) (groupCode layout hashBody signingBody)
    layout.randomInput.representation.encoding.words (groupInput layout).encoding.words

def randomSource (args : layout.randomInput.Value) : ProbComp (Output layout) :=
  (fun answer => .inl (answer, randomRequest layout args)) <$> RandomComponent.source layout args
def hashSource (source : layout.hashInput.Value → ProbComp layout.scalarOutput.Value)
    (args : layout.hashInput.Value) : ProbComp (Output layout) :=
  (fun answer => .inr (.inl (answer, hashRequest layout args))) <$> source args
def signingSource (source : layout.signingInput.Value → ProbComp layout.scalarOutput.Value)
    (args : layout.signingInput.Value) : ProbComp (Output layout) :=
  (fun answer => .inr (.inr (answer, signingRequest layout args))) <$> source args
def source (hash : layout.hashInput.Value → ProbComp layout.scalarOutput.Value)
    (signing : layout.signingInput.Value → ProbComp layout.scalarOutput.Value) : Input layout → ProbComp (Output layout) :=
  Sum.elim (randomSource layout) (Sum.elim (hashSource layout hash) (signingSource layout signing))

theorem random_held_refines : Interactive.Refines layout.random.port .unit layout.randomInput.representation (randomPacket layout)
    (fun args => (fun answer => (answer, randomRequest layout args)) <$> RandomComponent.source layout args) (randomHeld layout) :=
  Interactive.Prefix.refines _ _ _ (random_prefix layout) _ _ _ (randomPacket layout).fits _ (RandomComponent.refines layout)
theorem hash_held_refines {body : Interactive.Code w} {source : layout.hashInput.Value → ProbComp layout.scalarOutput.Value}
    (correct : Interactive.Refines layout.random.port .unit layout.hashInput.representation layout.scalarOutput.representation source body) :
    Interactive.Refines layout.random.port .unit layout.hashInput.representation (groupPacket layout)
      (fun args => (fun answer => (answer, hashRequest layout args)) <$> source args) (hashHeld layout body) :=
  Interactive.Prefix.refines _ _ _ (hash_prefix layout) _ _ _ (groupPacket layout).fits _ correct
theorem signing_held_refines {body : Interactive.Code w} {source : layout.signingInput.Value → ProbComp layout.scalarOutput.Value}
    (correct : Interactive.Refines layout.random.port .unit layout.signingInput.representation layout.scalarOutput.representation source body) :
    Interactive.Refines layout.random.port .unit layout.signingInput.representation (groupPacket layout)
      (fun args => (fun answer => (answer, signingRequest layout args)) <$> source args) (signingHeld layout body) :=
  Interactive.Prefix.refines _ _ _ (signing_prefix layout) _ _ _ (groupPacket layout).fits _ correct

theorem random_refines : Interactive.Refines layout.random.port .unit layout.randomInput.representation (output layout)
    (randomSource layout) (randomCode layout) := by
  have combined := (random_held_refines layout).seq (Interactive.Refines.compute _ .unit (randomTag layout))
  convert combined using 1
  · funext args
    simp only [bind_pure_comp, Functor.map_map]
    rfl
  · rfl
theorem hash_refines {body : Interactive.Code w} {source : layout.hashInput.Value → ProbComp layout.scalarOutput.Value}
    (correct : Interactive.Refines layout.random.port .unit layout.hashInput.representation layout.scalarOutput.representation source body) :
    Interactive.Refines layout.random.port .unit layout.hashInput.representation (output layout)
      (hashSource layout source) (hashCode layout body) := by
  have combined := (hash_held_refines layout correct).seq (Interactive.Refines.compute _ .unit (hashTag layout))
  convert combined using 1
  · funext args
    simp only [bind_pure_comp, Functor.map_map]
    rfl
  · rfl
theorem signing_refines {body : Interactive.Code w} {source : layout.signingInput.Value → ProbComp layout.scalarOutput.Value}
    (correct : Interactive.Refines layout.random.port .unit layout.signingInput.representation layout.scalarOutput.representation source body) :
    Interactive.Refines layout.random.port .unit layout.signingInput.representation (output layout)
      (signingSource layout source) (signingCode layout body) := by
  have combined := (signing_held_refines layout correct).seq (Interactive.Refines.compute _ .unit (signingTag layout))
  convert combined using 1
  · funext args
    simp only [bind_pure_comp, Functor.map_map]
    rfl
  · rfl

theorem refines {hashBody signingBody : Interactive.Code w}
    {hash : layout.hashInput.Value → ProbComp layout.scalarOutput.Value}
    {signing : layout.signingInput.Value → ProbComp layout.scalarOutput.Value}
    (hashCorrect : Interactive.Refines layout.random.port .unit layout.hashInput.representation layout.scalarOutput.representation hash hashBody)
    (signingCorrect : Interactive.Refines layout.random.port .unit layout.signingInput.representation layout.scalarOutput.representation signing signingBody) :
    Interactive.Refines layout.random.port .unit (input layout) (output layout) (source layout hash signing) (code layout hashBody signingBody) :=
  Interactive.Refines.dispatch _ _ _ (random_refines layout)
    (Interactive.Refines.dispatch _ _ _ (hash_refines layout hashCorrect) (signing_refines layout signingCorrect)
      (width_pos layout.scheme.wordFits) (groupInput layout).fits)
    (width_pos layout.scheme.wordFits) (input layout).fits

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.Dispatch

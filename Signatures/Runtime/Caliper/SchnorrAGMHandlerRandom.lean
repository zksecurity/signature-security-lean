import Signatures.Runtime.Caliper.SchnorrAGMHandlerRandomFinish

/-! Randomness handling over the common Schnorr store. The configuration is
saved in an allocated Caliper buffer, retained across the query, and restored. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G : Type}
  (layout : Handler.Layouts w M F G qH qS randomBound)

def retained : Interactive.Code w :=
  Interactive.retain (SchnorrAGM.Random.code layout.random)
    (Interactive.savedBuffer layout.random.port (SchnorrAGM.Random.code layout.random))
    layout.random.input.representation.encoding.words layout.random.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words
def code : Interactive.Code w := .seq (.compute (prepare layout).code)
  (.seq (retained layout) (.compute (finish layout).code))
def source (args : layout.randomInput.Value) : ProbComp layout.randomOutput.Value :=
  (fun answer => finishValue layout (answer, requestConfig layout args)) <$>
    SchnorrAGM.Random.source layout.random (prepareValue layout args).1

theorem retained_refines : Interactive.Refines layout.random.port .unit (prepared layout) (finished layout)
    (fun args => (fun answer => (answer, args.2)) <$> SchnorrAGM.Random.source layout.random args.1)
    (retained layout) :=
  (SchnorrAGM.Random.refines layout.random).retain (by decide) layout.scheme.config.representation
    layout.scheme.wordFits (inputFits layout) (outputFits layout)
theorem refines : Interactive.Refines layout.random.port .unit layout.randomInput.representation
    layout.randomOutput.representation (source layout) (code layout) := by
  have combined := (Interactive.Refines.compute layout.random.port .unit (prepare layout)).seq
    ((retained_refines layout).seq (Interactive.Refines.compute layout.random.port .unit (finish layout)))
  convert combined using 1
  · funext args
    simp only [pure_bind, bind_pure_comp, Functor.map_map]
    rfl
  · rfl

theorem erase (args : layout.randomInput.Value) :
    Subtype.val <$> source layout args =
      (fun answer : Fin (args.val.1.1 + 1) => ((answer.val, []), args.val.2.1,
        Signatures.Runtime.SchnorrAGM.Native.Random.marked args.val.1.2.1.isEmpty args.val.2.2)) <$>
          (unifSpec.query args.val.1.1) := by
  simp only [source, SchnorrAGM.Random.source, UniformQuery.forwardSource, UniformQuery.source, Functor.map_map]
  rfl

theorem reply_bound (args : layout.randomInput.Value) (answer : layout.randomOutput.Value)
    (supported : answer ∈ support (source layout args)) :
    answer.val.1.1 ≤ args.val.1.1 ∧ answer.val.1.2 = [] ∧
      answer.val.2.1 = args.val.2.1 ∧
      answer.val.2.2 = Signatures.Runtime.SchnorrAGM.Native.Random.marked args.val.1.2.1.isEmpty args.val.2.2 := by
  simp only [source, support_map, Set.mem_image] at supported
  obtain ⟨result, supported, rfl⟩ := supported
  obtain ⟨range, groups, state⟩ := SchnorrAGM.Random.reply_bound layout.random (prepareValue layout args).1 result supported
  exact ⟨range, groups, rfl, state⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent

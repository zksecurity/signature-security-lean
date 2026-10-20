import Signatures.Runtime.Caliper.SchnorrAGMRandomWrap

/-! Every represented randomness request forwards one runtime-selected uniform
query. Malformed requests still draw, preserve stores and return an empty list. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

def forward : Interactive.Code w :=
  UniformQuery.forward randomBound layout.scheme.wordFits layout.rangeFits layout.scheme.state.representation
def code : Interactive.Code w := .seq (.compute (prepareQuery layout).code)
  (.seq (forward layout) (.compute (wrap layout).code))
def source (args : layout.input.Value) : ProbComp layout.output.Value :=
  wrapValue layout <$> UniformQuery.forwardSource randomBound (preparedValue layout args)

theorem refines : Interactive.Refines layout.port .unit layout.input.representation layout.output.representation
    (source layout) (code layout) := by
  have forwarded := UniformQuery.forward_refines randomBound layout.scheme.wordFits layout.rangeFits
    layout.scheme.state.representation layout.frameFits
  have combined := (Interactive.Refines.compute layout.port .unit (prepareQuery layout)).seq
    (forwarded.seq (Interactive.Refines.compute layout.port .unit (wrap layout)))
  convert combined using 1
  · funext args
    simp only [pure_bind, bind_pure_comp]
    rfl
  · rfl

theorem erase (args : layout.input.Value) :
    Subtype.val <$> source layout args =
      (fun answer : Fin (args.val.2.2.1 + 1) => ((answer.val, []),
        Signatures.Runtime.SchnorrAGM.Native.Random.marked args.val.1.isEmpty args.val.2.2.2)) <$>
          (unifSpec.query args.val.2.2.1) := by
  simp only [source, UniformQuery.forwardSource, UniformQuery.source, Functor.map_map]
  rfl

theorem reply_bound (args : layout.input.Value) (answer : layout.output.Value)
    (supported : answer ∈ support (source layout args)) :
    answer.val.1.1 ≤ args.val.2.2.1 ∧ answer.val.1.2 = [] ∧
      answer.val.2 = Signatures.Runtime.SchnorrAGM.Native.Random.marked args.val.1.isEmpty args.val.2.2.2 := by
  simp only [source, UniformQuery.forwardSource, UniformQuery.source, Functor.map_map, support_map, Set.mem_image] at supported
  obtain ⟨sample, _, rfl⟩ := supported
  exact ⟨Nat.le_of_lt_succ sample.isLt, rfl, rfl⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random

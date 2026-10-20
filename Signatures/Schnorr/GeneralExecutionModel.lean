import Signatures.Schnorr.GeneralAGMParameters
import Signatures.Model.CyclicCurve

/-! The separate abstract backend interface, retained for its component-based
results. The public Schnorr AGM theorem uses the concrete Caliper model. -/
namespace Schnorr
open PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native
universe v w

/-- General local computation with measured costs and sizes. Messages need
decidable equality, with no finite-domain requirement. Request equality is used
by the dependent interaction interface; executed comparisons are priced separately. -/
class ExecutionModel (curve : Model.CyclicCurve) where
  steps : StepClass.{0, v}
  [products : steps.HasProd]
  [sums : steps.HasSum]
  [options : steps.HasOption]
  quantitative : QuantitativeStepClass.{0, v, w} steps
  [category : quantitative.HasCategory]
  [quantitativeProducts : quantitative.HasProd]
  [quantitativeSums : quantitative.HasSum]
  [quantitativeOptions : quantitative.HasOption]
  [distributive : quantitative.IsDistributive]
  [optionCode : OptionCode (Q := quantitative)]
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]
  [requestEquality : ∀ n, DecidableEq (Interface.SourceRequest (curve.Scalar n) (curve.Group n) (Message n))]

attribute [instance_reducible, instance] ExecutionModel.products ExecutionModel.sums ExecutionModel.options
  ExecutionModel.category ExecutionModel.quantitativeProducts ExecutionModel.quantitativeSums
  ExecutionModel.quantitativeOptions ExecutionModel.distributive ExecutionModel.optionCode
  ExecutionModel.messageEquality ExecutionModel.requestEquality

end Schnorr

import Signatures.BLS.GeneralCoCDHParameters
import Signatures.Model.PairingCurve

/-! The separate abstract backend interface, retained for its component-based
results. The public BLS AGM and co-CDH statements now use Caliper models. -/
namespace BLS
open PFunctor Signatures.Runtime Signatures.Runtime.BackendProgram
universe v w

class ExecutionModel (curve : Model.PairingCurve) where
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

attribute [instance_reducible, instance] ExecutionModel.products ExecutionModel.sums ExecutionModel.options
  ExecutionModel.category ExecutionModel.quantitativeProducts ExecutionModel.quantitativeSums
  ExecutionModel.quantitativeOptions ExecutionModel.distributive ExecutionModel.optionCode
  ExecutionModel.messageEquality
end BLS

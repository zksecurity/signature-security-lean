import Signatures.Model.PairingCurve
import Signatures.Runtime.GeneralWeightedParameters

/-! Shared execution context for the public weighted-signature statements.
Labels are topics for OOPS and slots for Proximity. They may be infinite.
The quantitative backend measures local code execution and encoded data sizes. -/

open OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace Signatures.Runtime.WeightedAGM

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
  Label : Nat → Type
  [labelEquality : ∀ n, DecidableEq (Label n)]

attribute [instance_reducible, instance] ExecutionModel.products ExecutionModel.sums ExecutionModel.options
  ExecutionModel.category ExecutionModel.quantitativeProducts ExecutionModel.quantitativeSums
  ExecutionModel.quantitativeOptions ExecutionModel.distributive ExecutionModel.optionCode
  ExecutionModel.labelEquality

end Signatures.Runtime.WeightedAGM

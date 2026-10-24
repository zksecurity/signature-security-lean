import Proofs.Runtime.BackendFamily

/-! A bundled fixed backend and its cost/description convention. Equality of
these configurations lets pointwise cryptographic parameters share one machine
across a security-parameter family. Encodings and programs may still vary with
the parameter; execution and code-size measures cannot be chosen per solver. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C} {I : Type}

structure Configuration (Q : QuantitativeStepClass.{0, v, w} C) (spec : OracleSpec I) where
  iface : Interface (C := C) spec
  control : ControlCosts
  queryCost : (i : I) → spec.Range i → Nat
  backend : Backend.{v, w, x} Q spec iface control queryCost
  sizes : DescriptionSize Q
  factor : Nat
  description : backend.DescriptionBound sizes factor

namespace Configuration

variable {spec : OracleSpec I} (config : Configuration.{v, w, x} Q spec)

def within {A B : Type} (a : C.Str A) (b : C.Str B)
    (inputSize codeSize time : Nat) (algorithm : A → OracleComp spec B) : Prop :=
  Within config.backend config.sizes config.factor config.description a b inputSize codeSize time algorithm

def nonuniformWithin {A B : Nat → Type} (a : ∀ n, C.Str (A n)) (b : ∀ n, C.Str (B n))
    (inputSize : Nat → Nat) (algorithm : ∀ n, A n → OracleComp spec (B n)) : Prop :=
  NonuniformWithin config.backend config.sizes config.factor config.description a b inputSize algorithm

theorem nonuniformWithin_of_pointwise {A B : Nat → Type}
    (a : ∀ n, C.Str (A n)) (b : ∀ n, C.Str (B n))
    (inputSize codeSize time : Nat → Nat) (algorithm : ∀ n, A n → OracleComp spec (B n))
    (hi : PolynomiallyBounded inputSize) (hc : PolynomiallyBounded codeSize)
    (ht : PolynomiallyBounded time)
    (hw : ∀ n, config.within (a n) (b n) (inputSize n) (codeSize n) (time n) (algorithm n)) :
    config.nonuniformWithin a b inputSize algorithm :=
  NonuniformWithin.of_pointwise config.backend config.sizes config.factor config.description
    a b inputSize algorithm codeSize time hi hc ht hw

end Configuration

end Signatures.Runtime.BackendProgram

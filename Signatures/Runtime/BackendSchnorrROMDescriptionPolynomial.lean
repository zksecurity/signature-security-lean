import Signatures.Runtime.BackendSchnorrROMDescriptionInputs
import Signatures.Runtime.BackendDescriptionPolynomial

/-! Polynomial stored code for the complete native Schnorr ROM solver, from
the original caller/sampler/primitive/port descriptions. The numerical formula
is exactly the existing complete stored-code budget, via `codeDescription_eq`. -/

namespace Signatures.Runtime.Schnorr.ListROM.NativeSolver

open BackendProgram RawTape

namespace DescriptionInputs

structure Polynomial (d : Nat → DescriptionInputs) : Prop where
  primitive : ∀ {a b} (op : CryptoOp a b), PolynomiallyBounded (fun n => (d n).primitiveSize op)
  samplerSize : PolynomiallyBounded (fun n => (d n).samplerSize)
  callerInit : PolynomiallyBounded (fun n => (d n).callerInit)
  callerHead : PolynomiallyBounded (fun n => (d n).callerHead)
  callerUpdate : PolynomiallyBounded (fun n => (d n).callerUpdate)
  inputPort : PolynomiallyBounded (fun n => (d n).inputPort)
  outputPort : PolynomiallyBounded (fun n => (d n).outputPort)
  optionalPort : PolynomiallyBounded (fun n => (d n).optionalPort)
  requestPort : PolynomiallyBounded (fun n => (d n).requestPort)
  randomTag : PolynomiallyBounded (fun n => (d n).randomTag)
  hashTag : PolynomiallyBounded (fun n => (d n).hashTag)
  signingTag : PolynomiallyBounded (fun n => (d n).signingTag)
  uniformRequest : PolynomiallyBounded (fun n => (d n).uniformRequest)
  uniformResponse : PolynomiallyBounded (fun n => (d n).uniformResponse)
  privateArity : PolynomiallyBounded (fun n => (d n).privateArity)
  privateReply : PolynomiallyBounded (fun n => (d n).privateReply)
  rejectSize : PolynomiallyBounded (fun n => (d n).rejectSize)
  acceptSize : PolynomiallyBounded (fun n => (d n).acceptSize)

theorem solver_polynomial (d : Nat → DescriptionInputs) (allowance fuel qH : Nat → Nat)
    (h : Polynomial d) (hAllowance : PolynomiallyBounded allowance)
    (hFuel : PolynomiallyBounded fuel) (hQueries : PolynomiallyBounded qH) :
    PolynomiallyBounded (fun n => (d n).solver (allowance n) (fuel n) (qH n)) := by
  have expressionPoly {Γ a} (e : Expr CryptoOp Γ a) :
      PolynomiallyBounded (fun n => Expression.descriptionBound (allowance n) (d n).primitiveSize e) :=
    Expression.descriptionBound_polynomial allowance (fun n => (d n).primitiveSize) hAllowance h.primitive e
  have programPoly {Γ a} (body : Program CryptoOp (SampledCache.Draw scalar) Γ a) :
      PolynomiallyBounded (fun n => Language.descriptionBound (allowance n) (d n).primitiveSize (fun _ => 0) body) :=
    Language.descriptionBound_polynomial allowance (fun n => (d n).primitiveSize) (fun _ _ => 0)
      hAllowance h.primitive (fun _ => PolynomiallyBounded.const 0) body
  rcases h with ⟨hp, hs, hci, hch, hcu, hi, ho, hn, hr, hrt, hht, hst, hur, hus, hpa, hpr, hrej, hacc⟩
  unfold solver fork pass handler privateHandler uniform challenge live managed signing extraction
    NativeFork.adapterDescription
  repeat' first
    | assumption
    | apply expressionPoly
    | apply programPoly
    | apply hp
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

theorem compiled_polynomial (d : Nat → DescriptionInputs) (factor allowance fuel qH : Nat → Nat)
    (h : Polynomial d) (hFactor : PolynomiallyBounded factor) (hAllowance : PolynomiallyBounded allowance)
    (hFuel : PolynomiallyBounded fuel) (hQueries : PolynomiallyBounded qH) :
    PolynomiallyBounded (fun n => factor n * (d n).solver (allowance n) (fuel n) (qH n)) :=
  hFactor.mul (solver_polynomial d allowance fuel qH h hAllowance hFuel hQueries)

end DescriptionInputs

end Signatures.Runtime.Schnorr.ListROM.NativeSolver

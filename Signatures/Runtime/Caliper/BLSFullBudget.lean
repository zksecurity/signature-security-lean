import Signatures.Runtime.Caliper.BLSFullCorrectness

/-! Component ledgers and derived complete-solver budgets. The assumptions are
only bounds for named primitive routines and local caller steps. Setup, query
handling and extraction costs are obtained from their constructed programs. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource
structure Budget where
  time : Nat
  words : Nat

section Components
variable {w : Nat} {M F G K A : Type}
    [Zero F] [Mul F] [Add F] [Sub F] [Neg F] [Div F] [SMul F G] [Add G] [SMul F K]
    (layout : Layouts w M F G K A) (routines : Routines layout)
structure Routines.Bounds where
  mul : Budget
  add : Budget
  sub : Budget
  neg : Budget
  divide : Budget
  scale : Budget
  groupAdd : Budget
  key : Budget
  mulBound : routines.scalarMul.BoundedBy mul.time mul.words
  addBound : routines.scalarAdd.BoundedBy add.time add.words
  subBound : routines.scalarSub.BoundedBy sub.time sub.words
  negBound : routines.scalarNeg.BoundedBy neg.time neg.words
  divBound : routines.scalarDiv.BoundedBy divide.time divide.words
  scaleBound : routines.groupScale.BoundedBy scale.time scale.words
  groupAddBound : routines.groupAdd.BoundedBy groupAdd.time groupAdd.words
  keyBound : routines.keyScale.BoundedBy key.time key.words
end Components

variable {w : Nat} {M F G K A : Type} (layout : Layouts w M F G K A) (caller : Caller layout)
structure Caller.Bounds where
  step : Budget
  initial : Budget
  localTime : ∀ value, caller.continuation.time value ≤ step.time
  initialTime : ∀ value, caller.initialCode.time value ≤ initial.time
  localWords : descriptionWords caller.continuation.code ≤ step.words
  initialWords : descriptionWords caller.initialCode.code ≤ initial.words
  names : Nat
  localNames : NamesAccounted caller.continuation.code names
  initialNames : NamesAccounted caller.initialCode.code names

variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [Zero (val.Value base)] [Mul (val.Value base)] [Add (val.Value base)]
    [Sub (val.Value base)] [Neg (val.Value base)] [Div (val.Value base)] [SMul (val.Value base) G] [Add G] [SMul (val.Value base) K]
    (layout : Layouts w (key.Value base) (val.Value base) G K A) (routines : Routines layout)
    (bound : Routines.Bounds layout routines) (caller : Caller layout) (localBound : Caller.Bounds layout caller)

def goodExtractionTime (drawTime : Nat) := BLSExtractor.goodTime (base := base) (key := key) (val := val)
  layout.tokens drawTime bound.mul.time bound.add.time bound.sub.time bound.divide.time
def badExtractionTime (drawTime : Nat) := BLSExtractor.badTime (base := base) (key := key) (val := val)
  layout.tokens drawTime bound.mul.time bound.add.time bound.sub.time bound.neg.time bound.divide.time
def goodExtractionWords (drawWords : Nat) := BLSExtractor.goodWords (base := base) (key := key) (val := val)
  layout.tokens drawWords bound.mul.words bound.add.words bound.sub.words bound.divide.words
def badExtractionWords (drawWords : Nat) := BLSExtractor.badWords (base := base) (key := key) (val := val)
  layout.tokens drawWords bound.mul.words bound.add.words bound.sub.words bound.neg.words bound.divide.words

def goodTailTime (drawTime fuel : Nat) := BLSCallerExtraction.timeBudget (base := base) (key := key) (val := val)
  layout.good layout.key.representation.encoding.words drawTime (fun _ => BLSResponse.goodTime layout.scheme.response bound.scale.time)
    localBound.step.time localBound.initial.time fuel (goodExtractionTime layout routines bound drawTime)
def badTailTime (drawTime fuel : Nat) := BLSCallerExtraction.timeBudget (base := base) (key := key) (val := .pair val val)
  layout.bad layout.key.representation.encoding.words
    (PairSampling.timeBudget layout.scheme.cache.value layout.scheme.cache.value drawTime drawTime)
    (fun signing => BLSResponse.badTime layout.scheme.response signing bound.scale.time bound.groupAdd.time)
    localBound.step.time localBound.initial.time fuel (badExtractionTime layout routines bound drawTime)
def goodTailWords (drawWords fuel : Nat) := BLSCallerExtraction.codeBudget (base := base) (key := key) (val := val)
  layout.good layout.key.representation.encoding.words drawWords (fun _ => BLSResponse.goodWords layout.scheme.response bound.scale.words)
    localBound.step.words localBound.initial.words fuel (goodExtractionWords layout routines bound drawWords)
def badTailWords (drawWords fuel : Nat) := BLSCallerExtraction.codeBudget (base := base) (key := key) (val := .pair val val)
  layout.bad layout.key.representation.encoding.words
    (PairSampling.codeBudget layout.scheme.cache.value layout.scheme.cache.value drawWords drawWords)
    (fun signing => BLSResponse.badWords layout.scheme.response signing bound.scale.words bound.groupAdd.words)
    localBound.step.words localBound.initial.words fuel (badExtractionWords layout routines bound drawWords)

def goodTime (drawTime fuel : Nat) := 200 * layout.setup.width + goodTailTime layout routines bound caller localBound drawTime fuel
def badTime (drawTime fuel : Nat) := BLSSetup.badTime layout.setup drawTime bound.key.time + badTailTime layout routines bound caller localBound drawTime fuel
def goodWords (drawWords fuel : Nat) := 700 * layout.setup.width + 251 + goodTailWords layout routines bound caller localBound drawWords fuel + 1
def badWords (drawWords fuel : Nat) := BLSSetup.badWords layout.setup drawWords bound.key.words + badTailWords layout routines bound caller localBound drawWords fuel + 1

def nameBudget (drawNames : Nat) := max (BLSExtractor.nameBudget drawNames routines.slots) localBound.names
end Signatures.Runtime.CaliperBackend.BLSFull

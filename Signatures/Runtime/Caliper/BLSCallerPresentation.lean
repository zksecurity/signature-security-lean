import Signatures.Runtime.Caliper.BLSFullSource
import Signatures.Runtime.Caliper.CallerPresentation

/-! A BLS caller supplies local Caliper code, not a second hand-built oracle
machine. This constructor derives that machine, its finite source tree and both
source-correspondence proofs. Point representation is complete; public-key
representation may be restricted. A represented fallback key totalizes only the
mathematical source outside the execution domain. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull.Caller
open Caliper OracleComp OracleSpec

variable {w : Nat} {M F G K A : Type}
    (layout : Layouts w M F G K A)
    (pointValid : ∀ point, layout.scheme.point.valid point)

/-- Represent an original oracle answer in the caller's reply packet. This is
the mathematical interface conversion already performed by the proved handler. -/
def representReply : (q : layout.Request) →
    (Model.LazyAGM.advSpec M M G).Range (BLSCallerHandler.query layout.good.service layout.randomBound q) → layout.Reply
  | .inl n, answer => .inl ⟨n, answer⟩
  | .inr (.inl _), point | .inr (.inr _), point => .inr ⟨point, pointValid point⟩

theorem representReply_eq (q : layout.Request) (represented : layout.Reply)
    (original : (Model.LazyAGM.advSpec M M G).Range (BLSCallerHandler.query layout.good.service layout.randomBound q))
    (related : BLSCallerHandler.replyMatches layout.good.service layout.randomBound q represented original) :
    represented = representReply layout pointValid q original := by
  rcases q with n | (message | message)
  · cases represented with
    | inl random =>
        have equal := Prod.mk.inj (Sum.inl.inj related)
        congr 1
        exact Sigma.ext (Fin.ext equal.1) (by cases Fin.ext equal.1; exact heq_of_eq (Fin.ext equal.2))
    | inr point => cases related
  · cases represented with
    | inl random => cases related
    | inr point => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj related))
  · cases represented with
    | inl random => cases related
    | inr point => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj related))

private theorem bad_query_eq_good :
    BLSCallerHandler.query layout.bad.service layout.randomBound =
      BLSCallerHandler.query layout.good.service layout.randomBound := by
  funext q
  rcases q with n | (message | message) <;> rfl

variable (caller : Caller layout)
    (fallback : layout.key.Value)

noncomputable def initialOnKeys : K → layout.Next :=
  CallerMachine.extendInput layout.key.valid fallback caller.initial

theorem initialOnKeys_valid (key : layout.key.Value) :
    initialOnKeys layout caller fallback key.val = caller.initial key :=
  CallerMachine.extendInput_valid _ _ _ key

/-- Local termination is the only oracle-machine obligation: every reply path
returns within the allowance. Caliper code/time/memory remain separately charged. -/
def Terminates (fuel : Nat) : Prop := ∀ key : layout.key.Value,
  CallerMachine.Terminates (BLSCallerHandler.query layout.good.service layout.randomBound)
    (representReply layout pointValid) caller.advance fuel (caller.initial key)

variable {fuel : Nat} (invariant : Invariant layout caller fuel)

theorem initialOnKeys_terminates (terminates : Terminates layout pointValid caller fuel) (key : K) :
    CallerMachine.Terminates (BLSCallerHandler.query layout.good.service layout.randomBound)
      (representReply layout pointValid) caller.advance fuel (initialOnKeys layout caller fallback key) :=
  CallerMachine.extendInput_property _ _ _ _ terminates key

noncomputable def Correspondence.ofCaller
    (terminates : Terminates layout pointValid caller fuel) :
    Correspondence layout caller invariant where
  machine := CallerMachine.ofCaller (BLSCallerHandler.query layout.good.service layout.randomBound)
    (representReply layout pointValid) caller.advance (initialOnKeys layout caller fallback)
  stateView := Sum.inr
  source := CallerMachine.sourceOfCaller (BLSCallerHandler.query layout.good.service layout.randomBound)
    (representReply layout pointValid) caller.advance (initialOnKeys layout caller fallback) fuel
      (initialOnKeys_terminates layout pointValid caller fallback terminates)
  implements := CallerMachine.ofCaller_implements _ _ _ _ _
    (initialOnKeys_terminates layout pointValid caller fallback terminates)
  goodAdvance := fun _ q c _ next view represented original related =>
    CallerMachine.ofCaller_advance _ _ _ _ q c next view represented original
      (representReply_eq layout pointValid q represented original related)
  badAdvance := by
    intro remaining q c valid next view represented original related
    rw [bad_query_eq_good layout]
    rcases q with n | (message | message)
    · exact CallerMachine.ofCaller_advance
        (BLSCallerHandler.query layout.good.service layout.randomBound)
        (representReply layout pointValid) caller.advance (initialOnKeys layout caller fallback)
        (.inl n) c next view represented original
        (representReply_eq layout pointValid (.inl n) represented original (by
          cases represented <;> exact related))
    · exact CallerMachine.ofCaller_advance
        (BLSCallerHandler.query layout.good.service layout.randomBound)
        (representReply layout pointValid) caller.advance (initialOnKeys layout caller fallback)
        (.inr (.inl message)) c next view represented original
        (representReply_eq layout pointValid (.inr (.inl message)) represented original (by
          cases represented <;> exact related))
    · exact CallerMachine.ofCaller_advance
        (BLSCallerHandler.query layout.good.service layout.randomBound)
        (representReply layout pointValid) caller.advance (initialOnKeys layout caller fallback)
        (.inr (.inr message)) c next view represented original
        (representReply_eq layout pointValid (.inr (.inr message)) represented original (by
          cases represented <;> exact related))

  goodInitial := by
    intro value
    change CallerMachine.Matches
      (CallerMachine.ofCaller (spec := Model.LazyAGM.advSpec M M G)
        (BLSCallerHandler.query layout.good.service layout.randomBound)
        (representReply layout pointValid) caller.advance (initialOnKeys layout caller fallback))
      (BLSCallerHandler.query layout.good.service layout.randomBound) Sum.inr
      (caller.initial value) (initialOnKeys layout caller fallback value.val)
    rw [initialOnKeys_valid]
    exact CallerMachine.ofCaller_matches _ _ _ _ (caller.initial value)
  badInitial := by
    intro value
    rw [bad_query_eq_good layout]
    change CallerMachine.Matches
      (CallerMachine.ofCaller (spec := Model.LazyAGM.advSpec M M G)
        (BLSCallerHandler.query layout.good.service layout.randomBound)
        (representReply layout pointValid) caller.advance (initialOnKeys layout caller fallback))
      (BLSCallerHandler.query layout.good.service layout.randomBound) Sum.inr
      (caller.initial value) (initialOnKeys layout caller fallback value.val)
    rw [initialOnKeys_valid]
    exact CallerMachine.ofCaller_matches _ _ _ _ (caller.initial value)

end Signatures.Runtime.CaliperBackend.BLSFull.Caller

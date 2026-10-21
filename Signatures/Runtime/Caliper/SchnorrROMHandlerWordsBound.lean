import Signatures.Runtime.Caliper.SchnorrROMHandlerBounds
import Signatures.Runtime.Caliper.SchnorrROMEnumeratedBounds

/-! Stored-code budgets of the private sampler stack with the caller's two
concrete code sizes abstracted. The handler's signing code budget embeds the
enumerated sampler's actual programs, whose description sizes are known
constants; stating the budget over those constants gives a formula in layout
widths alone, which the polynomial-family corollary can bound. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler
open Caliper BoundedSource
variable {w : Nat} {F C : Type} [Zero F] (layout : Layouts w F C) (zeroValid : layout.tape.scalar.valid 0)

def wordsOf (fuel initialWords continuationWords : Nat) : Nat :=
  initialWords + 26 * layout.tape.unit.representation.encoding.words + 507 * CallerStep.width (step layout) + 286 +
  fuel * (PrivateQuery.codeBudget layout.tape zeroValid + continuationWords + 742 * CallerStep.width (step layout) + 389)

theorem codeBudget_le_wordsOf (caller : Caller layout) {initialWords continuationWords : Nat}
    (initial : descriptionWords caller.initialCode.code ≤ initialWords)
    (continuation : descriptionWords caller.continuation.code ≤ continuationWords) (fuel : Nat) :
    codeBudget layout caller zeroValid fuel ≤ wordsOf layout zeroValid fuel initialWords continuationWords := by
  have query := PrivateQuery.code_bound layout.tape zeroValid
  unfold codeBudget CallerControl.programWords CallerControl.iterationWords wordsOf
  have inner : ((PrivateQuery.code layout.tape zeroValid).lower (Fresh.port layout.tape)).descriptionWords +
      descriptionWords caller.continuation.code + 742 * CallerStep.width (step layout) + 389 ≤
      PrivateQuery.codeBudget layout.tape zeroValid + continuationWords + 742 * CallerStep.width (step layout) + 389 := by omega
  have scaled := Nat.mul_le_mul_left fuel inner
  omega

namespace Service
def wordsOf (fuel initialWords continuationWords : Nat) : Nat :=
  PrivateSampler.wordsOf layout zeroValid fuel initialWords continuationWords + 325 * CallerStep.width (step layout) + 189
theorem codeBudget_le_wordsOf (caller : Caller layout) {initialWords continuationWords : Nat}
    (initial : descriptionWords caller.initialCode.code ≤ initialWords)
    (continuation : descriptionWords caller.continuation.code ≤ continuationWords) (fuel : Nat) :
    codeBudget layout caller zeroValid fuel ≤ wordsOf layout zeroValid fuel initialWords continuationWords := by
  have := PrivateSampler.codeBudget_le_wordsOf layout zeroValid caller initial continuation fuel
  unfold codeBudget wordsOf
  omega
end Service

namespace Pair
def wordsOf (fuel initialWords continuationWords : Nat) : Nat :=
  2 * Service.wordsOf layout zeroValid fuel initialWords continuationWords +
  26 * (Read.tapes layout.tape).representation.encoding.words +
  78 * (Reply.scalarOutput layout.tape).representation.encoding.words + 65 * layout.tape.scalar.representation.encoding.words + 74
theorem codeBudget_le_wordsOf (caller : Caller layout) {initialWords continuationWords : Nat}
    (initial : descriptionWords caller.initialCode.code ≤ initialWords)
    (continuation : descriptionWords caller.continuation.code ≤ continuationWords) (fuel : Nat) :
    codeBudget layout caller zeroValid fuel ≤ wordsOf layout zeroValid fuel initialWords continuationWords := by
  have := Nat.mul_le_mul_left 2 (Service.codeBudget_le_wordsOf layout zeroValid caller initial continuation fuel)
  unfold codeBudget wordsOf
  omega
end Pair
end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler

namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G C : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G C) (zeroValid : layout.sampler.tape.scalar.valid 0)

def wordsOf (fuel initialWords continuationWords scaleWords subWords : Nat) : Nat :=
  PrivateSampler.Pair.wordsOf layout.sampler zeroValid fuel initialWords continuationWords +
  26 * layout.prepared.encoding.words + 26 * (Read.tapes layout.sampler.tape).representation.encoding.words +
  26 * (PrivateSampler.Pair.output layout.sampler).representation.encoding.words + 39 * layout.context.representation.encoding.words +
  finishWords layout scaleWords subWords + 59
omit [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] in
theorem codeBudget_le_wordsOf (caller : PrivateSampler.Caller layout.sampler) {initialWords continuationWords : Nat}
    (initial : descriptionWords caller.initialCode.code ≤ initialWords)
    (continuation : descriptionWords caller.continuation.code ≤ continuationWords) (fuel scaleWords subWords : Nat) :
    codeBudget layout zeroValid caller fuel scaleWords subWords ≤ wordsOf layout zeroValid fuel initialWords continuationWords scaleWords subWords := by
  have := PrivateSampler.Pair.codeBudget_le_wordsOf layout.sampler zeroValid caller initial continuation fuel
  unfold codeBudget wordsOf
  omega
end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler

namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Handler
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Operations config) (budget : Budget config ops)

/-- The signing code budget as a formula in layout widths, with the enumerated
sampler's initialization (66 words) and continuation (161 words) code sizes. -/
def signingWordsBound : Nat := Signing.Handler.wordsOf config.handler trivial 1 66 161 budget.scaleWords budget.subWords
omit [DecidableEq M] [DecidableEq G] in
theorem signingWords_le : signingWords config ops budget ≤ signingWordsBound config ops budget :=
  Signing.Handler.codeBudget_le_wordsOf config.handler trivial (PrivateSampler.Enumerated.caller config.sampler)
    (PrivateSampler.Enumerated.initial_words config.sampler) (PrivateSampler.Enumerated.continuation_words config.sampler) 1 _ _
def codeBudgetBound : Nat := Random.codeBudget config + Hash.codeBudget config + signingWordsBound config ops budget +
  1400 * config.handler.width + 200
theorem codeBudget_le : codeBudget config ops budget ≤ codeBudgetBound config ops budget := by
  have := signingWords_le config ops budget
  unfold codeBudget codeBudgetBound
  omega
end Signatures.Runtime.CaliperBackend.SchnorrROM.Handler

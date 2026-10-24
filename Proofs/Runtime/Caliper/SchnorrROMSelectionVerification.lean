import Proofs.Runtime.Caliper.SchnorrROMSelectionLayout

/-! Executed signature verification using the existing two scalar products and
group subtraction. Encoded point equality is a word scan. Every argument and
retained commitment is copied by code accounted for in the verification budget. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
open Caliper BoundedSource
variable {w : Nat} {M F G : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq G]
    (config : Signing.Enumerated.Configuration w M F G) (ops : Handler.Operations config)

def point : Implementation .unit (input config) config.point
    (fun value => value.1.1.2.2 • value.2.1.1.1 - value.1.2 • value.2.1.1.2) :=
  ((verifyInput config).implementation.then
    (BLSResponse.pointArguments config.handler.core.arithmetic ops.scale ops.scaleNames.buffers ops.reserve)).then ops.sub
omit [DecidableEq G] in
theorem point_buffers : (point config ops).program.code.memBound ≤ max 5 ops.slots + 1 := by
  have prepared : (verifyInput config).implementation.program.code.memBound ≤ 5 := (verifyInput config).buffers_le
  have products := BLSResponse.pointArguments_buffers config.handler.core.arithmetic ops.scale ops.scaleNames.buffers ops.reserve
  have subtracted := ops.subNames.buffers
  change max (max _ _) _ ≤ _
  exact max_le (max_le (prepared.trans (by omega)) (products.trans (by omega))) (subtracted.trans (by omega))
omit [DecidableEq G] in
theorem point_names : NamesAccounted (point config ops).program.code ops.slots :=
  (((verifyInput config).names ops.slots).seq
    (BLSResponse.pointArguments_names config.handler.core.arithmetic ops.slots ops.scale ops.scaleNames.accounted ops.scaleNames.buffers ops.reserve)).seq
      ops.subNames.accounted

def comparison : Implementation .unit (input config) config.handler.core.arithmetic.points
    (fun value => (value.1.1.2.2 • value.2.1.1.1 - value.1.2 • value.2.1.1.2, value.1.1.2.1)) :=
  (point config ops).pair (getCommitment config).implementation (by decide) config.sampler.wordFits
    (by have := point_buffers config ops; have := config.sampler.wordFits; have := ops.reserve; change max 2 _ < _; omega)
    (by have bound : (getCommitment config).implementation.program.code.memBound ≤ 2 := (getCommitment config).buffers_le
        have := config.sampler.wordFits; change max 2 _ < _; omega)
    (duplicate config)
    (config.handler.fits_of_le (by
      have := (sizes config).1; have key := FinalHash.key_le config
      change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
      omega)) config.handler.core.arithmetic.points.representation.fits
def verified (value : Input M F G) := decide (value.1.1.2.2 • value.2.1.1.1 - value.1.2 • value.2.1.1.2 = value.1.1.2.1)
def verify : Implementation .unit (input config) (boolean config) verified :=
  (comparison config ops).then
    (EncodedEquality.implementation .unit config.point config.sampler.wordFits config.handler.core.arithmetic.points.representation.fits)
theorem verify_buffers : (verify config ops).program.code.memBound ≤ max 5 ops.slots + 2 := by
  have paired : (comparison config ops).program.code.memBound ≤ max 2 (max (max 5 ops.slots + 1) 2) + 1 :=
    Implementation.pair_buffers (firstBuffers := max 5 ops.slots + 1) (secondBuffers := 2)
    (point config ops) (getCommitment config).implementation config.sampler.wordFits _ _ _ _ _
    (point_buffers config ops) (getCommitment config).buffers_le
  have compared := (EncodedEquality.implementation_names .unit config.point config.sampler.wordFits
    config.handler.core.arithmetic.points.representation.fits).buffers
  change max (comparison config ops).program.code.memBound _ ≤ _
  exact max_le (paired.trans (by omega)) (compared.trans (by omega))
theorem verify_names : NamesAccounted (verify config ops).program.code ops.slots := by
  have paired : NamesAccounted (comparison config ops).program.code ops.slots :=
    Implementation.pair_names (point config ops) (getCommitment config).implementation
    config.sampler.wordFits _ _ _ _ _ (point_names config ops) ((getCommitment config).names ops.slots)
  have compared := (EncodedEquality.implementation_names .unit config.point config.sampler.wordFits
    config.handler.core.arithmetic.points.representation.fits).mono (b := ops.slots +
      descriptionWords (EncodedEquality.code (w := w) config.point.representation.encoding.words)) (by
        rw [EncodedEquality.code_descriptionWords]; omega)
  exact paired.seq compared

variable (budget : Handler.Budget config ops)
def pointBudget : Budget :=
  ((verifyInput config).budget.seq
    ⟨2 * budget.scaleTime + 604 + 476 * config.point.representation.encoding.words,
      2 * budget.scaleWords + 1963 + 1547 * config.point.representation.encoding.words + 520⟩).seq
    ⟨budget.subTime, budget.subWords⟩
omit [DecidableEq G] in
theorem point_bounded : (point config ops).BoundedBy (pointBudget config ops budget).time (pointBudget config ops budget).words :=
  (((verifyInput config).bounded.then
    (BLSResponse.pointArguments_bounded config.handler.core.arithmetic ops.scale budget.scale ops.scaleNames.buffers ops.reserve)).then budget.sub)
def verificationBudget : Budget :=
  (Budget.pair (input config).representation.encoding.words config.point.representation.encoding.words config.point.representation.encoding.words
    (pointBudget config ops budget) (getCommitment config).budget).seq
      ⟨6 * config.point.representation.encoding.words + 3, 30 * config.point.representation.encoding.words + 13⟩
theorem verify_bounded : (verify config ops).BoundedBy
    (verificationBudget config ops budget).time (verificationBudget config ops budget).words :=
  (Implementation.pair_boundedBy (point config ops) (getCommitment config).implementation _ _ _ _ _ _
    (point_bounded config ops budget) (getCommitment config).bounded).then
      (EncodedEquality.implementation_boundedBy config.point config.sampler.wordFits config.handler.core.arithmetic.points.representation.fits)

end Signatures.Runtime.CaliperBackend.SchnorrROM.Selection

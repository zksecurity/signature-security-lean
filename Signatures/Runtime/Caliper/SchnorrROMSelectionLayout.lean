import Signatures.Runtime.Caliper.ChronologicalIndex
import Signatures.Runtime.Caliper.SchnorrROMPassGrowth

/-! The selector reads the returned forgery, challenge, public points and LIVE
table. All projections and reconstructed arguments are charged programs. The
managed cache is not consulted when locating the forgery's challenge. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Selection
open Caliper BoundedSource SchnorrROMTape
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

abbrev Input (M F G : Type) := ((M × G × F) × F) × Schnorr.ListROM.Shared.Store F G M
def hashed := (ForgeryHash.forgery config).prod config.handler.sampler.tape.scalar (ForgeryHash.result config).fits
def input : Layout w (Input M F G) := (hashed config).prod config.handler.store (ForgeryHash.output config).fits
def tables := config.handler.core.table.prod config.handler.core.table
  (config.handler.fits_of_le (by have := config.handler.table_le; omega))
def chronology : ChronologicalIndex.Layouts w (M × G) F where
  key := config.handler.core.key
  value := config.handler.sampler.tape.scalar
  capacity := config.capacityPred + 1
  wordFits := config.sampler.wordFits
  countFits := by have := config.countFits; omega
  storageFits := by
    apply config.handler.fits_of_le
    change 16 * (4 + (config.capacityPred + 1 + 2) * (config.message.representation.encoding.words +
      config.point.representation.encoding.words + 1) + (config.message.representation.encoding.words + config.point.representation.encoding.words)) ≤ _
    change _ ≤ 128 * (1 + (config.capacityPred + 1) * (config.message.representation.encoding.words +
      config.point.representation.encoding.words + 1) + 3 + 3 * config.point.representation.encoding.words +
      config.message.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words)
    nlinarith
def result := (chronology config).result
def boolean := (chronology config).boolean
theorem sizes : (input config).representation.encoding.words ≤ 8 * config.handler.width ∧
    config.handler.core.arithmetic.badInput.representation.encoding.words ≤ 8 * config.handler.width ∧
    (chronology config).width ≤ 8 * config.handler.width := by
  have key := FinalHash.key_le config
  have saved := FinalHash.store_le config
  have positive := Random.positive config
  change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at key
  constructor
  · change ((config.message.representation.encoding.words + (config.point.representation.encoding.words + 1)) + 1) + _ ≤ _
    omega
  constructor
  · change (1 + 1) + (1 + (config.point.representation.encoding.words + config.point.representation.encoding.words)) ≤ _
    omega
  · change 4 + (config.capacityPred + 1 + 2) * (config.message.representation.encoding.words +
      config.point.representation.encoding.words + 1) + (config.message.representation.encoding.words + config.point.representation.encoding.words) ≤ _
    change _ ≤ 8 * (1 + (config.capacityPred + 1) * (config.message.representation.encoding.words +
      config.point.representation.encoding.words + 1) + 3 + 3 * config.point.representation.encoding.words +
      config.message.representation.encoding.words + (Read.tapes config.handler.sampler.tape).representation.encoding.words)
    nlinarith
theorem duplicate : (input config).representation.encoding.words + (input config).representation.encoding.words < 2 ^ w :=
  config.handler.fits_of_le (by have := (sizes config).1; omega)
theorem tagged : 1 + (input config).representation.encoding.words < 2 ^ w :=
  config.handler.fits_of_le (by have := (sizes config).1; have := Random.positive config; omega)

def getHashed := Constructed.first (hashed config) config.handler.store config.sampler.wordFits (input config).representation.fits
def getForgery := (getHashed config).then
  (Constructed.first (ForgeryHash.forgery config) config.handler.sampler.tape.scalar config.sampler.wordFits (hashed config).representation.fits)
def getChallenge := (getHashed config).then
  (Constructed.second (ForgeryHash.forgery config) config.handler.sampler.tape.scalar config.sampler.wordFits (hashed config).representation.fits)
def getMessage := (getForgery config).then
  (Constructed.first config.message config.handler.core.reply config.sampler.wordFits (ForgeryHash.forgery config).representation.fits)
def getReply := (getForgery config).then
  (Constructed.second config.message config.handler.core.reply config.sampler.wordFits (ForgeryHash.forgery config).representation.fits)
def getCommitment := (getReply config).then
  (Constructed.first config.point config.handler.sampler.tape.scalar config.sampler.wordFits config.handler.core.reply.representation.fits)
def getResponse := (getReply config).then
  (Constructed.second config.point config.handler.sampler.tape.scalar config.sampler.wordFits config.handler.core.reply.representation.fits)
def getStore := Constructed.second (hashed config) config.handler.store config.sampler.wordFits (input config).representation.fits
def getCaches := (getStore config).then
  (Constructed.first config.handler.caches (Read.tapes config.handler.sampler.tape) config.sampler.wordFits config.handler.store.representation.fits)
def getPoints := (getCaches config).then
  (Constructed.first config.handler.core.arithmetic.points (tables config) config.sampler.wordFits config.handler.caches.representation.fits)
def getGenerator := (getPoints config).then
  (Constructed.first config.point config.point config.sampler.wordFits config.handler.core.arithmetic.points.representation.fits)
def getPublicKey := (getPoints config).then
  (Constructed.second config.point config.point config.sampler.wordFits config.handler.core.arithmetic.points.representation.fits)
def getTables := (getCaches config).then
  (Constructed.second config.handler.core.arithmetic.points (tables config) config.sampler.wordFits config.handler.caches.representation.fits)
def getLive := (getTables config).then
  (Constructed.second config.handler.core.table config.handler.core.table config.sampler.wordFits (tables config).representation.fits)

def pair {A B : Type} {firstLayout : Layout w A} {secondLayout : Layout w B} {f : Input M F G → A} {g : Input M F G → B}
    (first : Constructed (input config) firstLayout f) (second : Constructed (input config) secondLayout g)
    (firstSmall : first.buffers ≤ 8) (secondSmall : second.buffers ≤ 8)
    (leftSize : firstLayout.representation.encoding.words ≤ 8 * config.handler.width)
    (rightSize : secondLayout.representation.encoding.words ≤ 8 * config.handler.width) :=
  first.pair second config.sampler.wordFits
    (by have := config.sampler.wordFits; omega) (by have := config.sampler.wordFits; omega)
    (duplicate config) (config.handler.fits_of_le (by have := (sizes config).1; omega))
    (config.handler.fits_of_le (by omega))
def key := pair config (getMessage config) (getCommitment config) (by change 2 ≤ 8; decide) (by change 2 ≤ 8; decide)
  (by have := FinalHash.key_le config; change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at this; omega)
  (by have := FinalHash.key_le config; change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at this; omega)
def liveInput : Constructed (input config) (chronology config).input (fun value => ((value.1.1.1, value.1.1.2.1), value.2.1.2.2)) :=
  pair config (key config) (getLive config) (by change 3 ≤ 8; decide) (by change 2 ≤ 8; decide)
    (by have := FinalHash.key_le config; exact this.trans (by omega))
    (config.handler.table_le.trans (by omega))

def scalars : Constructed (input config) config.handler.core.arithmetic.scalars (fun value => (value.1.1.2.2, value.1.2)) :=
  pair config (getResponse config) (getChallenge config) (by change 2 ≤ 8; decide) (by change 2 ≤ 8; decide)
    (by change 1 ≤ _; have := Random.positive config; omega) (by change 1 ≤ _; have := Random.positive config; omega)
def points : Constructed (input config) config.handler.core.arithmetic.points (fun value => (value.2.1.1.2, value.2.1.1.1)) :=
  pair config (getPublicKey config) (getGenerator config) (by change 2 ≤ 8; decide) (by change 2 ≤ 8; decide)
    (by have := FinalHash.key_le config; change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at this; omega)
    (by have := FinalHash.key_le config; change config.message.representation.encoding.words + config.point.representation.encoding.words ≤ _ at this; omega)
variable [Zero F]
def zero : Constructed (input config) config.handler.sampler.tape.scalar (fun _ => 0) :=
  Constructed.constant (input config) config.handler.sampler.tape.scalar ⟨0, trivial⟩ config.sampler.wordFits
def publicInput : Constructed (input config) config.handler.core.arithmetic.config (fun value => (0, value.2.1.1.2, value.2.1.1.1)) :=
  pair config (zero config) (points config) (by change 2 ≤ 8; decide) (by change 3 ≤ 8; decide)
    (by change 1 ≤ _; have := Random.positive config; omega)
    (by have := (sizes config).2.1; change (1 + 1) + (1 + config.handler.core.arithmetic.points.representation.encoding.words) ≤ _ at this; omega)
def verifyInput : Constructed (input config) config.handler.core.arithmetic.badInput
    (fun value => ((value.1.1.2.2, value.1.2), 0, value.2.1.1.2, value.2.1.1.1)) :=
  pair config (scalars config) (publicInput config) (by change 3 ≤ 8; decide) (by change 4 ≤ 8; decide)
    (by change 1 + 1 ≤ _; have := Random.positive config; omega)
    (by have := (sizes config).2.1; change (1 + 1) + config.handler.core.arithmetic.config.representation.encoding.words ≤ _ at this; omega)

def represented (value : ForgeryHash.Output config) : (input config).Value :=
  ⟨((value.1.1.val, value.1.2.val), value.2.val), ⟨value.1.1.property, value.1.2.property⟩, value.2.property⟩
omit [Zero F] in
theorem represented_bytes (value : ForgeryHash.Output config) :
    (input config).representation.encoding.encode (represented config value) = (ForgeryHash.output config).encoding.encode value := rfl

end Signatures.Runtime.CaliperBackend.SchnorrROM.Selection

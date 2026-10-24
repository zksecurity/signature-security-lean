import Proofs.Runtime.Caliper.SchnorrROMSigningCore
import Proofs.Runtime.Caliper.SchnorrROMPrivatePairBounds

/-! The complete signing frame contains separate managed and LIVE tables and
both replay tapes. Its scalar encoding is the private sampler's encoding.
The managed table reserves one insertion slot; tape reservations are the
reachable-domain invariant of the interactive sampler. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
open Caliper BoundedSource SchnorrROMTape

structure Layouts (w : Nat) (M F G C : Type) where
  sampler : PrivateSampler.Layouts w F C
  message : Layout w M
  point : Layout w G
  capacityPred : Nat
  countFits : capacityPred + 1 < 2 ^ w
  storageFits : 128 * (1 + (capacityPred + 1) * (message.representation.encoding.words +
    point.representation.encoding.words + sampler.tape.scalar.representation.encoding.words) +
    3 * sampler.tape.scalar.representation.encoding.words + 3 * point.representation.encoding.words +
    message.representation.encoding.words + (Read.tapes sampler.tape).representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {M F G C : Type} (layout : Layouts w M F G C)

def width := 1 + (layout.capacityPred + 1) * (layout.message.representation.encoding.words +
  layout.point.representation.encoding.words + layout.sampler.tape.scalar.representation.encoding.words) +
  3 * layout.sampler.tape.scalar.representation.encoding.words + 3 * layout.point.representation.encoding.words +
  layout.message.representation.encoding.words + (Read.tapes layout.sampler.tape).representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 128 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def core : Signing.Layouts w M F G where
  message := layout.message
  scalar := layout.sampler.tape.scalar
  point := layout.point
  capacityPred := layout.capacityPred
  wordFits := layout.sampler.tape.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by unfold width; omega)

theorem width_eq : layout.width = layout.core.width + (Read.tapes layout.sampler.tape).representation.encoding.words := rfl
theorem table_le : layout.core.table.representation.encoding.words ≤ layout.width := by
  rw [Signing.Layouts.table_words, width_eq]
  unfold Signing.Layouts.width
  omega
theorem base_le : layout.core.base.representation.encoding.words ≤ layout.width := by
  have := layout.core.input_le
  rw [width_eq]
  change _ + (_ + (_ + layout.core.table.representation.encoding.words)) ≤ _
  rw [Signing.Layouts.input_words] at this
  omega

def caches := layout.core.arithmetic.points.prod
  (layout.core.table.prod layout.core.table (layout.fits_of_le (by have := layout.table_le; omega)))
  (layout.fits_of_le (by
    change (_ + _) + (_ + _) ≤ _
    have := layout.table_le
    have := layout.core.output_le
    change (_ + _) + ((_ + _) + _) ≤ _ at this
    rw [width_eq]
    omega))
def store := layout.caches.prod (Read.tapes layout.sampler.tape) (layout.fits_of_le (by
  change ((_ + _) + (_ + _)) + _ ≤ _
  have := layout.table_le
  have := layout.core.output_le
  change (_ + _) + ((_ + _) + _) ≤ _ at this
  rw [width_eq] at *
  omega))
def rawInput := layout.message.prod layout.store (layout.fits_of_le (by
  change _ + (((_ + _) + (_ + _)) + _) ≤ _
  have := layout.table_le
  have := layout.core.input_le
  rw [Signing.Layouts.input_words, width_eq] at *
  dsimp only [core, Signing.Layouts.arithmetic] at *
  omega))
def ready (value : M × Schnorr.ListROM.Shared.Store F G M) : Prop :=
  value.2.1.2.1.length ≤ layout.capacityPred
instance (value : M × Schnorr.ListROM.Shared.Store F G M) : Decidable (layout.ready value) :=
  inferInstanceAs (Decidable (_ ≤ _))
def input := layout.rawInput.restrict layout.ready

def baseReady (value : G × G × M × Table M F G) : Prop := value.2.2.2.length ≤ layout.capacityPred
instance (value : G × G × M × Table M F G) : Decidable (layout.baseReady value) :=
  inferInstanceAs (Decidable (_ ≤ _))
def base := layout.core.base.restrict layout.baseReady
def context := layout.base.prod layout.core.table
  (layout.fits_of_le (by
    change layout.core.base.representation.encoding.words + _ ≤ _
    have := layout.base_le; have := layout.table_le; omega))
theorem context_le : layout.context.representation.encoding.words ≤ 2 * layout.width := by
  change layout.core.base.representation.encoding.words + _ ≤ _
  have := layout.base_le; have := layout.table_le; omega

def prepared := (Read.tapes layout.sampler.tape).representation.prod layout.context.representation
  (layout.fits_of_le (by have := layout.context_le; rw [width_eq] at *; omega))
def sampled := (PrivateSampler.Pair.output layout.sampler).representation.prod layout.context.representation
  (layout.fits_of_le (by
    have := layout.context_le
    change (_ + (_ + _)) + _ ≤ _
    rw [width_eq] at *
    unfold Signing.Layouts.width at *
    dsimp only [core] at *
    omega))
def saved := layout.core.table.prod (Read.tapes layout.sampler.tape)
  (layout.fits_of_le (by have := layout.table_le; rw [width_eq] at *; omega))
def work := layout.core.input.representation.prod layout.saved.representation
  (layout.fits_of_le (by
    have := layout.core.input_le; have := layout.table_le
    change _ + (_ + _) ≤ _
    rw [width_eq] at *
    omega))
def finished := layout.core.output.representation.prod layout.saved.representation
  (layout.fits_of_le (by
    have := layout.core.output_le; have := layout.table_le
    change _ + (_ + _) ≤ _
    rw [width_eq] at *
    omega))
def output := layout.core.reply.prod layout.store
  (layout.fits_of_le (by
    have outputBound := layout.core.output_le; have := layout.table_le
    change (_ + _) + (((_ + _) + (_ + _)) + _) ≤ _
    change (_ + _) + ((_ + _) + _) ≤ _ at outputBound
    rw [width_eq] at *
    omega))

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler

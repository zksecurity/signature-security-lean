import Signatures.Runtime.Caliper.SchnorrROMPrivateSamplerBounds
import Signatures.Runtime.Caliper.EncodedConstant

/-! Executed output conversion for the adaptive private sampler. The returned
tag and padding are removed by charged copies. A cutoff constructs zero and
preserves both tapes; the sampler's termination proof excludes that branch. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Finish
open Caliper BoundedSource
variable {w : Nat} {F C : Type} (layout : Layouts w F C) (zero : layout.tape.scalar.Value)

abbrev Packet := CallerControl.Packet C (Request layout) layout.tape.scalar.Value (Store layout)
def value (packet : Packet layout) : layout.tape.scalar.Value × Store layout :=
  (packet.1.elim id (fun _ => zero), packet.2)

def constant : Realizer .unit (CallerStep.pending (step layout)) layout.tape.scalar.representation (fun _ => zero) :=
  (Implementation.constant (Layout.all (CallerStep.pending (step layout))) layout.tape.scalar zero layout.tape.wordFits).program.viewInput
    (CallerStep.pending (step layout)) (fun pending => ⟨pending, trivial⟩) (fun _ => rfl)

theorem constant_buffers : (constant layout zero).code.memBound ≤ 2 :=
  Implementation.constant_buffers (Layout.all (CallerStep.pending (step layout))) layout.tape.scalar zero layout.tape.wordFits
theorem constant_nameFits : (constant layout zero).savedBuffer < 2 ^ w := by
  have bound := constant_buffers layout zero
  have := layout.tape.wordFits
  dsimp only [Realizer.savedBuffer]
  omega

def fallback : Realizer .unit (CallerStep.frame (step layout)) (CallerControl.result (step layout))
    (fun packet => (zero, packet.2)) :=
  (constant layout zero).retain (by decide) (Read.tapes layout.tape).representation layout.tape.wordFits
    (constant_nameFits layout zero) (CallerStep.frame (step layout)).fits (CallerControl.result (step layout)).fits

def program : Realizer .unit (CallerStep.output (step layout)) (CallerControl.result (step layout)) (value layout zero) :=
  ((CallerControl.distribute (step layout)).then
    (branchRealizer .unit (by decide) (CallerControl.result (step layout)) (CallerStep.frame (step layout))
      (CallerControl.result (step layout))
      (Realizer.identity (width_pos layout.tape.wordFits) (CallerControl.result (step layout)))
      (fallback layout zero) layout.tape.wordFits (CallerControl.choice (step layout)).fits)).viewOutput
        (CallerControl.result (step layout)) (value layout zero) (by
          intro packet
          rcases packet with ⟨result | pending, saved⟩ <;> rfl)

theorem fallback_time (packet) : (fallback layout zero).time packet ≤ 36 * CallerStep.width (step layout) := by
  have copied := (constant layout zero).retain_time_unit_le (Read.tapes layout.tape).representation layout.tape.wordFits
    (constant_nameFits layout zero) (CallerStep.frame (step layout)).fits (CallerControl.result (step layout)).fits packet
  have primitive := (Implementation.constant_bounded (Layout.all (CallerStep.pending (step layout))) layout.tape.scalar
    zero layout.tape.wordFits).time_le ⟨packet.1, trivial⟩
  have sizes := CallerControl.sizes (step layout)
  change (constant layout zero).time packet.1 ≤ 8 * (step layout).result.encoding.words at primitive
  change _ ≤ _ + 8 * (CallerStep.pending (step layout)).encoding.words + 8 * (step layout).result.encoding.words +
    12 * (step layout).store.encoding.words at copied
  exact copied.trans (by omega)

theorem fallback_words : descriptionWords (fallback layout zero).code ≤ 117 * CallerStep.width (step layout) + 53 := by
  have copied := (constant layout zero).retain_descriptionWords_le (by decide) (Read.tapes layout.tape).representation layout.tape.wordFits
    (constant_nameFits layout zero) (CallerStep.frame (step layout)).fits (CallerControl.result (step layout)).fits
  have primitive := (Implementation.constant_bounded (Layout.all (CallerStep.pending (step layout))) layout.tape.scalar
    zero layout.tape.wordFits).code_le
  have sizes := CallerControl.sizes (step layout)
  change descriptionWords (constant layout zero).code ≤ 26 * (step layout).result.encoding.words + 14 at primitive
  change _ ≤ _ + 26 * (CallerStep.pending (step layout)).encoding.words + 26 * (step layout).result.encoding.words +
    39 * (step layout).store.encoding.words + 39 at copied
  exact copied.trans (by omega)

theorem time (packet : Packet layout) : (program layout zero).time packet ≤ 68 * CallerStep.width (step layout) + 4 := by
  have distributed := CallerControl.distribute_time (step layout) packet
  have sizes := CallerControl.sizes (step layout)
  rcases packet with ⟨result | pending, saved⟩
  · change _ + (1 + (1 + ((selectSlice (w := w) 1 (CallerControl.result (step layout)).encoding.words).staticTime .unit + 0))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    omega
  · have stopped := fallback_time layout zero (pending, saved)
    change _ + (1 + (1 + ((selectSlice (w := w) 1 (CallerStep.frame (step layout)).encoding.words).staticTime .unit + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, Caliper.CostModel.unit]
    omega

theorem words : descriptionWords (program layout zero).code ≤ 325 * CallerStep.width (step layout) + 187 := by
  have distributed := CallerControl.distribute_words (step layout)
  have stopped := fallback_words layout zero
  have sizes := CallerControl.sizes (step layout)
  change descriptionWords (_ ;; Dispatch.code .skip _ (CallerControl.result (step layout)).encoding.words
    (CallerStep.frame (step layout)).encoding.words) ≤ _
  rw [descriptionWords_seq, Dispatch.code_descriptionWords]
  change _ + (1 + _ + 26 * _ + 26 * _ + 37) + 1 ≤ _
  omega

theorem names : NamesAccounted (program layout zero).code 3 :=
  (CallerControl.distribute_names (step layout)).seq (Dispatch.names (Signatures.Runtime.CaliperBackend.skip_names 3)
    (Retain.names (Implementation.constant_names (Layout.all (CallerStep.pending (step layout)))
      layout.tape.scalar zero layout.tape.wordFits 3) _ _ _) _ _)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Finish

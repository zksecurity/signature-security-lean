import Proofs.Runtime.Caliper.AttachRowsBounds

/-! Chronological coefficient rows from reverse-stored transcript tokens. Both
transcript reversal and positional attachment execute their constructed Caliper
programs. The default is a represented constant (zero in the AGM application),
whose encoding is included in the program and executed copies. -/

namespace Signatures.Runtime.CaliperBackend.TokenRows
open Caliper BoundedSource
variable {w : Nat} {K V : Type} (layout : AttachRows.Layouts w K V)

def reversal : ListReverse.Layouts w K where
  entry := layout.key
  capacity := layout.capacity
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by dsimp only [AttachRows.Layouts.width]; nlinarith)
def input : Layout w (List K × List V) := layout.keys.prod layout.values
  (layout.fits_of_le (by have := layout.base_sizes; omega))
theorem input_size : (input layout).representation.encoding.words ≤ 2 * layout.width := by
  change layout.keys.representation.encoding.words + layout.values.representation.encoding.words ≤ _
  have := layout.base_sizes; omega
def keys : Implementation .unit (input layout) layout.keys (fun value => value.1.reverse) :=
  (Implementation.first (by decide) layout.keys layout.values layout.wordFits (input layout).representation.fits).then
    (ListReverse.implementation (reversal layout))
def values : Implementation .unit (input layout) layout.values Prod.snd :=
  Implementation.second (by decide) layout.keys layout.values layout.wordFits (input layout).representation.fits
theorem keys_buffers : (keys layout).program.code.memBound ≤ 3 :=
  max_le ((Implementation.first_buffers _ _ _ _ _).trans (by decide)) (ListReverse.buffers _)
theorem values_buffers : (values layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _

variable (default : layout.value.Value)
def constant : Implementation .unit (input layout) layout.value (fun _ => default.val) :=
  Implementation.constant (input layout) layout.value default layout.wordFits
theorem constant_buffers : (constant layout default).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
def environment : Implementation .unit (input layout) layout.env (fun value => (default.val, value.2)) :=
  (constant layout default).pair (values layout) (by decide) layout.wordFits
    (layout.nameFits _ (constant_buffers layout default) (by decide)) (layout.nameFits _ (values_buffers layout) (by decide))
    (layout.fits_of_le (by have := input_size layout; omega))
    (layout.fits_of_le (by have := input_size layout; have := layout.base_sizes; omega))
    layout.env.representation.fits
theorem environment_buffers : (environment layout default).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (constant_buffers layout default) (values_buffers layout)
def prepare : Implementation .unit (input layout) layout.input (fun value => (value.1.reverse, default.val, value.2)) :=
  (keys layout).pair (environment layout default) (by decide) layout.wordFits
    (layout.nameFits _ (keys_buffers layout) (by decide)) (layout.nameFits _ (environment_buffers layout default) (by decide))
    (layout.fits_of_le (by have := input_size layout; omega))
    (layout.fits_of_le (by have := input_size layout; have := layout.base_sizes; omega)) layout.input.representation.fits
def implementation : Implementation .unit (input layout) layout.output
    (fun value => value.1.reverse.mapIdx (fun n key => (key, (value.2[n]?).getD default.val))) :=
  (prepare layout default).then (AttachRows.implementation layout)
theorem prepare_buffers : (prepare layout default).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 3) (secondBuffers := 3) _ _ _ _ _ _ _ _
    (keys_buffers layout) (environment_buffers layout default)
theorem buffers : (implementation layout default).program.code.memBound ≤ 10 :=
  max_le ((prepare_buffers layout default).trans (by decide)) (AttachRows.buffers layout)

end Signatures.Runtime.CaliperBackend.TokenRows

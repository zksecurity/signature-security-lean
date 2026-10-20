import Signatures.Runtime.Caliper.SchnorrAGMHistoriesLayout

/-! Signing history projections use the existing charged product copies.
The free-slot invariant restricts the original input and remains available
when constructing the two append arguments. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def selectSaved : Implementation .unit layout.input layout.signing.saved Prod.snd :=
  (Implementation.second (by decide) layout.scheme.cache.lookup.input layout.signing.saved layout.scheme.wordFits _).restrictInput layout.room
def selectHistory : Implementation .unit layout.input layout.signing.history (fun input => input.2.2) :=
  (selectSaved layout).then (Implementation.second (by decide) layout.signing.computed layout.signing.history layout.scheme.wordFits _)
def selectTail : Implementation .unit layout.input layout.signing.historyTail (fun input => input.2.2.2) :=
  (selectHistory layout).then (Implementation.second (by decide) layout.scheme.affine layout.signing.historyTail layout.scheme.wordFits _)
def selectMetadata : Implementation .unit layout.input layout.scheme.metadata (fun input => input.2.2.2.2) :=
  (selectTail layout).then (Implementation.second (by decide) layout.scheme.message layout.scheme.metadata layout.scheme.wordFits _)
def selectSignedFlags : Implementation .unit layout.input layout.scheme.signedFlags (fun input => input.2.2.2.2.2) :=
  (selectMetadata layout).then (Implementation.second (by decide) layout.scheme.basis layout.scheme.signedFlags layout.scheme.wordFits _)

def selectCache : Implementation .unit layout.input layout.scheme.cache.lookup.input Prod.fst :=
  (Implementation.first (by decide) layout.scheme.cache.lookup.input layout.signing.saved layout.scheme.wordFits _).restrictInput layout.room
def selectReply : Implementation .unit layout.input layout.signing.computed (fun input => input.2.1) :=
  (selectSaved layout).then (Implementation.first (by decide) layout.signing.computed layout.signing.history layout.scheme.wordFits _)
def selectAffine : Implementation .unit layout.input layout.scheme.affine (fun input => input.2.2.1) :=
  (selectHistory layout).then (Implementation.first (by decide) layout.scheme.affine layout.signing.historyTail layout.scheme.wordFits _)
def selectMessage : Implementation .unit layout.input layout.scheme.message (fun input => input.2.2.2.1) :=
  (selectTail layout).then (Implementation.first (by decide) layout.scheme.message layout.scheme.metadata layout.scheme.wordFits _)
def selectBasis : Implementation .unit layout.input layout.scheme.basis (fun input => input.2.2.2.2.1) :=
  (selectMetadata layout).then (Implementation.first (by decide) layout.scheme.basis layout.scheme.signedFlags layout.scheme.wordFits _)
def selectSigned : Implementation .unit layout.input layout.scheme.signed (fun input => input.2.2.2.2.2.1) :=
  (selectSignedFlags layout).then (Implementation.first (by decide) layout.scheme.signed layout.scheme.flags layout.scheme.wordFits _)
def selectFlags : Implementation .unit layout.input layout.scheme.flags (fun input => input.2.2.2.2.2.2) :=
  (selectSignedFlags layout).then (Implementation.second (by decide) layout.scheme.signed layout.scheme.flags layout.scheme.wordFits _)

theorem selection_buffers : (selectCache layout).program.code.memBound ≤ 2 ∧ (selectReply layout).program.code.memBound ≤ 2 ∧
    (selectAffine layout).program.code.memBound ≤ 2 ∧ (selectMessage layout).program.code.memBound ≤ 2 ∧
    (selectBasis layout).program.code.memBound ≤ 2 ∧ (selectSigned layout).program.code.memBound ≤ 2 ∧
    (selectFlags layout).program.code.memBound ≤ 2 := by
  have saved : (selectSaved layout).program.code.memBound ≤ 2 := Implementation.second_buffers (cost := .unit) (by decide) layout.scheme.cache.lookup.input layout.signing.saved layout.scheme.wordFits layout.signing.work.representation.fits
  have history : (selectHistory layout).program.code.memBound ≤ 2 := max_le saved (Implementation.second_buffers (cost := .unit) (by decide) layout.signing.computed layout.signing.history layout.scheme.wordFits layout.signing.saved.representation.fits)
  have tail : (selectTail layout).program.code.memBound ≤ 2 := max_le history (Implementation.second_buffers (cost := .unit) (by decide) layout.scheme.affine layout.signing.historyTail layout.scheme.wordFits layout.signing.history.representation.fits)
  have metadata : (selectMetadata layout).program.code.memBound ≤ 2 := max_le tail (Implementation.second_buffers (cost := .unit) (by decide) layout.scheme.message layout.scheme.metadata layout.scheme.wordFits layout.signing.historyTail.representation.fits)
  have signedFlags : (selectSignedFlags layout).program.code.memBound ≤ 2 := max_le metadata (Implementation.second_buffers (cost := .unit) (by decide) layout.scheme.basis layout.scheme.signedFlags layout.scheme.wordFits layout.scheme.metadata.representation.fits)
  exact ⟨Implementation.first_buffers (cost := .unit) (by decide) layout.scheme.cache.lookup.input layout.signing.saved layout.scheme.wordFits layout.signing.work.representation.fits, max_le saved (Implementation.first_buffers (cost := .unit) (by decide) layout.signing.computed layout.signing.history layout.scheme.wordFits layout.signing.saved.representation.fits),
    max_le history (Implementation.first_buffers (cost := .unit) (by decide) layout.scheme.affine layout.signing.historyTail layout.scheme.wordFits layout.signing.history.representation.fits), max_le tail (Implementation.first_buffers (cost := .unit) (by decide) layout.scheme.message layout.scheme.metadata layout.scheme.wordFits layout.signing.historyTail.representation.fits),
    max_le metadata (Implementation.first_buffers (cost := .unit) (by decide) layout.scheme.basis layout.scheme.signedFlags layout.scheme.wordFits layout.scheme.metadata.representation.fits), max_le signedFlags (Implementation.first_buffers (cost := .unit) (by decide) layout.scheme.signed layout.scheme.flags layout.scheme.wordFits layout.scheme.signedFlags.representation.fits),
    max_le signedFlags (Implementation.second_buffers (cost := .unit) (by decide) layout.scheme.signed layout.scheme.flags layout.scheme.wordFits layout.scheme.signedFlags.representation.fits)⟩

theorem selection_names (slots : Nat) : NamesAccounted (selectCache layout).program.code slots ∧ NamesAccounted (selectReply layout).program.code slots ∧
    NamesAccounted (selectAffine layout).program.code slots ∧ NamesAccounted (selectMessage layout).program.code slots ∧
    NamesAccounted (selectBasis layout).program.code slots ∧ NamesAccounted (selectSigned layout).program.code slots ∧
    NamesAccounted (selectFlags layout).program.code slots := by
  have saved : NamesAccounted (selectSaved layout).program.code slots := Implementation.second_names layout.scheme.cache.lookup.input layout.signing.saved layout.scheme.wordFits layout.signing.work.representation.fits slots
  have history : NamesAccounted (selectHistory layout).program.code slots := saved.seq (Implementation.second_names layout.signing.computed layout.signing.history layout.scheme.wordFits layout.signing.saved.representation.fits slots)
  have tail : NamesAccounted (selectTail layout).program.code slots := history.seq (Implementation.second_names layout.scheme.affine layout.signing.historyTail layout.scheme.wordFits layout.signing.history.representation.fits slots)
  have metadata : NamesAccounted (selectMetadata layout).program.code slots := tail.seq (Implementation.second_names layout.scheme.message layout.scheme.metadata layout.scheme.wordFits layout.signing.historyTail.representation.fits slots)
  have signedFlags : NamesAccounted (selectSignedFlags layout).program.code slots := metadata.seq (Implementation.second_names layout.scheme.basis layout.scheme.signedFlags layout.scheme.wordFits layout.scheme.metadata.representation.fits slots)
  exact ⟨Implementation.first_names layout.scheme.cache.lookup.input layout.signing.saved layout.scheme.wordFits layout.signing.work.representation.fits slots, saved.seq (Implementation.first_names layout.signing.computed layout.signing.history layout.scheme.wordFits layout.signing.saved.representation.fits slots),
    history.seq (Implementation.first_names layout.scheme.affine layout.signing.historyTail layout.scheme.wordFits layout.signing.history.representation.fits slots), tail.seq (Implementation.first_names layout.scheme.message layout.scheme.metadata layout.scheme.wordFits layout.signing.historyTail.representation.fits slots),
    metadata.seq (Implementation.first_names layout.scheme.basis layout.scheme.signedFlags layout.scheme.wordFits layout.scheme.metadata.representation.fits slots), signedFlags.seq (Implementation.first_names layout.scheme.signed layout.scheme.flags layout.scheme.wordFits layout.scheme.signedFlags.representation.fits slots),
    signedFlags.seq (Implementation.second_names layout.scheme.signed layout.scheme.flags layout.scheme.wordFits layout.scheme.signedFlags.representation.fits slots)⟩

private theorem first_bound {A B : Type} (head : Layout w A) (tail : Layout w B)
    (fits : head.representation.encoding.words + tail.representation.encoding.words < 2 ^ w)
    (bound : head.representation.encoding.words ≤ 3 * layout.width) :
    (Implementation.first (cost := .unit) (by decide) head tail layout.scheme.wordFits fits).BoundedBy (24 * layout.width) (78 * layout.width + 14) :=
  (Implementation.first_boundedBy head tail layout.scheme.wordFits fits).mono (by omega) (by omega)
private theorem second_bound {A B : Type} (head : Layout w A) (tail : Layout w B)
    (fits : head.representation.encoding.words + tail.representation.encoding.words < 2 ^ w)
    (bound : tail.representation.encoding.words ≤ 3 * layout.width) :
    (Implementation.second (cost := .unit) (by decide) head tail layout.scheme.wordFits fits).BoundedBy (24 * layout.width) (78 * layout.width + 14) :=
  (Implementation.second_boundedBy head tail layout.scheme.wordFits fits).mono (by omega) (by omega)

theorem selection_bounded : (selectCache layout).BoundedBy (144 * layout.width) (468 * layout.width + 90) ∧
    (selectReply layout).BoundedBy (144 * layout.width) (468 * layout.width + 90) ∧
    (selectAffine layout).BoundedBy (144 * layout.width) (468 * layout.width + 90) ∧
    (selectMessage layout).BoundedBy (144 * layout.width) (468 * layout.width + 90) ∧
    (selectBasis layout).BoundedBy (144 * layout.width) (468 * layout.width + 90) ∧
    (selectSigned layout).BoundedBy (144 * layout.width) (468 * layout.width + 90) ∧
    (selectFlags layout).BoundedBy (144 * layout.width) (468 * layout.width + 90) := by
  rcases layout.field_sizes with ⟨cacheSize, replySize, savedSize, historySize, tailSize, affineSize, messageSize,
    metadataSize, basisSize, signedFlagsSize, signedSize, flagsSize, _⟩
  have saved := (second_bound layout layout.scheme.cache.lookup.input layout.signing.saved layout.signing.work.representation.fits savedSize).restrictInput layout.room
  have history := saved.then (second_bound layout layout.signing.computed layout.signing.history layout.signing.saved.representation.fits historySize)
  have tail := history.then (second_bound layout layout.scheme.affine layout.signing.historyTail layout.signing.history.representation.fits tailSize)
  have metadata := tail.then (second_bound layout layout.scheme.message layout.scheme.metadata layout.signing.historyTail.representation.fits metadataSize)
  have signedFlags := metadata.then (second_bound layout layout.scheme.basis layout.scheme.signedFlags layout.scheme.metadata.representation.fits signedFlagsSize)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((first_bound layout layout.scheme.cache.lookup.input layout.signing.saved layout.signing.work.representation.fits cacheSize).restrictInput layout.room).mono (by omega) (by omega)
  · exact (saved.then (first_bound layout layout.signing.computed layout.signing.history layout.signing.saved.representation.fits replySize)).mono (by omega) (by omega)
  · exact (history.then (first_bound layout layout.scheme.affine layout.signing.historyTail layout.signing.history.representation.fits affineSize)).mono (by omega) (by omega)
  · exact (tail.then (first_bound layout layout.scheme.message layout.scheme.metadata layout.signing.historyTail.representation.fits messageSize)).mono (by omega) (by omega)
  · exact (metadata.then (first_bound layout layout.scheme.basis layout.scheme.signedFlags layout.scheme.metadata.representation.fits basisSize)).mono (by omega) (by omega)
  · exact (signedFlags.then (first_bound layout layout.scheme.signed layout.scheme.flags layout.scheme.signedFlags.representation.fits signedSize)).mono (by omega) (by omega)
  · exact (signedFlags.then (second_bound layout layout.scheme.signed layout.scheme.flags layout.scheme.signedFlags.representation.fits flagsSize)).mono (by omega) (by omega)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories

import Proofs.Runtime.Caliper.SchnorrAGMHistoriesLayout
import Proofs.Runtime.Caliper.SchnorrAGMCache
import Proofs.Runtime.Caliper.CacheBounds

/-! Deterministic signing cache programming and final result assembly. The
bounded cache program compares encoded keys and preserves existing entries.
The signature and metadata remain physically resident during that execution;
the final signature/state pair is rebuilt by charged reads and writes. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Programming
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Histories.Layouts w M F G qH qS)

def input : Layout w (Histories.Output M F G) :=
  layout.output.restrict (fun value => layout.scheme.cache.admissible value.1)

theorem sizes : layout.scheme.cache.input.representation.encoding.words + layout.saved.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.cache.lookup.table.representation.encoding.words + layout.signing.computed.representation.encoding.words +
      layout.scheme.metadata.representation.encoding.words ≤ 3 * layout.width := by
  have bound := layout.sizes.2.2
  change layout.scheme.cache.lookup.input.representation.encoding.words +
    (layout.signing.computed.representation.encoding.words + layout.scheme.metadata.representation.encoding.words) ≤ _ at bound
  change _ + (_ + _) ≤ _ ∧ _ + _ + _ ≤ _
  change (layout.scheme.cache.key.representation.encoding.words + (layout.scheme.cache.value.representation.encoding.words +
    (layout.scheme.cache.lookup.table.representation.encoding.words + 0))) + (_ + _) ≤ _ at bound
  change (layout.scheme.cache.key.representation.encoding.words + (layout.scheme.cache.value.representation.encoding.words +
    (layout.scheme.cache.lookup.table.representation.encoding.words + 0))) + (_ + _) ≤ _ ∧ _
  omega

def frame : Representation w (layout.scheme.cache.lookup.table.Value × layout.saved.Value) :=
  layout.scheme.cache.lookup.table.representation.prod layout.saved.representation
    (layout.fits_of_le (by have := (sizes layout).2; change _ + (_ + _) ≤ _; omega))

def output : Layout w ((G × F) × EncodedState F G M) :=
  layout.signing.computed.prod layout.scheme.state
    (layout.fits_of_le (by have := (sizes layout).2; change _ + (_ + _) ≤ _; omega))

def cache := EncodedCache.implementation (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
  layout.scheme.cache (Cache.primitives F G M) Cache.comparison (Cache.comparison_correct F G M)

theorem cache_source (args : CacheLayout.Input (M × G) (EncodedEntry F)) :
    (cacheProgram (val := entryTy) Cache.comparison).denote (Cache.primitives F G M) args =
      CacheProgramming.value args.1 args.2.1 args.2.2.1 := by
  rcases args with ⟨key, entry, entries, ⟨⟩⟩
  rw [← Expr.run_value, cacheProgram_value _ _ (Cache.comparison_correct F G M), lookupValue_cacheMap]
  cases found : cacheMap entries key <;> simp [CacheProgramming.value, found]

def cacheImplementation : Implementation .unit layout.scheme.cache.input layout.scheme.cache.lookup.table
    (fun args => CacheProgramming.value args.1 args.2.1 args.2.2.1) :=
  (cache layout).castFunction (funext cache_source)

theorem cache_nameFits : (cacheImplementation layout).program.savedBuffer < 2 ^ w := by
  have bound := EncodedCache.buffers (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy) layout.scheme.cache (Cache.primitives F G M) Cache.comparison (Cache.comparison_correct F G M)
  have hw := layout.scheme.wordFits
  change max 2 (cache layout).program.code.memBound < _
  change (cache layout).program.code.memBound ≤ 8 at bound
  omega

def retained := (cacheImplementation layout).program.retain (by decide) layout.saved.representation
  layout.scheme.wordFits (cache_nameFits layout)
  (layout.fits_of_le (by have := (sizes layout).1; omega)) (frame layout).fits

def inputValue (value : (input layout).Value) : layout.scheme.cache.input.Value × layout.saved.Value :=
  (⟨value.val.1, value.property.1.1, value.property.2⟩, ⟨value.val.2, value.property.1.2⟩)

def finishValue (value : layout.scheme.cache.lookup.table.Value × layout.saved.Value) : (output layout).Value :=
  ⟨Signatures.Runtime.SchnorrAGM.Native.Signing.returnValue (value.1.val, value.2.val),
    value.2.property.1, value.1.property, value.2.property.2⟩

def finish : Realizer .unit (frame layout) (output layout).representation (finishValue layout) :=
  ((Reorder.realizer .unit (by decide) layout.scheme.cache.lookup.table.representation layout.signing.computed.representation
    layout.scheme.metadata.representation layout.scheme.wordFits
    (layout.fits_of_le (by have := (sizes layout).2; omega))).viewInput (frame layout)
      (fun value => (value.1, ⟨value.2.val.1, value.2.property.1⟩, ⟨value.2.val.2, value.2.property.2⟩)) (fun _ => rfl)).viewOutput
        (output layout).representation (finishValue layout) (fun _ => rfl)

def value (args : Histories.Output M F G) : (G × F) × EncodedState F G M :=
  Signatures.Runtime.SchnorrAGM.Native.Signing.returnValue
    (CacheProgramming.value args.1.1 args.1.2.1 args.1.2.2.1, args.2)

def implementation : Implementation .unit (input layout) (output layout) value where
  preserves args valid := ⟨valid.1.2.1,
    (cacheImplementation layout).preserves args.1 ⟨valid.1.1, valid.2⟩, valid.1.2.2⟩
  program := ((retained layout).viewInput (input layout).representation (inputValue layout) (fun _ => rfl)).then (finish layout)

theorem buffers : (implementation layout).program.code.memBound ≤ 9 := by
  have body := EncodedCache.buffers (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy) layout.scheme.cache (Cache.primitives F G M) Cache.comparison (Cache.comparison_correct F G M)
  have held := (Retain.code_names (cacheImplementation layout).program.code (cacheImplementation layout).program.savedBuffer
    layout.scheme.cache.input.representation.encoding.words layout.scheme.cache.lookup.table.representation.encoding.words
    layout.saved.representation.encoding.words (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  have finished := Reorder.buffers (w := w) layout.scheme.cache.lookup.table.representation.encoding.words
    layout.signing.computed.representation.encoding.words layout.scheme.metadata.representation.encoding.words
  change (cacheImplementation layout).program.code.memBound ≤ 8 at body
  change (retained layout).code.memBound ≤ max 2 (cacheImplementation layout).program.code.memBound + 1 at held
  change (finish layout).code.memBound ≤ 2 at finished
  change max (retained layout).code.memBound (finish layout).code.memBound ≤ _
  omega

theorem names : NamesAccounted (implementation layout).program.code 5 := by
  have body : NamesAccounted (cacheImplementation layout).program.code 5 :=
    EncodedCache.names (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
      layout.scheme.cache (Cache.primitives F G M) Cache.comparison (Cache.comparison_correct F G M)
  have held : NamesAccounted (retained layout).code 5 := Retain.names body _ _ _
  have finished : NamesAccounted (finish layout).code 5 := Reorder.names _ _ _ 5
  exact held.seq finished

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Programming

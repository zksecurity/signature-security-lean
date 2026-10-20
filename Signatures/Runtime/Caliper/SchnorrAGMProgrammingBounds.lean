import Signatures.Runtime.Caliper.SchnorrAGMProgramming
import Signatures.Runtime.Caliper.SchnorrAGMReachability

/-! Complete signing-programming bounds, including the retained histories and
signature, final result copies, stored code and all reached live memory. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Programming
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Histories.Layouts w M F G qH qS)

def timeBudget : Nat := EncodedCache.timeBudget (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
  layout.scheme.cache + 128 * layout.width
def codeBudget : Nat := EncodedCache.codeBudget (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
  layout.scheme.cache + 416 * layout.width + 64

theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have widths := sizes layout
  have body := EncodedCache.bounded (base := cryptoBase F G Unit M M) (key := cacheKeyTy) (val := entryTy)
    layout.scheme.cache (Cache.primitives F G M) Cache.comparison (Cache.comparison_correct F G M)
  have savedSize : layout.saved.representation.encoding.words = layout.signing.computed.representation.encoding.words +
      layout.scheme.metadata.representation.encoding.words := rfl
  constructor
  · intro args
    have held := (cacheImplementation layout).program.retain_time_unit_le layout.saved.representation
      layout.scheme.wordFits (cache_nameFits layout)
      (layout.fits_of_le (by have := widths.1; omega)) (frame layout).fits (inputValue layout args)
    have finished := Reorder.time_unit_le (w := w) layout.scheme.cache.lookup.table.representation.encoding.words
      layout.signing.computed.representation.encoding.words layout.scheme.metadata.representation.encoding.words
    have elapsed := body.time_le (inputValue layout args).1
    change (retained layout).time (inputValue layout args) ≤ _ at held
    change (cacheImplementation layout).program.time (inputValue layout args).1 ≤ _ at elapsed
    change (finish layout).time ((fun pair =>
      (⟨CacheProgramming.value pair.1.val.1 pair.1.val.2.1 pair.1.val.2.2.1,
        (cacheImplementation layout).preserves pair.1.val pair.1.property⟩, pair.2)) (inputValue layout args)) ≤ _ at finished
    change (retained layout).time (inputValue layout args) + (finish layout).time _ ≤ _
    unfold timeBudget
    dsimp only [Function.comp_apply] at *
    omega
  · have held := (cacheImplementation layout).program.retain_descriptionWords_le (by decide) layout.saved.representation
      layout.scheme.wordFits (cache_nameFits layout)
      (layout.fits_of_le (by have := widths.1; omega)) (frame layout).fits
    have finished := Reorder.descriptionWords_le (w := w) layout.scheme.cache.lookup.table.representation.encoding.words
      layout.signing.computed.representation.encoding.words layout.scheme.metadata.representation.encoding.words
    change descriptionWords (retained layout).code ≤ _ at held
    change descriptionWords (finish layout).code ≤ _ at finished
    change descriptionWords ((retained layout).code ;; (finish layout).code) ≤ _
    rw [descriptionWords_seq]
    have stored := body.code_le
    change descriptionWords (cacheImplementation layout).program.code ≤ _ at stored
    unfold codeBudget
    omega

theorem static_bound (registers buffers : Nat) : staticWords (implementation layout).program.code registers buffers ≤
    5 * codeBudget layout + 20 + registers + 3 * buffers := by
  have stored := (bounded layout).code_le
  have named := names layout
  have registerBound := named.registers
  have bufferBound := named.buffers
  unfold staticWords
  omega

theorem resources (tape : RandomTape w) (args : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time args) net peak ∧
      (output layout).representation.Holds ⟨value args.val, (implementation layout).preserves args.val args.property⟩ after ∧
      (implementation layout).program.time args ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
          5 * codeBudget layout + 20 + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, result, elapsed, _, _⟩ := (bounded layout).exec (by decide) tape args before holds
  refine ⟨after, net, peak, execution, result, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout registers buffers
  omega

theorem source [Field F] [AddCommGroup G] [Module F G] (args : Input M F G) :
    value (Signatures.Runtime.SchnorrAGM.Native.Signing.historiesValue (Arithmetic.value args)) =
      Signatures.Runtime.SchnorrAGM.Native.Signing.signedValue args := rfl

theorem reserved_admissible [Field F] [AddCommGroup G] [Module F G] {hashes signatures : Nat}
    {state : Signatures.Runtime.SchnorrAGM.State F G M} (room : layout.scheme.Reserved hashes (signatures + 1) state)
    (challenge response : F) (generator publicKey : G) (message : M) :
    layout.scheme.cache.admissible
      (Signatures.Runtime.SchnorrAGM.Native.Signing.historiesValue
        (Arithmetic.value ((challenge, response), generator, publicKey, message, encodeState state))).1 := by
  intro _
  change (state.cache.map _).length ≤ qH + qS
  rw [List.length_map]
  have reserved := room.2.1
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Programming

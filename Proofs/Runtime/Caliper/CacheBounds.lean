import Proofs.Runtime.Caliper.CacheCompilation

/-! Resource bounds for the complete original cache-programming expression.
Lookup contributes its proved quadratic budget; retaining the input and updating
the fixed-capacity table add only linear overhead in the stored widths. -/

namespace Signatures.Runtime.CaliperBackend.EncodedCache

open Caliper BoundedSource SourceExpression

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : CacheLayout w (key.Value base) (val.Value base))

def timeBudget : Nat := EncodedLookup.timeBudget (base := base) (key := key) (val := val) layout.lookup +
  160 * layout.lookup.width + 128 * layout.value.representation.encoding.words +
  40 * layout.lookup.table.representation.encoding.words + 176

def codeBudget : Nat := EncodedLookup.codeBudget (base := base) (key := key) (val := val) layout.lookup +
  546 * layout.lookup.width + 442 * layout.value.representation.encoding.words +
  130 * layout.lookup.table.representation.encoding.words + 1030

variable {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem paired_bounded : (paired layout P comparison correct).BoundedBy
    (EncodedLookup.timeBudget layout.lookup + 68 * layout.lookup.width + 36 * layout.lookup.result.representation.encoding.words)
    (EncodedLookup.codeBudget layout.lookup + 221 * layout.lookup.width + 117 * layout.lookup.result.representation.encoding.words + 125) := by
  have identityFits : (Implementation.identity (cost := .unit) layout.lookup.input (width_pos layout.wordFits)).program.savedBuffer < 2 ^ w := by
    change max 2 0 < 2 ^ w
    have hw := layout.wordFits
    omega
  have bound := Implementation.checkedPair_boundedBy (lookup layout P comparison correct)
    (Implementation.identity layout.lookup.input (width_pos layout.wordFits)) layout.wordFits
    layout.lookup.input_duplicateFits _ _ _ _ 0 1
    (EncodedLookup.implementation_bounded layout.lookup P comparison correct)
    (Implementation.identity_boundedBy layout.lookup.input (width_pos layout.wordFits))
    (paired layout P comparison correct)
    (by simp only [Implementation.checkedPair, dite_eq_left (lookup_nameFits layout P comparison correct), dite_eq_left identityFits]; rfl)
  apply bound.mono <;> simp only [LookupLayout.input_words] <;> omega

theorem frame_bounded : (frame layout P comparison correct).BoundedBy
    (EncodedLookup.timeBudget layout.lookup + 68 * layout.lookup.width + 36 * layout.lookup.result.representation.encoding.words)
    (EncodedLookup.codeBudget layout.lookup + 221 * layout.lookup.width + 117 * layout.lookup.result.representation.encoding.words + 125) :=
  ⟨fun value => (paired_bounded layout P comparison correct).time_le ⟨value.val, value.property.1⟩,
    (paired_bounded layout P comparison correct).code_le⟩

theorem bounded : (implementation layout P comparison correct).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have bound := ((frame_bounded layout P comparison correct).then (CacheFinish.bounded layout)).castFunction rfl
  apply bound.mono
  all_goals
    simp only [LookupLayout.result_words]
    dsimp only [timeBudget, codeBudget, CacheFinish.timeBudget, CacheFinish.codeBudget, CacheLayout.lookup]
    omega

theorem buffers : (implementation layout P comparison correct).program.code.memBound ≤ 8 := by
  have lookupBuffers := EncodedLookup.implementation_buffers layout.lookup P comparison correct
  have pairedBuffers := Pairing.buffers (lookup layout P comparison correct).program
    (Implementation.identity (cost := .unit) layout.lookup.input (width_pos layout.wordFits)).program
    (by decide) layout.wordFits (lookup_nameFits layout P comparison correct)
    (by change max 2 0 < 2 ^ w; have hw := layout.wordFits; omega) layout.lookup.input_duplicateFits
    (by apply layout.lookup.fits_of_le; simp [LookupLayout.width]; omega)
    (by apply layout.lookup.fits_of_le; simp [LookupLayout.width]; omega)
  change (paired layout P comparison correct).program.code.memBound ≤ max 2 (max (lookup layout P comparison correct).program.code.memBound 0) + 1 at pairedBuffers
  change (lookup layout P comparison correct).program.code.memBound ≤ 7 at lookupBuffers
  have finishBuffers := CacheFinish.buffers layout
  change max (paired layout P comparison correct).program.code.memBound (CacheFinish.implementation layout).program.code.memBound ≤ _
  omega

theorem lookup_names : NamesAccounted (lookup layout P comparison correct).program.code 5 := by
  obtain ⟨body, accepted, resultEq⟩ := Option.map_eq_some_iff.mp (EncodedLookup.compiled layout.lookup P comparison correct)
  change NamesAccounted (EncodedLookup.implementation layout.lookup P comparison correct).program.code 5
  rw [← resultEq]
  exact (EncodedLookup.certificate layout.lookup).names 5 (EncodedLookup.primitiveNames layout.lookup) body accepted

theorem names : NamesAccounted (implementation layout P comparison correct).program.code 5 := by
  have pairedNames : NamesAccounted (paired layout P comparison correct).program.code 5 :=
    Pairing.names _ _ _ _ _ _ _ _
      (by apply layout.lookup.fits_of_le; simp [LookupLayout.width]; omega)
      (lookup_names layout P comparison correct) (skip_names 5)
  exact pairedNames.seq (CacheFinish.names layout 5)

theorem staticMemory (registers buffers : Nat) :
    staticWords (implementation layout P comparison correct).program.code registers buffers ≤
      5 * codeBudget layout + 20 + registers + 3 * buffers := by
  have codeBound := (bounded layout P comparison correct).code_le
  have nameBound := names layout P comparison correct
  rcases nameBound with ⟨registerBound, bufferBound⟩
  unfold staticWords
  omega

/-- Includes stored code, dense register/descriptor metadata, all initial caller
capacity, and every intermediate or final state of the executed cache update. -/
theorem memoryBound (tape : RandomTape w) (environment : layout.input.Value) (before : State w)
    (represented : layout.input.representation.Holds environment before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout P comparison correct).program.code before after
        ((implementation layout P comparison correct).program.time environment) net peak ∧
      layout.lookup.table.representation.Holds
        ⟨(cacheProgram comparison).denote P environment.val,
          (implementation layout P comparison correct).preserves environment.val environment.property⟩ after ∧
      (implementation layout P comparison correct).program.time environment ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout P comparison correct).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation layout P comparison correct).program.code)) ∧
        between.SupportBound (max buffers (implementation layout P comparison correct).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation layout P comparison correct).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout P comparison correct).program.code.memBound) ≤
            5 * codeBudget layout + 20 + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, peakBound⟩ :=
    (bounded layout P comparison correct).exec (by decide) tape environment before represented
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers represented.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := staticMemory layout P comparison correct registers buffers
  omega

end Signatures.Runtime.CaliperBackend.EncodedCache

import Proofs.Runtime.Caliper.CacheReadMemory

/-! Scratch-buffer extents for the effectful cache. An outer caller can reserve
its frame beyond this extent without requiring the whole code size to fit in
one address. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource

namespace Interactive
variable {w : Nat} {I : Type} {spec : OracleSpec I}
theorem dispatch_buffers (port : Port w spec) (left right : Code w) (leftWords rightWords : Nat) :
    ((dispatch left right leftWords rightWords).lower port).memBound ≤ max 2 (max (left.lower port).memBound (right.lower port).memBound) := by
  have one := selectSlice_buffers (w := w) 1 leftWords
  have two := selectSlice_buffers (w := w) 1 rightWords
  simp only [dispatch, Code.lower, WordIO.Code.memBound, Stmt.memBound]
  omega
end Interactive

namespace CacheRead
variable {w : Nat} {K V I : Type} {spec : OracleSpec I}
    (layout : CacheLayout w K V) (port : Interactive.Port w spec) (draw : Interactive.Code w)

theorem hit_buffers : (hit layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (cached layout) (oldTable layout) layout.wordFits
    (nameFits layout _ (cached_buffers layout) (by decide)) (nameFits layout _ (oldTable_buffers layout) (by decide))
    (frame_duplicateFits layout) (frame_valueFits layout) (outputFits layout) (cached_buffers layout) (oldTable_buffers layout)

theorem branch_buffers : ((branchCode layout port draw).lower port).memBound ≤ max 5 ((draw.lower port).memBound + 1) := by
  have retained := Interactive.retain_buffers port draw layout.lookup.unit.representation.encoding.words
    layout.value.representation.encoding.words (no layout).representation.encoding.words
  have finished := finish_buffers layout
  have hit := hit_buffers layout
  have dispatched := Interactive.dispatch_buffers port (.compute (CacheRead.hit layout).program.code) (missCode layout port draw)
    (yes layout).representation.encoding.words (no layout).representation.encoding.words
  change ((branchCode layout port draw).lower port).memBound ≤
    max 2 (max (CacheRead.hit layout).program.code.memBound
      (max ((drawCode layout port draw).lower port).memBound (finish layout).program.code.memBound)) at dispatched
  change ((drawCode layout port draw).lower port).memBound ≤ _ at retained
  omega
end CacheRead

namespace EncodedCacheRead
variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : CacheLayout w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem choose_buffers : (choose layout P comparison correct).program.code.memBound ≤ 8 := by
  have paired : (EncodedCache.paired layout P comparison correct).program.code.memBound ≤ 8 :=
    (Nat.le_max_left _ _).trans (EncodedCache.buffers layout P comparison correct)
  have test : (CacheFinish.test layout).program.code.memBound ≤ 2 :=
    max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
  have selected := GuardedBranch.selector_buffers (hw := layout.wordFits) (CacheFinish.test layout)
    (CacheFinish.test_nameFits layout) layout.frame_duplicateFits layout.frame_tagFits test
  change max _ _ ≤ _
  exact max_le paired (selected.trans (by omega))

theorem buffers {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec) (draw : Interactive.Code w) :
    ((code layout P comparison correct port draw).lower port).memBound ≤ max 8 ((draw.lower port).memBound + 1) := by
  have chosen := choose_buffers layout P comparison correct
  have branches := CacheRead.branch_buffers layout port draw
  change max (choose layout P comparison correct).program.code.memBound ((CacheRead.branchCode layout port draw).lower port).memBound ≤ _
  omega
end EncodedCacheRead
end Signatures.Runtime.CaliperBackend

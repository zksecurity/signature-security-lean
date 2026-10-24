import Proofs.Runtime.Caliper.StatefulCacheMemory

/-! Scratch-buffer bounds for retaining another caller frame around the
stateful cache. Buffer names depend on the fresh routine's footprint, not on
the cache capacity or the size of its stored program. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper BoundedSource Assembly

namespace SumContext
variable {w : Nat} {A B S : Type}
    (left : Representation w A) (right : Representation w B) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (fits : 1 + max left.encoding.words right.encoding.words + saved.encoding.words < 2 ^ w)

theorem unpad_buffers (value : Representation w A) (padding : Nat)
    (fit : value.encoding.words + padding + saved.encoding.words < 2 ^ w) :
    (unpad value saved padding hw fit).code.memBound ≤ 2 :=
  (code_names _ 1 ((sourcesBound_append _ _ _).mpr
    ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩)).2

theorem buffers : (distribute left right saved hw fits).code.memBound ≤ 3 := by
  have first := unpad_buffers saved hw left (max left.encoding.words right.encoding.words - left.encoding.words) (by omega)
  have second := unpad_buffers saved hw right (max left.encoding.words right.encoding.words - right.encoding.words) (by omega)
  have taggedLeft := (inl_names (left.prod saved (by omega)) (right.prod saved (by omega)) hw
    (output left right saved hw fits).fits).buffers
  have taggedRight := (inr_names (left.prod saved (by omega)) (right.prod saved (by omega)) hw
    (output left right saved hw fits).fits).buffers
  have dispatched := Dispatch.buffers
    ((unpad left saved (max left.encoding.words right.encoding.words - left.encoding.words) hw (by omega)).code ;; (inlRealizer .unit (by decide) (left.prod saved (by omega)) (right.prod saved (by omega)) hw (output left right saved hw fits).fits).code)
    ((unpad right saved (max left.encoding.words right.encoding.words - right.encoding.words) hw (by omega)).code ;; (inrRealizer .unit (by decide) (left.prod saved (by omega)) (right.prod saved (by omega)) hw (output left right saved hw fits).fits).code)
    (leftFrame left right saved fits).encoding.words (rightFrame left right saved fits).encoding.words
  change (distribute left right saved hw fits).code.memBound ≤ _ at dispatched
  simp only [Stmt.memBound] at dispatched
  omega
end SumContext

namespace StatefulCacheRead
variable {w : Nat} {K V S I : Type} {spec : OracleSpec I}
    (layout : Layouts w K V S) (port : Interactive.Port w spec)

theorem swap_buffers : (swap layout).code.memBound ≤ 2 := Reorder.buffers _ _ _
theorem shuffle_buffers : (shuffle layout).code.memBound ≤ 2 :=
  max_le (Reorder.buffers _ _ _) (Reorder.buffers _ _ _)

theorem hit_buffers : ((hitCode layout port).lower port).memBound ≤ 4 := by
  have retained := Interactive.retain_buffers port (.compute (CacheRead.hit layout.cache).program.code)
    (CacheRead.yes layout.cache).representation.encoding.words
    (CacheRead.output layout.cache).representation.encoding.words layout.saved.encoding.words
  have bounded := CacheRead.hit_buffers layout.cache
  change ((hitCode layout port).lower port).memBound ≤ max 2 (CacheRead.hit layout.cache).program.code.memBound + 1 at retained
  omega

theorem insert_buffers : ((insertCode layout port).lower port).memBound ≤ 6 := by
  have retained := Interactive.retain_buffers port (.compute (CacheRead.finish layout.cache).program.code)
    (CacheRead.drawn layout.cache).representation.encoding.words
    (CacheRead.output layout.cache).representation.encoding.words layout.saved.encoding.words
  have bounded := CacheRead.finish_buffers layout.cache
  change ((insertCode layout port).lower port).memBound ≤ max 2 (CacheRead.finish layout.cache).program.code.memBound + 1 at retained
  omega

theorem branch_buffers (draw : Interactive.Code w) :
    ((branchCode layout port draw).lower port).memBound ≤ max 6 ((draw.lower port).memBound + 1) := by
  have swapped := swap_buffers layout
  have shuffled := shuffle_buffers layout
  have inserted := insert_buffers layout port
  have hit := hit_buffers layout port
  have retained := Interactive.retain_buffers port draw layout.saved.encoding.words
    layout.freshOutput.encoding.words (CacheRead.no layout.cache).representation.encoding.words
  have dispatched := Interactive.dispatch_buffers port (hitCode layout port) (missCode layout port draw)
    layout.hitInput.encoding.words layout.missInput.encoding.words
  change ((branchCode layout port draw).lower port).memBound ≤ max 2
    (max ((hitCode layout port).lower port).memBound (max (swap layout).code.memBound
      (max _ (max (shuffle layout).code.memBound ((insertCode layout port).lower port).memBound)))) at dispatched
  omega

section Lookup
variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom} [DecidableEq (key.Value base)]
    (layout : Layouts w (key.Value base) (val.Value base) S)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem select_buffers : ((selectCode port layout P comparison correct).lower port).memBound ≤ 9 := by
  have retained := Interactive.retain_buffers port (.compute (EncodedCacheRead.choose layout.cache P comparison correct).program.code)
    layout.cache.input.representation.encoding.words (CacheRead.choice layout.cache).representation.encoding.words layout.saved.encoding.words
  have chosen := EncodedCacheRead.choose_buffers layout.cache P comparison correct
  have distributed := SumContext.buffers (CacheRead.yes layout.cache).representation (CacheRead.no layout.cache).representation
    layout.saved layout.cache.wordFits (choiceFrame layout).fits
  change (distribute layout).code.memBound ≤ 3 at distributed
  change _ ≤ max 2 (EncodedCacheRead.choose layout.cache P comparison correct).program.code.memBound + 1 at retained
  change max _ (distribute layout).code.memBound ≤ _
  omega

theorem buffers (draw : Interactive.Code w) :
    ((code port layout P comparison correct draw).lower port).memBound ≤ max 9 ((draw.lower port).memBound + 1) := by
  have selected := select_buffers port layout P comparison correct
  have branches := branch_buffers layout port draw
  change max ((selectCode port layout P comparison correct).lower port).memBound
    ((branchCode layout port draw).lower port).memBound ≤ _
  omega
end Lookup
end StatefulCacheRead
end Signatures.Runtime.CaliperBackend

import Proofs.Runtime.Caliper.CacheFinishBounds
import Proofs.Runtime.Caliper.LookupAcceptance
import Proofs.Runtime.CacheExpr

/-! A total Caliper implementation of the original cache-programming expression.
The only source premise says that the supplied comparator tests key equality.
The lookup and update code are constructed, including their paid saved input.
Full-table hits are admitted; misses require a reachable-state free-slot proof. -/

namespace Signatures.Runtime.CaliperBackend.EncodedCache

open Caliper BoundedSource SourceExpression

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : CacheLayout w (key.Value base) (val.Value base))
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

def lookup := EncodedLookup.implementation layout.lookup P comparison correct

theorem lookup_nameFits : (lookup layout P comparison correct).program.savedBuffer < 2 ^ w := by
  have bound := EncodedLookup.implementation_buffers layout.lookup P comparison correct
  have hw := layout.wordFits
  change max 2 (lookup layout P comparison correct).program.code.memBound < 2 ^ w
  change (lookup layout P comparison correct).program.code.memBound ≤ 7 at bound
  omega

def paired : Implementation .unit layout.lookup.input layout.lookup.accumulatorTail
    (fun value => ((lookupExpr comparison).denote P value, value)) :=
  (lookup layout P comparison correct).pair (Implementation.identity layout.lookup.input (width_pos layout.wordFits))
    (by decide) layout.wordFits (lookup_nameFits layout P comparison correct)
    (by change max 2 0 < 2 ^ w; have hw := layout.wordFits; omega) layout.lookup.input_duplicateFits
    (by apply layout.lookup.fits_of_le; simp [LookupLayout.width]; omega)
    (by apply layout.lookup.fits_of_le; simp [LookupLayout.width]; omega)

def frame : Implementation .unit layout.input layout.frame
    (fun value => ((lookupExpr comparison).denote P value, value)) :=
  ((paired layout P comparison correct).restrictInput layout.admissible).restrictOutput layout.frameGuard (by
    intro value valid
    have equality : (lookupExpr comparison).denote P value = lookupValue value.1 value.2.1 value.2.2.1 := by
      simpa only [Expr.run_value] using lookupExpr_value P comparison correct value.1 value.2.1 value.2.2.1
    change ((lookupExpr comparison).denote P value).1 = false → value.2.2.1.length ≤ layout.capacityPred
    rw [equality]
    exact valid.2)

def implementation : Implementation .unit layout.input layout.lookup.table ((cacheProgram comparison).denote P) :=
  ((frame layout P comparison correct).then (CacheFinish.implementation layout)).castFunction rfl

end Signatures.Runtime.CaliperBackend.EncodedCache

import Proofs.Runtime.Caliper.CacheReadLayout
import Proofs.Runtime.Caliper.PairBounds

/-! Local continuations for cache reads. The hit returns the stored value.
After a primitive draw, all key/value pairing and fixed-capacity insertion is
executed Caliper code; the miss frame supplies the required free-slot proof. -/

namespace Signatures.Runtime.CaliperBackend.CacheRead

open Caliper BoundedSource

variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

def cached : Implementation .unit layout.lookup.accumulatorTail layout.value (fun value => value.1.2) :=
  (CacheFinish.result layout).then (Implementation.second (by decide) _ _ layout.wordFits _)

def oldTable : Implementation .unit layout.lookup.accumulatorTail layout.lookup.table (fun value => value.2.2.2.1) :=
  (CacheFinish.original layout).then (CacheFinish.table layout)

theorem cached_buffers : (cached layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers (by decide) _ _ layout.wordFits _)
    (Implementation.second_buffers (by decide) _ _ layout.wordFits _)

theorem oldTable_buffers : (oldTable layout).program.code.memBound ≤ 2 :=
  CacheFinish.hit_buffers layout

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {out : Layout w B} {f : A → B}
    (body : Implementation .unit input out f) {buffers : Nat} (bound : body.program.code.memBound ≤ buffers)
    (small : buffers ≤ 16) : body.program.savedBuffer < 2 ^ w := by
  have width := layout.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega

def hit : Implementation .unit (yes layout) (output layout) (fun value => (value.1.2, value.2.2.2.1)) :=
  (((cached layout).pair (oldTable layout) (by decide) layout.wordFits
    (nameFits layout _ (cached_buffers layout) (by decide)) (nameFits layout _ (oldTable_buffers layout) (by decide))
    (frame_duplicateFits layout) (frame_valueFits layout) (outputFits layout)).restrictInput layout.frameGuard).restrictInput
      (fun value => value.1.1 = true)

def fresh : Implementation .unit (drawn layout) layout.value Prod.fst :=
  Implementation.first (by decide) _ _ layout.wordFits _

def saved : Implementation .unit (drawn layout) (no layout) Prod.snd :=
  Implementation.second (by decide) _ _ layout.wordFits _

def key : Implementation .unit (drawn layout) layout.key (fun value => value.2.2.1) :=
  (saved layout).then
    ((((CacheFinish.original layout).then (Implementation.first (by decide) layout.key layout.lookup.valueTail layout.wordFits _)).restrictInput
      layout.frameGuard).restrictInput (fun value => value.1.1 = false))

def table : Implementation .unit (drawn layout) layout.lookup.table (fun value => value.2.2.2.2.1) :=
  (saved layout).then (((oldTable layout).restrictInput layout.frameGuard).restrictInput (fun value => value.1.1 = false))

theorem fresh_buffers : (fresh layout).program.code.memBound ≤ 2 := Implementation.first_buffers (by decide) _ _ layout.wordFits _
theorem saved_buffers : (saved layout).program.code.memBound ≤ 2 := Implementation.second_buffers (by decide) _ _ layout.wordFits _
theorem key_buffers : (key layout).program.code.memBound ≤ 2 :=
  max_le (saved_buffers layout) (max_le (Implementation.second_buffers (by decide) _ _ layout.wordFits _)
    (Implementation.first_buffers (by decide) _ _ layout.wordFits _))
theorem table_buffers : (table layout).program.code.memBound ≤ 2 := max_le (saved_buffers layout) (oldTable_buffers layout)

def entry : Implementation .unit (drawn layout) layout.lookup.entry (fun value => (value.2.2.1, value.1)) :=
  (key layout).pair (fresh layout) (by decide) layout.wordFits
    (nameFits layout _ (key_buffers layout) (by decide)) (nameFits layout _ (fresh_buffers layout) (by decide))
    (drawn_duplicateFits layout) (drawn_keyFits layout) _

theorem entry_buffers : (entry layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (key_buffers layout) (fresh_buffers layout)

def arguments : Implementation .unit (drawn layout) layout.entryTable
    (fun value => ((value.2.2.1, value.1), value.2.2.2.2.1)) :=
  (entry layout).pair (table layout) (by decide) layout.wordFits
    (nameFits layout _ (entry_buffers layout) (by decide)) (nameFits layout _ (table_buffers layout) (by decide))
    (drawn_duplicateFits layout) (drawn_entryFits layout) _

theorem arguments_buffers : (arguments layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (entry_buffers layout) (table_buffers layout)

def inserted : Implementation .unit (drawn layout) layout.lookup.table
    (fun value => (value.2.2.1, value.1) :: value.2.2.2.2.1) :=
  ((arguments layout).restrictOutput (fun value => value.2.length ≤ layout.capacityPred)
    (fun _ valid => valid.2.1.2 valid.2.2)).then
      (ListData.fixedCons .unit (by decide) layout.lookup.entry layout.capacityPred layout.wordFits layout.countFits layout.fixedConsFits)

theorem inserted_buffers : (inserted layout).program.code.memBound ≤ 4 :=
  max_le (arguments_buffers layout)
    ((ListData.fixedCons_buffers .unit (by decide) _ _ _ _ _).trans (by decide))

def finish : Implementation .unit (drawn layout) (output layout)
    (fun value => (value.1, (value.2.2.1, value.1) :: value.2.2.2.2.1)) :=
  (fresh layout).pair (inserted layout) (by decide) layout.wordFits
    (nameFits layout _ (fresh_buffers layout) (by decide)) (nameFits layout _ (inserted_buffers layout) (by decide))
    (drawn_duplicateFits layout) (drawn_valueFits layout) (outputFits layout)

theorem finish_buffers : (finish layout).program.code.memBound ≤ 5 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (fresh_buffers layout) (inserted_buffers layout)

end Signatures.Runtime.CaliperBackend.CacheRead

import Proofs.Runtime.Caliper.CacheLayout
import Proofs.Runtime.Caliper.ListFixedCons
import Proofs.Runtime.Caliper.GuardedBranchBounds

/-! Executed fixed-capacity cache updates after lookup. A hit copies the old
table unchanged. A miss copies the original input and prepends within its
existing capacity, using the free-slot invariant of the observed false branch. -/

namespace Signatures.Runtime.CaliperBackend.CacheFinish

open Caliper BoundedSource

variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

def result : Implementation .unit layout.lookup.accumulatorTail layout.lookup.result Prod.fst :=
  Implementation.first (by decide) _ _ layout.wordFits _

def original : Implementation .unit layout.lookup.accumulatorTail layout.lookup.input Prod.snd :=
  Implementation.second (by decide) _ _ layout.wordFits _

def test : Implementation .unit layout.frame layout.lookup.boolean (fun value => value.1.1) :=
  ((result layout).then (Implementation.first (by decide) _ _ layout.wordFits _)).restrictInput layout.frameGuard

def table : Implementation .unit layout.lookup.input layout.lookup.table (fun value => value.2.2.1) :=
  ((Implementation.second (by decide) layout.key layout.lookup.valueTail layout.wordFits _).then
    (Implementation.second (by decide) layout.value layout.lookup.tableTail layout.wordFits _)).then
      (Implementation.first (by decide) layout.lookup.table layout.lookup.unit layout.wordFits _)

/-- Reassociation and dropping a zero-word unit change no stored bytes. -/
def entryTable : Implementation .unit layout.lookup.input layout.entryTable
    (fun value => ((value.1, value.2.1), value.2.2.1)) where
  preserves _ valid := ⟨⟨valid.1, valid.2.1⟩, valid.2.2.1⟩
  program := (Realizer.identity (width_pos layout.wordFits) layout.lookup.input.representation).viewOutput _ _ (by
    intro value
    change (layout.key.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
      layout.value.representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩) ++
        layout.lookup.table.representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩ =
      layout.key.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
        (layout.value.representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩ ++
          (layout.lookup.table.representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩ ++ []))
    simp only [List.append_nil, List.append_assoc])

def hit : Implementation .unit (GuardedBranch.yesInput layout.frame (fun value => value.1.1))
    layout.lookup.table (fun value => value.2.2.2.1) :=
  (((original layout).then (table layout)).restrictInput layout.frameGuard).restrictInput (fun value => value.1.1 = true)

def miss : Implementation .unit (GuardedBranch.noInput layout.frame (fun value => value.1.1))
    layout.lookup.table (fun value => (value.2.1, value.2.2.1) :: value.2.2.2.1) :=
  let prepared := (((original layout).then (entryTable layout)).restrictInput layout.frameGuard).restrictInput
    (fun value => value.1.1 = false)
  let room := prepared.restrictOutput (fun value => value.2.length ≤ layout.capacityPred)
    (fun _ valid => valid.1.2 valid.2)
  room.then (ListData.fixedCons .unit (by decide) layout.lookup.entry layout.capacityPred layout.wordFits layout.countFits layout.fixedConsFits)

theorem test_buffers : (test layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers (by decide) _ _ layout.wordFits _)
    (Implementation.first_buffers (by decide) _ _ layout.wordFits _)

theorem test_nameFits : (test layout).program.savedBuffer < 2 ^ w := by
  have bound := test_buffers layout
  have width := layout.wordFits
  change max 2 (test layout).program.code.memBound < 2 ^ w
  omega

def value (frame : CacheLayout.Frame K V) : List (K × V) :=
  if frame.1.1 = true then frame.2.2.2.1 else (frame.2.1, frame.2.2.1) :: frame.2.2.2.1

def implementation : Implementation .unit layout.frame layout.lookup.table value :=
  GuardedBranch.implementation (hw := layout.wordFits) (test layout) (by decide) (test_nameFits layout)
    layout.frame_duplicateFits layout.frame_tagFits (hit layout) (miss layout)

end Signatures.Runtime.CaliperBackend.CacheFinish

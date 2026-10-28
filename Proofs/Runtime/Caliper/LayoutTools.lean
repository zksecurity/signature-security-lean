import Proofs.Runtime.Caliper.SumContextBounds
import Proofs.Runtime.Caliper.PairBounds
import Proofs.Runtime.Caliper.DataBudgets
import Proofs.Runtime.Caliper.StructuralNames
import Proofs.Runtime.Caliper.BranchBudgets
import Proofs.Runtime.Caliper.TagBounds
import Proofs.Runtime.Caliper.RestrictedLayout
import Proofs.Runtime.Caliper.EncodedConstant

/-! Layout-level wrappers for a few byte-level realizers: distributing a product over a sum,
swapping a pair, and reading a realizer between plain representations as an implementation
between unrestricted layouts. Each keeps the original code and costs. -/
namespace Signatures.Runtime.CaliperBackend.BoundedSource
open Caliper

variable {w : Nat} {A B S : Type}

/-- Word counts of layout products and sums. -/
theorem Layout.prod_words (left : Layout w A) (right : Layout w B)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (left.prod right fits).representation.encoding.words = left.representation.encoding.words + right.representation.encoding.words := rfl
theorem Layout.sum_words (left : Layout w A) (right : Layout w B) (hw : 0 < w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w) :
    (left.sum right hw fits).representation.encoding.words =
      1 + max left.representation.encoding.words right.representation.encoding.words := rfl
theorem Layout.all_words (rep : Representation w A) : (Layout.all rep).representation.encoding.words = rep.encoding.words := rfl

section Distribute
variable (left : Layout w A) (right : Layout w B) (saved : Layout w S) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words +
      saved.representation.encoding.words < 2 ^ w)

/-- The sum-with-context input and output layouts. -/
def distributeInput : Layout w ((A ⊕ B) × S) :=
  (left.sum right (width_pos hw) (by omega)).prod saved (by rw [Layout.sum_words]; exact fits)
def distributeOutput : Layout w ((A × S) ⊕ (B × S)) :=
  (left.prod saved (by omega)).sum (right.prod saved (by omega)) (width_pos hw) (by
    change 1 + max (_ + _) (_ + _) < 2 ^ w; omega)

def Implementation.distribute :
    Implementation .unit (distributeInput left right saved hw fits) (distributeOutput left right saved hw fits)
      SumContext.view where
  preserves value valid := by rcases value with ⟨a | b, s⟩ <;> exact valid
  program := ((SumContext.distribute left.representation right.representation saved.representation hw fits).viewInput _
      (fun value => (sumView left right ⟨value.val.1, value.property.1⟩, ⟨value.val.2, value.property.2⟩))
      (by rintro ⟨⟨a | b, s⟩, valid⟩ <;> rfl)).viewOutput _ _ (by rintro ⟨⟨a | b, s⟩, valid⟩ <;> rfl)

theorem Implementation.distribute_boundedBy : (Implementation.distribute left right saved hw fits).BoundedBy
    (24 * (1 + max left.representation.encoding.words right.representation.encoding.words + saved.representation.encoding.words) + 2)
    (156 * (1 + max left.representation.encoding.words right.representation.encoding.words + saved.representation.encoding.words) + 95) :=
  ⟨fun _ => SumContext.time _ _ _ hw fits _, SumContext.words _ _ _ hw fits⟩

theorem Implementation.distribute_names : NamesAccounted (Implementation.distribute left right saved hw fits).program.code 3 :=
  SumContext.names _ _ _ hw fits
end Distribute

section Swap
variable (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)

def Implementation.swap : Implementation .unit (left.prod right fits) (right.prod left (by omega)) Prod.swap where
  preserves _ valid := ⟨valid.2, valid.1⟩
  program := ((Pairing.swap .unit (by decide) left.representation right.representation hw fits).viewInput _
    (productView left right) (fun _ => rfl)).viewOutput _ _ (fun _ => rfl)

theorem Implementation.swap_boundedBy : (Implementation.swap left right hw fits).BoundedBy
    (8 * (left.representation.encoding.words + right.representation.encoding.words))
    (26 * (left.representation.encoding.words + right.representation.encoding.words) + 14) :=
  ⟨fun value => Pairing.swap_time_unit_le _ _ hw fits (productView left right value),
    Pairing.swap_descriptionWords_le .unit (by decide) _ _ hw fits⟩

theorem Implementation.swap_names (slots : Nat) : NamesAccounted (Implementation.swap left right hw fits).program.code slots :=
  Reorder.names _ _ _ slots
end Swap

section Realizers
variable {input : Representation w A} {output : Representation w B} {f : A → B}

/-- A realizer between representations, as an implementation between the unrestricted layouts. -/
def Implementation.ofRealizer (body : Realizer .unit input output f) :
    Implementation .unit (Layout.all input) (Layout.all output) f where
  preserves _ _ := trivial
  program := (body.viewInput (Layout.all input).representation Subtype.val (fun _ => rfl)).viewOutput _ _ (fun _ => rfl)

theorem Implementation.ofRealizer_boundedBy (body : Realizer .unit input output f) {time words : Nat}
    (timeBound : ∀ value, body.time value ≤ time) (wordsBound : descriptionWords body.code ≤ words) :
    (Implementation.ofRealizer body).BoundedBy time words :=
  ⟨fun value => timeBound value.val, wordsBound⟩

theorem Implementation.ofRealizer_names (body : Realizer .unit input output f) {slots : Nat}
    (names : NamesAccounted body.code slots) : NamesAccounted (Implementation.ofRealizer body).program.code slots := names

/-- An implementation between unrestricted layouts, as a realizer between the representations. -/
def Implementation.toRealizer (body : Implementation .unit (Layout.all input) (Layout.all output) f) :
    Realizer .unit input output f :=
  (body.program.viewInput input (fun value => ⟨value, trivial⟩) (fun _ => rfl)).viewOutput output f (fun _ => rfl)
end Realizers

section Casts
variable (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)

/-- Reassociate the unrestricted layout of a product as a product of unrestricted layouts. -/
def Implementation.allProd {a : Representation w A} {b : Representation w B}
    (fits : a.encoding.words + b.encoding.words < 2 ^ w) :
    Implementation .unit (Layout.all (a.prod b fits)) ((Layout.all a).prod (Layout.all b) fits) id :=
  Implementation.view (width_pos hw) (fun _ _ => ⟨trivial, trivial⟩) (fun _ => rfl)

def Implementation.allProd' {a : Representation w A} {b : Representation w B}
    (fits : a.encoding.words + b.encoding.words < 2 ^ w) :
    Implementation .unit ((Layout.all a).prod (Layout.all b) fits) (Layout.all (a.prod b fits)) id :=
  Implementation.view (width_pos hw) (fun _ _ => trivial) (fun _ => rfl)

/-- Read the unrestricted layout of a sum as a sum of unrestricted layouts. -/
def Implementation.allSum {a : Representation w A} {b : Representation w B}
    (fits : 1 + max a.encoding.words b.encoding.words < 2 ^ w) :
    Implementation .unit (Layout.all (a.sum b (width_pos hw) fits)) ((Layout.all a).sum (Layout.all b) (width_pos hw) fits) id :=
  Implementation.view (width_pos hw) (fun value _ => by cases value <;> trivial) (by rintro ⟨a | b, _⟩ <;> rfl)

def Implementation.allSum' {a : Representation w A} {b : Representation w B}
    (fits : 1 + max a.encoding.words b.encoding.words < 2 ^ w) :
    Implementation .unit ((Layout.all a).sum (Layout.all b) (width_pos hw) fits) (Layout.all (a.sum b (width_pos hw) fits)) id :=
  Implementation.view (width_pos hw) (fun _ _ => trivial) (by rintro ⟨a | b, _⟩ <;> rfl)
end Casts

end Signatures.Runtime.CaliperBackend.BoundedSource

namespace Signatures.Runtime.CaliperBackend.BoundedSource
open Caliper

variable {w : Nat} {A B D : Type}

section Injections
variable (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w)

def Implementation.inl : Implementation .unit left (left.sum right (width_pos hw) fits) Sum.inl where
  preserves _ valid := valid
  program := (inlRealizer .unit (by decide) left.representation right.representation hw fits).viewOutput _ _ (fun _ => rfl)
def Implementation.inr : Implementation .unit right (left.sum right (width_pos hw) fits) Sum.inr where
  preserves _ valid := valid
  program := (inrRealizer .unit (by decide) left.representation right.representation hw fits).viewOutput _ _ (fun _ => rfl)

theorem Implementation.inl_boundedBy : (Implementation.inl left right hw fits).BoundedBy
    (8 * (1 + max left.representation.encoding.words right.representation.encoding.words))
    (26 * (1 + max left.representation.encoding.words right.representation.encoding.words) + 14) :=
  ⟨fun value => inl_time _ _ hw fits value, inl_words _ _ hw fits⟩
theorem Implementation.inr_boundedBy : (Implementation.inr left right hw fits).BoundedBy
    (8 * (1 + max left.representation.encoding.words right.representation.encoding.words))
    (26 * (1 + max left.representation.encoding.words right.representation.encoding.words) + 14) :=
  ⟨fun value => inr_time _ _ hw fits value, inr_words _ _ hw fits⟩
theorem Implementation.inl_names : NamesAccounted (Implementation.inl left right hw fits).program.code 3 :=
  (_root_.Signatures.Runtime.CaliperBackend.inl_names _ _ hw fits).accounted
theorem Implementation.inr_names : NamesAccounted (Implementation.inr left right hw fits).program.code 3 :=
  (_root_.Signatures.Runtime.CaliperBackend.inr_names _ _ hw fits).accounted
theorem Implementation.inl_buffers : (Implementation.inl left right hw fits).program.code.memBound ≤ 3 :=
  (_root_.Signatures.Runtime.CaliperBackend.inl_names _ _ hw fits).buffers
theorem Implementation.inr_buffers : (Implementation.inr left right hw fits).program.code.memBound ≤ 3 :=
  (_root_.Signatures.Runtime.CaliperBackend.inr_names _ _ hw fits).buffers
end Injections

section Projections
variable (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)

/-- The components of a product, read through the unrestricted layout of the product. -/
def Implementation.allFirst : Implementation .unit (Layout.all (left.prod right fits).representation)
    (Layout.all left.representation) (fun value => ⟨value.val.1, value.property.1⟩) where
  preserves _ _ := trivial
  program := ((firstRealizer .unit (by decide) left.representation right.representation hw fits).viewInput _
    (fun value => productView left right value.val) (fun _ => rfl)).viewOutput _ _ (fun _ => rfl)
def Implementation.allSecond : Implementation .unit (Layout.all (left.prod right fits).representation)
    (Layout.all right.representation) (fun value => ⟨value.val.2, value.property.2⟩) where
  preserves _ _ := trivial
  program := ((secondRealizer .unit (by decide) left.representation right.representation hw fits).viewInput _
    (fun value => productView left right value.val) (fun _ => rfl)).viewOutput _ _ (fun _ => rfl)

theorem Implementation.allFirst_boundedBy : (Implementation.allFirst left right hw fits).BoundedBy
    (8 * left.representation.encoding.words) (26 * left.representation.encoding.words + 14) := by
  constructor
  · intro _
    change (selectSlice (w := w) 0 left.representation.encoding.words).staticTime .unit ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · exact (selectSlice_descriptionWords 0 left.representation.encoding.words).le
theorem Implementation.allSecond_boundedBy : (Implementation.allSecond left right hw fits).BoundedBy
    (8 * right.representation.encoding.words) (26 * right.representation.encoding.words + 14) := by
  constructor
  · intro _
    change (selectSlice (w := w) left.representation.encoding.words right.representation.encoding.words).staticTime .unit ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · exact (selectSlice_descriptionWords _ right.representation.encoding.words).le
theorem Implementation.allFirst_names (slots : Nat) : NamesAccounted (Implementation.allFirst left right hw fits).program.code slots :=
  selectSlice_names _ _ _
theorem Implementation.allSecond_names (slots : Nat) : NamesAccounted (Implementation.allSecond left right hw fits).program.code slots :=
  selectSlice_names _ _ _
theorem Implementation.allFirst_buffers : (Implementation.allFirst left right hw fits).program.code.memBound ≤ 2 := selectSlice_buffers _ _
theorem Implementation.allSecond_buffers : (Implementation.allSecond left right hw fits).program.code.memBound ≤ 2 := selectSlice_buffers _ _
end Projections

section Recast
variable (hw : 0 < w)

/-- Reinterpret the stored bytes under another layout and carrier, with no executed instruction. -/
def Implementation.recast (left : Layout w A) (right : Layout w B) (f : A → B)
    (preserves : ∀ value, left.valid value → right.valid (f value))
    (sameBytes : ∀ value : left.Value, right.representation.encoding.encode ⟨f value.val, preserves value.val value.property⟩ =
      left.representation.encoding.encode value) : Implementation .unit left right f where
  preserves := preserves
  program := (Realizer.identity hw left.representation).viewOutput _ _ sameBytes

theorem Implementation.recast_boundedBy (left : Layout w A) (right : Layout w B) (f : A → B) (preserves) (sameBytes) :
    (Implementation.recast hw left right f preserves sameBytes).BoundedBy 0 1 := ⟨fun _ => le_rfl, le_rfl⟩
theorem Implementation.recast_names (left : Layout w A) (right : Layout w B) (f : A → B) (preserves) (sameBytes) (slots : Nat) :
    NamesAccounted (Implementation.recast hw left right f preserves sameBytes).program.code slots := skip_names slots
theorem Implementation.recast_buffers (left : Layout w A) (right : Layout w B) (f : A → B) (preserves) (sameBytes) :
    (Implementation.recast hw left right f preserves sameBytes).program.code.memBound ≤ 0 := le_rfl

/-- Drop the certificate of an unrestricted layout over a layout's values. -/
def Implementation.unall (layout : Layout w A) : Implementation .unit (Layout.all layout.representation) layout Subtype.val :=
  Implementation.recast hw _ _ _ (fun value _ => value.property) (fun _ => rfl)
end Recast

end Signatures.Runtime.CaliperBackend.BoundedSource

namespace Signatures.Runtime.CaliperBackend.BoundedSource
open Caliper

variable {w : Nat} {A B D : Type}

section Buffers
variable {input : Layout w A} {middle : Layout w B} {output : Layout w D} {f : A → B} {g : B → D}

theorem Implementation.then_buffers (first : Implementation .unit input middle f) (second : Implementation .unit middle output g)
    {a b : Nat} (left : first.program.code.memBound ≤ a) (right : second.program.code.memBound ≤ b) :
    (first.then second).program.code.memBound ≤ max a b := max_le_max left right
theorem Implementation.then_names (first : Implementation .unit input middle f) (second : Implementation .unit middle output g)
    {slots : Nat} (left : NamesAccounted first.program.code slots) (right : NamesAccounted second.program.code slots) :
    NamesAccounted (first.then second).program.code slots := left.seq right

theorem Implementation.branch_buffers {left : Layout w A} {right : Layout w B} {f : A → D} {g : B → D}
    (first : Implementation .unit left output f) (second : Implementation .unit right output g) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w)
    {a b : Nat} (leftBound : first.program.code.memBound ≤ a) (rightBound : second.program.code.memBound ≤ b) :
    (first.branch second (by decide) hw fits).program.code.memBound ≤ max 2 (max a b) :=
  (Dispatch.buffers first.program.code second.program.code _ _).trans (by omega)
theorem Implementation.branch_names {left : Layout w A} {right : Layout w B} {f : A → D} {g : B → D}
    (first : Implementation .unit left output f) (second : Implementation .unit right output g) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w)
    {slots : Nat} (leftBound : NamesAccounted first.program.code slots) (rightBound : NamesAccounted second.program.code slots) :
    NamesAccounted (first.branch second (by decide) hw fits).program.code slots :=
  Dispatch.names leftBound rightBound _ _

theorem Implementation.castFunction_buffers (body : Implementation .unit input middle f) {g : A → B} (equal : f = g) {a : Nat}
    (bound : body.program.code.memBound ≤ a) : (body.castFunction equal).program.code.memBound ≤ a := bound
theorem Implementation.castFunction_names (body : Implementation .unit input middle f) {g : A → B} (equal : f = g) {slots : Nat}
    (bound : NamesAccounted body.program.code slots) : NamesAccounted (body.castFunction equal).program.code slots := bound
theorem Implementation.restrictInput_buffers (body : Implementation .unit input middle f) (predicate : A → Prop) [DecidablePred predicate]
    {a : Nat} (bound : body.program.code.memBound ≤ a) : (body.restrictInput predicate).program.code.memBound ≤ a := bound
theorem Implementation.restrictInput_names (body : Implementation .unit input middle f) (predicate : A → Prop) [DecidablePred predicate]
    {slots : Nat} (bound : NamesAccounted body.program.code slots) : NamesAccounted (body.restrictInput predicate).program.code slots := bound
theorem Implementation.view_buffers {input output : Layout w A} (hw : 0 < w) (preserves : ∀ value, input.valid value → output.valid value)
    (sameBytes : ∀ value : input.Value,
      output.representation.encoding.encode ⟨value.val, preserves value.val value.property⟩ = input.representation.encoding.encode value) :
    (Implementation.view (cost := .unit) hw preserves sameBytes).program.code.memBound ≤ 0 := le_rfl
theorem Implementation.view_names {input output : Layout w A} (hw : 0 < w) (preserves : ∀ value, input.valid value → output.valid value)
    (sameBytes : ∀ value : input.Value,
      output.representation.encoding.encode ⟨value.val, preserves value.val value.property⟩ = input.representation.encoding.encode value)
    (slots : Nat) : NamesAccounted (Implementation.view (cost := .unit) hw preserves sameBytes).program.code slots := skip_names slots
theorem Implementation.identity_buffers (hw : 0 < w) : (Implementation.identity (cost := .unit) input hw).program.code.memBound ≤ 0 := le_rfl
theorem Implementation.identity_names (hw : 0 < w) (slots : Nat) :
    NamesAccounted (Implementation.identity (cost := .unit) input hw).program.code slots := skip_names slots
theorem Implementation.ofRealizer_buffers {a : Representation w A} {b : Representation w B} {h : A → B} (body : Realizer .unit a b h)
    {n : Nat} (bound : body.code.memBound ≤ n) : (Implementation.ofRealizer body).program.code.memBound ≤ n := bound

theorem Implementation.swap_buffers (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (Implementation.swap left right hw fits).program.code.memBound ≤ 2 := Reorder.buffers _ _ _
theorem Implementation.distribute_buffers (left : Layout w A) (right : Layout w B) (saved : Layout w D) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words + saved.representation.encoding.words < 2 ^ w) :
    (Implementation.distribute left right saved hw fits).program.code.memBound ≤
      3 + (156 * (1 + max left.representation.encoding.words right.representation.encoding.words + saved.representation.encoding.words) + 95) :=
  (Implementation.distribute_names left right saved hw fits).buffers.trans
    (Nat.add_le_add_left (Implementation.distribute_boundedBy left right saved hw fits).code_le _)

/-- A saved-buffer name fits whenever the buffer count does. -/
theorem Implementation.savedBuffer_lt (body : Implementation .unit input middle f) {n : Nat}
    (bound : body.program.code.memBound ≤ n) (room : n + 2 < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  change max 2 body.program.code.memBound < 2 ^ w
  omega
end Buffers

end Signatures.Runtime.CaliperBackend.BoundedSource

namespace Signatures.Runtime.CaliperBackend.BoundedSource
open Caliper

variable {w : Nat} {A B D : Type}

section Pair
variable {input : Layout w A} {left : Layout w B} {right : Layout w D} {f : A → B} {g : A → D}
    (first : Implementation .unit input left f) (second : Implementation .unit input right g) (hw : 16 < 2 ^ w)
    {a b : Nat} (firstBuffers : first.program.code.memBound ≤ a) (secondBuffers : second.program.code.memBound ≤ b)
    (room : max a b + 2 < 2 ^ w)
    (fits : input.representation.encoding.words + input.representation.encoding.words +
      left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)

/-- `pair` with its side conditions derived from buffer bounds and one storage bound. -/
def Implementation.pair' : Implementation .unit input (left.prod right (by omega)) (fun value => (f value, g value)) :=
  first.pair second (by decide) hw (first.savedBuffer_lt firstBuffers (by omega)) (second.savedBuffer_lt secondBuffers (by omega))
    (by omega) (by omega) (by omega)

theorem Implementation.pair'_boundedBy {firstTime firstWords secondTime secondWords : Nat}
    (firstBound : first.BoundedBy firstTime firstWords) (secondBound : second.BoundedBy secondTime secondWords) :
    (first.pair' second hw firstBuffers secondBuffers room fits).BoundedBy
      (firstTime + secondTime + 52 * input.representation.encoding.words + 36 * left.representation.encoding.words +
        16 * right.representation.encoding.words)
      (firstWords + secondWords + 169 * input.representation.encoding.words + 117 * left.representation.encoding.words +
        52 * right.representation.encoding.words + 124) :=
  Implementation.pair_boundedBy _ _ _ _ _ _ _ _ firstBound secondBound
theorem Implementation.pair'_buffers :
    (first.pair' second hw firstBuffers secondBuffers room fits).program.code.memBound ≤ max 2 (max a b) + 1 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ firstBuffers secondBuffers
theorem Implementation.pair'_names {slots : Nat}
    (firstNames : NamesAccounted first.program.code slots) (secondNames : NamesAccounted second.program.code slots) :
    NamesAccounted (first.pair' second hw firstBuffers secondBuffers room fits).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ firstNames secondNames
end Pair

end Signatures.Runtime.CaliperBackend.BoundedSource

namespace Signatures.Runtime.CaliperBackend.BoundedSource
open Caliper

/-! ## Bounds through explicit width bounds

Compound layouts carry fit proofs whose types mention component widths, which blocks
rewriting their word counts. These variants take upper bounds on every component width
instead, so derived budgets only mention the supplied numbers. -/

variable {w : Nat} {A B D : Type}

section Primed
variable {input : Layout w A} {left : Layout w B} {right : Layout w D}

theorem Implementation.pair'_boundedBy' {f : A → B} {g : A → D}
    (first : Implementation .unit input left f) (second : Implementation .unit input right g) (hw : 16 < 2 ^ w)
    {a b : Nat} (firstBuffers : first.program.code.memBound ≤ a) (secondBuffers : second.program.code.memBound ≤ b)
    (room : max a b + 2 < 2 ^ w)
    (fits : input.representation.encoding.words + input.representation.encoding.words +
      left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {firstTime firstWords secondTime secondWords i l r : Nat}
    (firstBound : first.BoundedBy firstTime firstWords) (secondBound : second.BoundedBy secondTime secondWords)
    (hi : input.representation.encoding.words ≤ i) (hl : left.representation.encoding.words ≤ l)
    (hr : right.representation.encoding.words ≤ r) :
    (first.pair' second hw firstBuffers secondBuffers room fits).BoundedBy
      (firstTime + secondTime + 52 * i + 36 * l + 16 * r) (firstWords + secondWords + 169 * i + 117 * l + 52 * r + 124) :=
  (Implementation.pair'_boundedBy first second hw firstBuffers secondBuffers room fits firstBound secondBound).mono
    (by omega) (by omega)

theorem Implementation.branch_boundedBy' {output : Layout w A} {f : B → A} {g : D → A}
    (first : Implementation .unit left output f) (second : Implementation .unit right output g) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w)
    {firstTime firstWords secondTime secondWords l r : Nat}
    (firstBound : first.BoundedBy firstTime firstWords) (secondBound : second.BoundedBy secondTime secondWords)
    (hl : left.representation.encoding.words ≤ l) (hr : right.representation.encoding.words ≤ r) :
    (first.branch second (by decide) hw fits).BoundedBy
      (firstTime + secondTime + 8 * (l + r) + 2) (firstWords + secondWords + 26 * l + 26 * r + 37) :=
  (Implementation.branch_boundedBy first second hw fits _ _ _ _ firstBound secondBound).mono (by omega) (by omega)

theorem Implementation.distribute_boundedBy' (saved : Layout w A) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words + saved.representation.encoding.words < 2 ^ w)
    {l r s : Nat} (hl : left.representation.encoding.words ≤ l) (hr : right.representation.encoding.words ≤ r)
    (hs : saved.representation.encoding.words ≤ s) :
    (Implementation.distribute left right saved hw fits).BoundedBy (24 * (1 + l + r + s) + 2) (156 * (1 + l + r + s) + 95) :=
  (Implementation.distribute_boundedBy left right saved hw fits).mono (by omega) (by omega)

theorem Implementation.inl_boundedBy' (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w)
    {l r : Nat} (hl : left.representation.encoding.words ≤ l) (hr : right.representation.encoding.words ≤ r) :
    (Implementation.inl left right hw fits).BoundedBy (8 * (1 + l + r)) (26 * (1 + l + r) + 14) :=
  (Implementation.inl_boundedBy left right hw fits).mono (by omega) (by omega)
theorem Implementation.inr_boundedBy' (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w)
    {l r : Nat} (hl : left.representation.encoding.words ≤ l) (hr : right.representation.encoding.words ≤ r) :
    (Implementation.inr left right hw fits).BoundedBy (8 * (1 + l + r)) (26 * (1 + l + r) + 14) :=
  (Implementation.inr_boundedBy left right hw fits).mono (by omega) (by omega)

theorem Implementation.first_boundedBy' (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {l : Nat} (hl : left.representation.encoding.words ≤ l) :
    (Implementation.first (cost := .unit) (by decide) left right hw fits).BoundedBy (8 * l) (26 * l + 14) :=
  (Implementation.first_boundedBy left right hw fits).mono (by omega) (by omega)
theorem Implementation.second_boundedBy' (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {r : Nat} (hr : right.representation.encoding.words ≤ r) :
    (Implementation.second (cost := .unit) (by decide) left right hw fits).BoundedBy (8 * r) (26 * r + 14) :=
  (Implementation.second_boundedBy left right hw fits).mono (by omega) (by omega)
theorem Implementation.allFirst_boundedBy' (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {l : Nat} (hl : left.representation.encoding.words ≤ l) :
    (Implementation.allFirst left right hw fits).BoundedBy (8 * l) (26 * l + 14) :=
  (Implementation.allFirst_boundedBy left right hw fits).mono (by omega) (by omega)
theorem Implementation.allSecond_boundedBy' (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {r : Nat} (hr : right.representation.encoding.words ≤ r) :
    (Implementation.allSecond left right hw fits).BoundedBy (8 * r) (26 * r + 14) :=
  (Implementation.allSecond_boundedBy left right hw fits).mono (by omega) (by omega)
theorem Implementation.swap_boundedBy' (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {l r : Nat} (hl : left.representation.encoding.words ≤ l) (hr : right.representation.encoding.words ≤ r) :
    (Implementation.swap left right hw fits).BoundedBy (8 * (l + r)) (26 * (l + r) + 14) :=
  (Implementation.swap_boundedBy left right hw fits).mono (by omega) (by omega)
theorem Implementation.constant_bounded' {output : Layout w B} (value : output.Value) (hw : 16 < 2 ^ w)
    {o : Nat} (ho : output.representation.encoding.words ≤ o) :
    (Implementation.constant input output value hw).BoundedBy (8 * o) (26 * o + 14) :=
  (Implementation.constant_bounded input output value hw).mono (by omega) (by omega)
end Primed

/-- Widths of products and sums, bounded through their components. -/
theorem Layout.prod_le' (left : Layout w A) (right : Layout w B) (fits) {a b : Nat}
    (ha : left.representation.encoding.words ≤ a) (hb : right.representation.encoding.words ≤ b) :
    (left.prod right fits).representation.encoding.words ≤ a + b := by rw [Layout.prod_words]; omega
theorem Layout.sum_le' (left : Layout w A) (right : Layout w B) (hw : 0 < w) (fits) {a b : Nat}
    (ha : left.representation.encoding.words ≤ a) (hb : right.representation.encoding.words ≤ b) :
    (left.sum right hw fits).representation.encoding.words ≤ 1 + a + b := by rw [Layout.sum_words]; omega
theorem Layout.all_le (rep : Representation w A) {a : Nat} (ha : rep.encoding.words ≤ a) :
    (Layout.all rep).representation.encoding.words ≤ a := ha

end Signatures.Runtime.CaliperBackend.BoundedSource

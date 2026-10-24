import Proofs.Runtime.Caliper.ProximityTerms
import Proofs.Runtime.Caliper.Powers

/-! OOPS term generation combines executed scalar powers with the shared
coordinate/label assembler. Internal keys store the finite degree before the
topic; the exact permutation from the source's topic/degree key is proved. -/
namespace Signatures.Runtime.CaliperBackend.OOPSTerms
open Caliper BoundedSource Assembly

structure Layouts (w : Nat) (F K : Type) (degree : Nat) where
  scalar : Layout w F
  label : Layout w K
  wordFits : 16 < 2 ^ w
  countFits : degree + 1 < 2 ^ w
  storageFits : 64 * ((degree + 2) *
    (1 + label.representation.encoding.words + scalar.representation.encoding.words)) < 2 ^ w

namespace Layouts
variable {w degree : Nat} {F K : Type} (layout : Layouts w F K degree)
def width : Nat := (degree + 2) *
  (1 + layout.label.representation.encoding.words + layout.scalar.representation.encoding.words)
theorem fits_of_le {words : Nat} (bound : words ≤ 64 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
def terms : ProximityTerms.Layouts w F K degree where
  scalar := layout.scalar
  label := layout.label
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by unfold width; nlinarith)
def powers : Powers.Layouts w F degree where
  scalar := layout.scalar
  wordFits := layout.wordFits
  storageFits := layout.fits_of_le (by unfold width; nlinarith)
def input := layout.scalar.prod layout.label (layout.fits_of_le (by unfold width; nlinarith))
def output := layout.terms.output
theorem parts :
    layout.scalar.representation.encoding.words ≤ layout.width ∧
    layout.label.representation.encoding.words ≤ layout.width ∧
    layout.input.representation.encoding.words ≤ layout.width ∧
    layout.terms.vector.representation.encoding.words ≤ layout.width ∧
    layout.terms.width ≤ 2 * layout.width := by
  change _ ≤ _ ∧ _ ≤ _ ∧ (_ + _) ≤ _ ∧ (vectorEncoding layout.scalar degree).words ≤ _ ∧ _ ≤ _
  rw [vectorEncoding_words]
  dsimp only [width, terms, ProximityTerms.Layouts.width]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
end Layouts

variable {w degree : Nat} {F K : Type} [Mul F] [One F] (layout : Layouts w F K degree)
    (oneValid : layout.scalar.valid (1 : F))
    (mul : Implementation .unit layout.powers.input layout.scalar (fun input => input.1 * input.2))
    {slots : Nat} (mulBuffers : mul.program.code.memBound ≤ slots)
    (reserve : Powers.baseSlots slots + degree < 2 ^ w)

def value (input : F × K) : List ((Fin (degree + 1) × K) × F) :=
  ProximityTerms.value (Powers.values degree (input.1, input.1), input.2)

def scalar : Implementation .unit layout.input layout.scalar Prod.fst :=
  Implementation.first (by decide) layout.scalar layout.label layout.wordFits _
def label : Implementation .unit layout.input layout.label Prod.snd :=
  Implementation.second (by decide) layout.scalar layout.label layout.wordFits _
def duplicate : Implementation .unit layout.scalar layout.powers.input (fun x => (x, x)) where
  preserves _ valid := ⟨valid, valid⟩
  program := (duplicateRealizer .unit (by decide) layout.scalar.representation layout.wordFits
    layout.powers.input.representation.fits).viewOutput _ _
    (fun _ => rfl)

omit [Mul F] [One F] in
theorem duplicate_buffers : (duplicate layout).program.code.memBound ≤ 2 :=
  (code_names
    (reads 0 0 layout.scalar.representation.encoding.words ++ reads 0 0 layout.scalar.representation.encoding.words) 1
      ((sourcesBound_append _ _ _).mpr
        ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩)).2

def generated : Implementation .unit layout.input layout.terms.vector
    (fun input => Powers.values degree (input.1, input.1)) :=
  ((scalar layout).then (duplicate layout)).then
    (Powers.compile layout.powers reserve mul mulBuffers degree (Nat.le_refl _)).implementation

omit [One F] in
theorem generated_buffers : (generated layout mul mulBuffers reserve).program.code.memBound ≤
    Powers.baseSlots slots + degree :=
  max_le (max_le
    ((Implementation.first_buffers _ _ _ _ _).trans (by unfold Powers.baseSlots; omega))
    ((duplicate_buffers layout).trans (by unfold Powers.baseSlots; omega)))
    (Powers.compile layout.powers reserve mul mulBuffers degree (Nat.le_refl _)).buffers

def prepare : Implementation .unit layout.input layout.terms.input
    (fun input => (Powers.values degree (input.1, input.1), input.2)) :=
  (generated layout mul mulBuffers reserve).pair (label layout) (by decide) layout.wordFits
    (Powers.nameFits reserve _ (generated_buffers layout mul mulBuffers reserve))
    (Powers.nameFits reserve _ ((Implementation.second_buffers _ _ _ _ _).trans (by unfold Powers.baseSlots; omega)))
    (layout.fits_of_le (by have := layout.parts; omega))
    (layout.fits_of_le (by have := layout.parts; omega))
    layout.terms.input.representation.fits

def implementation : Implementation .unit layout.input layout.output value :=
  (prepare layout mul mulBuffers reserve).then (ProximityTerms.implementation layout.terms oneValid)

theorem buffers : (implementation layout oneValid mul mulBuffers reserve).program.code.memBound ≤
    Powers.baseSlots slots + degree + 1 := by
  have prepared := Implementation.pair_buffers (generated layout mul mulBuffers reserve) (label layout) layout.wordFits
    (Powers.nameFits reserve _ (generated_buffers layout mul mulBuffers reserve))
    (Powers.nameFits reserve _ ((Implementation.second_buffers _ _ _ _ _).trans (by unfold Powers.baseSlots; omega)))
    (layout.fits_of_le (by have := layout.parts; omega))
    (layout.fits_of_le (by have := layout.parts; omega))
    layout.terms.input.representation.fits
    (generated_buffers layout mul mulBuffers reserve) (Implementation.second_buffers _ _ _ _ _)
  have assembled := ProximityTerms.buffers layout.terms oneValid
  change max (prepare layout mul mulBuffers reserve).program.code.memBound _ ≤ _
  apply max_le
  · exact prepared.trans (by unfold Powers.baseSlots; omega)
  · exact assembled.trans (by unfold Powers.baseSlots; omega)

section Source
variable {F K : Type} [CommMonoid F] (degree : Nat) (input : F × K)

theorem source : value (degree := degree) input =
    (OOPS.LazyAGM.terms degree input).map (fun term => ((term.1.2, term.1.1), term.2)) := by
  simp only [value, ProximityTerms.value, OOPS.LazyAGM.terms, List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cases_succ, Powers.values_eq, Fin.val_succ, pow_succ]
    congr 1
    exact mul_comm _ _
end Source

end Signatures.Runtime.CaliperBackend.OOPSTerms

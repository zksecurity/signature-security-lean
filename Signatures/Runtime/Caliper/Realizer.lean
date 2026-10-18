import Signatures.Runtime.Caliper.Encoding
import Signatures.Runtime.Caliper.Description
import Caliper.Tape
import PolyFun.Realizability.Quantitative
import Signatures.Runtime.BackendProgram

/-! Actual Caliper realizers for the existing quantitative interface.

Representations are pinned, bounded encodings. Every realizer contains code and a
total-correctness proof with exact Caliper time and bounds on net/peak workspace.
Identity and composition are implemented by `skip` and `seq`; their execution and
cost laws are proved below. No all-types product/list closure is asserted: fixed
word widths require explicit capacity bounds before such layouts can be built.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper PFunctor

variable {w : Nat} {A B D : Type}

/-- A pinned encoding whose input buffer fits the selected address width. -/
structure Representation (w : Nat) (A : Type) where
  encoding : Encoding w A
  fits : encoding.words < 2 ^ w

/-- Local-call convention: register zero is the zero offset, buffer zero is the
represented value. Other storage is available to the caller and callee subject
to the callee's specification; physical memory includes all reserved capacities. -/
def Representation.Holds (representation : Representation w A) (value : A)
    (state : State w) : Prop :=
  state.regs 0 = 0 ∧ (state.bufs 0).toList = representation.encoding.encode value ∧
  state.WellFormed ∧ ∀ buffer, state.caps buffer < 2 ^ w

/-- Input loading is a boundary convention, not an executable constant-time
instruction. Its complete stored data is charged by `encoding.words`. -/
def Representation.initial (representation : Representation w A) (value : A) : State w where
  regs _ := 0
  bufs buffer := if buffer = 0 then (representation.encoding.encode value).toArray else #[]
  caps buffer := if buffer = 0 then representation.encoding.words else 0

theorem Representation.initial_holds (representation : Representation w A) (value : A) :
    representation.Holds value (representation.initial value) := by
  refine ⟨rfl, by simp [initial], ⟨?_, ?_⟩, ?_⟩
  · intro buffer
    by_cases hb : buffer = 0
    · simp [initial, hb, representation.encoding.encode_length]
    · simp [initial, hb]
  · exact ⟨1, fun buffer hb => by simp [initial, show buffer ≠ 0 by omega]⟩
  · intro buffer
    by_cases hb : buffer = 0
    · simpa [initial, hb] using representation.fits
    · simp [initial, hb]

/-- A deterministic local map implemented by literal Caliper code. The arbitrary
function `f` is only a specification: executable evidence must implement it on
every represented input and every caller state satisfying the convention. -/
structure Realizer (cost : CostModel) (input : Representation w A)
    (output : Representation w B) (f : A → B) where
  code : Stmt w
  positive_width : 0 < w
  description_fits : DescriptionFits code
  random_free : code.RandomFree
  time : A → Nat
  net : A → Int
  workspace : A → Int
  correct : ∀ tape value before, input.Holds value before →
    ∃ after actualNet actualPeak,
      Caliper.Exec cost tape code before after (time value) actualNet actualPeak ∧
      output.Holds (f value) after ∧ actualNet ≤ net value ∧ actualPeak ≤ workspace value

variable {cost : CostModel} {input : Representation w A} {middle : Representation w B}
  {output : Representation w D} {f : A → B} {g : B → D}

def Realizer.identity (hw : 0 < w) (input : Representation w A) : Realizer cost input input id where
  code := .skip
  positive_width := hw
  description_fits := by simp [DescriptionFits, description]
  random_free := trivial
  time _ := 0
  net _ := 0
  workspace _ := 0
  correct _ _ before h := ⟨before, 0, 0, .skip, h, le_rfl, le_rfl⟩

def Realizer.then (first : Realizer cost input middle f)
    (second : Realizer cost middle output g) : Realizer cost input output (g ∘ f) where
  code := .seq first.code second.code
  positive_width := first.positive_width
  description_fits := first.description_fits.seq first.positive_width second.description_fits
  random_free := ⟨first.random_free, second.random_free⟩
  time value := first.time value + second.time (f value)
  net value := first.net value + second.net (f value)
  workspace value := max (first.workspace value) (first.net value + second.workspace (f value))
  correct tape value before h := by
    obtain ⟨between, d₁, p₁, he₁, hm, hd₁, hp₁⟩ := first.correct tape value before h
    obtain ⟨after, d₂, p₂, he₂, ho, hd₂, hp₂⟩ := second.correct tape (f value) between hm
    exact ⟨after, d₁ + d₂, max p₁ (d₁ + p₂), .seq he₁ he₂, ho, by omega, by omega⟩

/-- The cost is determined by actual execution, not a freely assigned upper bound. -/
theorem Realizer.execution_cost (realizer : Realizer cost input middle f)
    {tape : RandomTape w} {value : A} {before after : State w} {elapsed : Nat} {net peak : Int}
    (represented : input.Holds value before)
    (execution : Caliper.Exec cost tape realizer.code before after elapsed net peak) :
    elapsed = realizer.time value := by
  obtain ⟨_, _, _, certified, _, _, _⟩ := realizer.correct tape value before represented
  exact (execution.deterministic certified).2.1

/-- The qualitative class has actual executable witnesses. -/
def stepClass (w : Nat) (hw : 0 < w) (cost : CostModel) : StepClass where
  Str := Representation w
  Hom a b f := Nonempty (Realizer cost a b f)
  id_mem a := ⟨Realizer.identity hw a⟩
  comp_mem := fun ⟨first⟩ ⟨second⟩ => ⟨first.then second⟩

/-- This instantiates PolyFun's quantitative boundary with Caliper execution. -/
def quantitative (w : Nat) (hw : 0 < w) (cost : CostModel) :
    QuantitativeStepClass (stepClass w hw cost) where
  Realizer := Realizer cost
  size representation _ := representation.encoding.words
  cost realizer := realizer.time
  admissible realizer := ⟨realizer⟩

def exactCategory (w : Nat) (hw : 0 < w) (cost : CostModel) :
    (quantitative w hw cost).ExactCategory where
  identity := Realizer.identity hw
  compose := Realizer.then
  composeOverhead _ _ _ := 0
  cost_compose_eq _ _ _ := by simp [quantitative, Realizer.then]

instance (w : Nat) (hw : 0 < w) (cost : CostModel) :
    (quantitative w hw cost).HasCategory := (exactCategory w hw cost).toHasCategory

instance (w : Nat) (hw : 0 < w) (cost : CostModel) :
    (quantitative w hw cost).HasExactCategory := (exactCategory w hw cost).toHasExactCategory

/-- Existing reduction code accounting can use the concrete stored Caliper
description of each local implementation. -/
def descriptionSizes (w : Nat) (hw : 0 < w) (cost : CostModel) :
    BackendProgram.DescriptionSize (quantitative w hw cost) where
  localSize realizer := descriptionWords realizer.code

theorem Realizer.then_description (first : Realizer cost input middle f)
    (second : Realizer cost middle output g) :
    descriptionWords (first.then second).code =
      descriptionWords first.code + descriptionWords second.code + 1 :=
  descriptionWords_seq first.code second.code

end Signatures.Runtime.CaliperBackend

import Proofs.Runtime.Caliper.KeyedStage
import Proofs.Runtime.Caliper.WeightedGood
import Proofs.Runtime.Caliper.WeightedBad
import Proofs.Runtime.Caliper.LayoutTools

/-! Weighted solvers with a known-key draw in front: the challenge is turned into the keyed
challenge `((pk, k•g₂), k)` by a preparation stage, then the complete weighted program runs
over the keyed setup. The good branch draws the known key; the bad branch first resamples
the public key. Both are resource-bounded DLog solvers whose source is the weighted list
reduction on the keyed adversary, with the known key drawn from the certified scalar source. -/
namespace Signatures.Runtime.CaliperBackend.Preparation
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {X Y : Type} {port : Interactive.Port w unifSpec} {input : Layout w X}

/-- Re-type a stage along an equality of output layouts. -/
def Stage.cast {left right : Layout w Y} (same : left = right) (stage : Stage port input left) : Stage port input right := same ▸ stage

theorem Stage.cast_source {left right : Layout w Y} (same : left = right) (stage : Stage port input left) (value : input.Value) :
    (stage.cast same).source value = (fun output => (same ▸ output : right.Value)) <$> stage.source value := by
  subst same; simp [Stage.cast]
theorem cast_val {left right : Layout w Y} (same : left = right) (value : left.Value) : (same ▸ value : right.Value).val = value.val := by
  subst same; rfl
theorem Stage.cast_words {left right : Layout w Y} (same : left = right) (stage : Stage port input left) : (stage.cast same).words = stage.words := by
  subst same; rfl
theorem Stage.cast_time {left right : Layout w Y} (same : left = right) (stage : Stage port input left) : (stage.cast same).time = stage.time := by
  subst same; rfl
theorem Stage.cast_slots {left right : Layout w Y} (same : left = right) (stage : Stage port input left) : (stage.cast same).slots = stage.slots := by
  subst same; rfl

theorem Stage.seq_source {Y' : Type} {middle : Layout w Y} {output : Layout w Y'} (hw : 16 < 2 ^ w)
    (first : Stage port input middle) (second : Stage port middle output) (value : input.Value) :
    (first.seq hw second).source value = first.source value >>= second.source := rfl

/-- Executed code without queries as a stage. -/
def Stage.compute {output : Layout w Y} {f : X → Y} (implementation : Implementation .unit input output f)
    {time words slots : Nat} (bound : implementation.BoundedBy time words) (names : NamesAccounted implementation.program.code slots) :
    Stage port input output where
  code := .compute implementation.program.code
  source value := pure ⟨f value.val, implementation.preserves value.val value.property⟩
  refines := Interactive.Refines.compute port .unit implementation.program
  time := time
  words := words + 1
  slots := slots
  timeBound := Interactive.TimeBound.compute (port := port) (cost := .unit) implementation.program time bound.time_le
  wordsBound := by simpa only [Interactive.Code.lower, WordIO.Code.descriptionWords_compute] using Nat.add_le_add_right bound.code_le 1
  names := WordIO.NamesAccounted.compute names
  fits := .compute implementation.program.description_fits

theorem Stage.compute_source {output : Layout w Y} {f : X → Y} (implementation : Implementation .unit input output f)
    {time words slots : Nat} (bound : implementation.BoundedBy time words) (names : NamesAccounted implementation.program.code slots)
    (value : input.Value) :
    Subtype.val <$> (Stage.compute (port := port) implementation bound names).source value = pure (f value.val) := by
  simp [Stage.compute]

end Signatures.Runtime.CaliperBackend.Preparation

/-! ## Permuting the keyed challenge's key pairs -/
namespace Signatures.Runtime.CaliperBackend.KeyedSetup
open Caliper BoundedSource

variable {w : Nat} {F C K : Type} (layout : Layouts w F C K)

/-- Storage bounds over the keyed layouts, by expanding to the base layouts. -/
theorem fitsBase {n : Nat} (bound : n ≤ 16 * layout.width) : n < 2 ^ w := layout.fits bound
theorem keys_words : layout.keys.representation.encoding.words = 2 * layout.key.representation.encoding.words := by
  change layout.key.representation.encoding.words + layout.key.representation.encoding.words = _; omega
theorem keyed_words : layout.keyed.representation.encoding.words = 2 * layout.key.representation.encoding.words + layout.scalar.representation.encoding.words := by
  change layout.keys.representation.encoding.words + layout.scalar.representation.encoding.words = _; rw [keys_words]
theorem keyeds_words : layout.keyeds.representation.encoding.words = 2 * layout.keyed.representation.encoding.words := by
  change layout.keyed.representation.encoding.words + layout.keyed.representation.encoding.words = _; omega
theorem output_words : layout.output.representation.encoding.words = layout.config.representation.encoding.words + layout.keyeds.representation.encoding.words := rfl

/-- The wrapped key with its two public keys swapped. -/
def swapKeyed : Implementation .unit layout.keyed layout.keyed (fun value => ((value.1.2, value.1.1), value.2)) :=
  ((Implementation.first (cost := .unit) (by decide) layout.keys layout.scalar layout.wordFits layout.keyed.representation.fits).then
      (Implementation.swap layout.key layout.key layout.wordFits layout.keys.representation.fits)).pair'
    (Implementation.second (cost := .unit) (by decide) layout.keys layout.scalar layout.wordFits layout.keyed.representation.fits) layout.wordFits
    (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (Implementation.swap_buffers _ _ _ _))
    (Implementation.second_buffers _ _ _ _ _) (by have := layout.wordFits; omega)
    (fitsBase layout (by
      show (layout.keys.representation.encoding.words + layout.scalar.representation.encoding.words) +
        (layout.keys.representation.encoding.words + layout.scalar.representation.encoding.words) +
        (layout.key.representation.encoding.words + layout.key.representation.encoding.words) + layout.scalar.representation.encoding.words ≤ _
      rw [keys_words]; unfold Layouts.width; omega))
theorem swapKeyed_buffers : (swapKeyed layout).program.code.memBound ≤ 4 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
def swapKeyeds : Implementation .unit layout.keyeds layout.keyeds
    (fun value => (((value.1.1.2, value.1.1.1), value.1.2), ((value.2.1.2, value.2.1.1), value.2.2))) :=
  ((Implementation.first (cost := .unit) (by decide) layout.keyed layout.keyed layout.wordFits layout.keyeds.representation.fits).then (swapKeyed layout)).pair'
    ((Implementation.second (cost := .unit) (by decide) layout.keyed layout.keyed layout.wordFits layout.keyeds.representation.fits).then (swapKeyed layout)) layout.wordFits
    (Implementation.then_buffers _ _ (Implementation.first_buffers _ _ _ _ _) (swapKeyed_buffers layout))
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (swapKeyed_buffers layout))
    (by have := layout.wordFits; omega) (fitsBase layout (by
      show (layout.keyed.representation.encoding.words + layout.keyed.representation.encoding.words) +
        (layout.keyed.representation.encoding.words + layout.keyed.representation.encoding.words) +
        layout.keyed.representation.encoding.words + layout.keyed.representation.encoding.words ≤ _
      rw [keyed_words]; unfold Layouts.width; omega))
theorem swapKeyeds_buffers : (swapKeyeds layout).program.code.memBound ≤ 5 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
/-- The key pairs of both slots of the keyed challenge swapped. -/
def swapValue (value : C × (((K × K) × F) × ((K × K) × F))) : C × (((K × K) × F) × ((K × K) × F)) :=
  (value.1, (((value.2.1.1.2, value.2.1.1.1), value.2.1.2), ((value.2.2.1.2, value.2.2.1.1), value.2.2.2)))
def swapOutput : Implementation .unit layout.output layout.output swapValue :=
  (Implementation.first (cost := .unit) (by decide) layout.config layout.keyeds layout.wordFits layout.output.representation.fits).pair'
    ((Implementation.second (cost := .unit) (by decide) layout.config layout.keyeds layout.wordFits layout.output.representation.fits).then (swapKeyeds layout)) layout.wordFits
    (Implementation.first_buffers _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.second_buffers _ _ _ _ _) (swapKeyeds_buffers layout))
    (by have := layout.wordFits; omega) (fitsBase layout (by
      show (layout.config.representation.encoding.words + layout.keyeds.representation.encoding.words) +
        (layout.config.representation.encoding.words + layout.keyeds.representation.encoding.words) +
        layout.config.representation.encoding.words + layout.keyeds.representation.encoding.words ≤ _
      rw [keyeds_words, keyed_words]; unfold Layouts.width; omega))

theorem swapKeyed_boundedBy : (swapKeyed layout).BoundedBy (300 * layout.width) (900 * layout.width + 400) := by
  unfold swapKeyed
  have := layout.sizes
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((Implementation.first_boundedBy' _ _ this.2.2.2.1).then
    (Implementation.swap_boundedBy' _ _ this.2.2.1 this.2.2.1)) (Implementation.second_boundedBy' _ _ this.1)
    this.2.2.2.2.2.2.1 this.2.2.2.1 this.1).mono ?_ ?_ <;> omega
theorem swapKeyeds_boundedBy : (swapKeyeds layout).BoundedBy (1500 * layout.width) (4500 * layout.width + 2000) := by
  unfold swapKeyeds
  have := layout.sizes
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((Implementation.first_boundedBy' _ _ this.2.2.2.2.2.2.1).then (swapKeyed_boundedBy layout))
    ((Implementation.second_boundedBy' _ _ this.2.2.2.2.2.2.1).then (swapKeyed_boundedBy layout))
    this.2.2.2.2.2.2.2.1 this.2.2.2.2.2.2.1 this.2.2.2.2.2.2.1).mono ?_ ?_ <;> omega
theorem swapOutput_boundedBy : (swapOutput layout).BoundedBy (2500 * layout.width) (7500 * layout.width + 3000) := by
  unfold swapOutput
  have := layout.sizes
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.first_boundedBy' _ _ this.2.1)
    ((Implementation.second_boundedBy' _ _ this.2.2.2.2.2.2.2.1).then (swapKeyeds_boundedBy layout))
    this.2.2.2.2.2.2.2.2 this.2.1 this.2.2.2.2.2.2.2.1).mono ?_ ?_ <;> omega
theorem swapKeyed_names (slots : Nat) : NamesAccounted (swapKeyed layout).program.code slots :=
  Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.first_names _ _ _ _ _).seq (Implementation.swap_names _ _ _ _ _)) (Implementation.second_names _ _ _ _ _)
theorem swapKeyeds_names (slots : Nat) : NamesAccounted (swapKeyeds layout).program.code slots :=
  Implementation.pair'_names _ _ _ _ _ _ _ ((Implementation.first_names _ _ _ _ _).seq (swapKeyed_names layout slots))
    ((Implementation.second_names _ _ _ _ _).seq (swapKeyed_names layout slots))
theorem swapOutput_names (slots : Nat) : NamesAccounted (swapOutput layout).program.code slots :=
  Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _) ((Implementation.second_names _ _ _ _ _).seq (swapKeyeds_names layout slots))

variable (port : Interactive.Port w unifSpec)
/-- The swap as a preparation stage. -/
def swapStage : Preparation.Stage port layout.output layout.output :=
  Preparation.Stage.compute (swapOutput layout) (swapOutput_boundedBy layout) (swapOutput_names layout 0)
/-- Leaving the keyed challenge as it is. -/
def keepStage : Preparation.Stage port layout.output layout.output :=
  Preparation.Stage.compute (Implementation.identity layout.output (width_pos layout.wordFits)) (Implementation.identity_boundedBy _ _)
    (Implementation.identity_names _ 0)
theorem swapStage_source (value : layout.output.Value) : Subtype.val <$> (swapStage layout port).source value = pure (swapValue value.val) :=
  Preparation.Stage.compute_source _ _ _ value
theorem keepStage_source (value : layout.output.Value) : Subtype.val <$> (keepStage layout port).source value = pure value.val := by
  unfold keepStage; exact Preparation.Stage.compute_source _ _ _ value

end Signatures.Runtime.CaliperBackend.KeyedSetup

namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM Preparation

section Good
variable {w : Nat} {G M A J K₀ : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [DecidableEq J] [Field (val.Value base)] [SampleableType (val.Value base)]
    [AddCommGroup G] [Module (val.Value base) G] [AddCommGroup K₀] [Module (val.Value base) K₀]
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G (val.Value base) (val.Value base) (G × G) A)
    (setup : WeightedSetup.Layouts layout.service ((K₀ × K₀) × val.Value base)) (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout setup.key.representation) (fuel : Nat)
    (source : ProbComp layout.service.evaluation.cache.value.Value)
    (coefficientLaw : routines.coefficientDefault.val = 0)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (respondLaw : routines.respond = fun signing value => value.1 • (if signing then value.2.2 else value.2.1))
    (calculateLaw : routines.calculate = fun value => value.1 / (value.2.1 - value.2.2))
    (numeratorLaw : routines.numerator = fun value => value.1 + value.2)
    (invariant : Invariant layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)
    (keys : J ≃ key.Value base) (terms : M → List (J × val.Value base))
    (termsEqual : ∀ message, routines.generate message = (terms message).map (Prod.map keys id))
    (witness : Correspondence layout setup caller fuel invariant keys)
    (adversary : Adversary (val.Value base) J M G ((K₀ × K₀) × val.Value base))
    (same : ∀ pk : setup.key.Value,
      (fun answer => WeightedCallerProgram.output answer.val) <$> witness.source pk.val = adversary.main pk.val)
    (bound : Routines.Bounds layout routines) (localBound : Caller.Bounds layout setup caller)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    {drawTime drawWords drawSlots : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (drawReserve : drawSlots + 5 < 2 ^ w)
    (handlerReserve : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words) + 1 < 2 ^ w)
    (generator : G) (keyGenerator : K₀)

/-! ## The known-key draw -/
variable (keyed : KeyedSetup.Layouts w (val.Value base) (G × G) K₀) (compatible : keyed.output = setup.challenge)
    (scale : Implementation .unit keyed.arguments keyed.key (fun value => value.1 • value.2))
    {scaleSlots : Nat} (scaleBuffers : scale.program.code.memBound ≤ scaleSlots) (scaleReserve : scaleSlots + 5 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)
    {scaleNameSlots : Nat} (scaleNames : NamesAccounted scale.program.code scaleNameSlots)
    (keyDraw : Interactive.Code w) (keySource : ProbComp keyed.scalar.Value)
    (keyCorrect : Interactive.Refines layout.port .unit keyed.unit.representation keyed.scalar.representation (fun _ => keySource) keyDraw)
    {keyTime keyWords keySlots : Nat}
    (keyTimeBound : Interactive.TimeBound layout.port .unit keyed.unit.representation keyDraw keyTime)
    (keyWordsBound : (keyDraw.lower layout.port).descriptionWords ≤ keyWords)
    (keyNames : WordIO.NamesBound (keyDraw.lower layout.port) keySlots)
    (keyFits : (keyDraw.lower layout.port).DescriptionFits) (keyReserve : keySlots < 2 ^ w)
    (challengeValid : ∀ scalar : val.Value base,
      keyed.challenge.valid ((generator, scalar • generator), (keyGenerator, scalar • keyGenerator)))
    -- a rearrangement of the keyed challenge, e.g. swapping the key pairs
    (post : Stage layout.port setup.challenge setup.challenge)
    (postFn : (G × G) × (((K₀ × K₀) × val.Value base) × ((K₀ × K₀) × val.Value base)) →
      (G × G) × (((K₀ × K₀) × val.Value base) × ((K₀ × K₀) × val.Value base)))
    (postLaw : ∀ value, Subtype.val <$> post.source value = pure (postFn value.val))

/-- The keyed challenge for the known key `k`: `((pk, k • g₂), k)` in both key slots, rearranged. -/
def keyedStage : Stage layout.port keyed.challenge setup.challenge :=
  ((KeyedSetup.stage keyed scale scaleBuffers scaleReserve scaleBound scaleNames layout.port keyDraw keySource keyCorrect keyTimeBound
    keyWordsBound keyNames keyFits keyReserve).cast compatible).seq layout.service.evaluation.cache.wordFits post

include coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw numeratorLaw cacheRoom hashRoom signRoom termsEqual same
    correct drawCorrect drawTimeBound drawWordsBound drawNames drawFits drawReserve handlerReserve challengeValid
    compatible scale scaleBuffers scaleReserve scaleBound scaleNames keyDraw keyCorrect keyTimeBound keyWordsBound keyNames keyFits keyReserve postLaw in
/-- **The keyed good solver.** Drawing the known key, then running the complete good program on
the keyed challenge, is the good weighted list reduction on the keyed adversary with the known
key from the certified scalar source. -/
theorem keyed_good_dlogWithin : dlogWithin layout.port keyed.challenge layout.extraction.scalar generator keyGenerator
    (KeyedSetup.codeBudget keyed keyWords scaleWords + post.words + 1 + codeBudget layout setup routines caller bound localBound true drawWords fuel + 1)
    (5 * (KeyedSetup.codeBudget keyed keyWords scaleWords + post.words + 1 + codeBudget layout setup routines caller bound localBound true drawWords fuel + 1) +
      4 * max (max (max (max 3 keySlots) scaleNameSlots) post.slots) (nameBudget layout setup routines caller localBound drawSlots) + 3 +
      keyed.challenge.representation.encoding.words +
      (KeyedSetup.timeBudget keyed keyTime scaleTime + post.time + timeBudget layout setup routines caller bound localBound true drawTime fuel))
    (KeyedSetup.timeBudget keyed keyTime scaleTime + post.time + timeBudget layout setup routines caller bound localBound true drawTime fuel)
    (fun g X g₂ Z₂ => keySource >>= fun scalar =>
      let keyedValue := postFn ((g, X), (((Z₂, scalar.val • g₂), scalar.val), ((Z₂, scalar.val • g₂), scalar.val)))
      WeightedReduction.goodReductionList terms adversary keyedValue.1.1 keyedValue.1.2 keyedValue.2.1 keyedValue.2.2) := by
  refine ⟨challengeValid, ?_⟩
  have within := stage_within layout setup routines caller bound localBound P comparison correct draw fuel true source drawCorrect drawTimeBound
    drawWordsBound drawNames invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform drawFits drawReserve handlerReserve
    (keyedStage layout setup keyed compatible scale scaleBuffers scaleReserve scaleBound scaleNames keyDraw keySource keyCorrect
      keyTimeBound keyWordsBound keyNames keyFits keyReserve post)
  simp only [keyedStage, Stage.seq, Stage.cast_words, Stage.cast_time, Stage.cast_slots, KeyedSetup.stage] at within
  refine within.congr ?_
  intro value
  simp only [Stage.cast_source, KeyedSetup.denote, map_bind, bind_assoc, Functor.map_map, bind_map_left]
  refine bind_congr fun scalar => ?_
  have inner : ∀ s : setup.challenge.Value, Subtype.val <$> denote layout setup routines P comparison correct caller fuel true source s =
      WeightedReduction.goodReductionList terms adversary s.val.1.1 s.val.1.2 s.val.2.1 s.val.2.2 :=
    good_source layout setup routines P comparison correct caller fuel source coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw
      numeratorLaw invariant cacheRoom hashRoom signRoom keys terms termsEqual witness adversary same
  simp only [inner]
  trans ((Subtype.val <$> post.source (compatible ▸ KeyedSetup.result keyed scale scaleBuffers scaleReserve (KeyedSetup.sampledValue keyed value scalar)
      : setup.challenge.Value)) >>= fun v => WeightedReduction.goodReductionList terms adversary v.1.1 v.1.2 v.2.1 v.2.2)
  · rw [bind_map_left]
  rw [postLaw, pure_bind, Preparation.cast_val]
  rfl

end Good

/-! ## The bad branch: resample the public key, then draw the known key -/
section Bad
variable {w : Nat} {G M A J K₀ : Type} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom}
    [DecidableEq (key.Value base)] [DecidableEq J] [Field (scalar.Value base)] [SampleableType (scalar.Value base)]
    [AddCommGroup G] [Module (scalar.Value base) G] [AddCommGroup K₀] [Module (scalar.Value base) K₀]
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G (scalar.Value base)
      ((Ty.pair scalar scalar).Value base) (scalar.Value base × (G × G)) A)
    (setup : WeightedSetup.Layouts layout.service ((K₀ × K₀) × scalar.Value base))
    (routines : Routines (base := base) (key := key) (val := .pair scalar scalar) layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller (base := base) (key := key) (val := .pair scalar scalar) layout setup.key.representation) (fuel : Nat)
    (source : ProbComp layout.service.evaluation.cache.value.Value)
    (coefficientLaw : routines.coefficientDefault.val = 0)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ ((Ty.pair scalar scalar).Value base) : ProbComp _))
    (respondLaw : routines.respond = fun signing value =>
      if signing then value.2.1 • (value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
      else value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
    (calculateLaw : routines.calculate = fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1))
    (invariant : Invariant (base := base) (key := key) (val := .pair scalar scalar) layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)
    (keys : J ≃ key.Value base) (terms : M → List (J × scalar.Value base))
    (termsEqual : ∀ message, routines.generate message = (terms message).map (Prod.map keys id))
    (witness : Correspondence (base := base) (key := key) (val := .pair scalar scalar) layout setup caller fuel invariant keys)
    (adversary : Adversary (scalar.Value base) J M G ((K₀ × K₀) × scalar.Value base))
    (same : ∀ pk : setup.key.Value,
      (fun answer => WeightedCallerProgram.output answer.val) <$> witness.source pk.val = adversary.main pk.val)
    (bound : Routines.Bounds (base := base) (key := key) (val := .pair scalar scalar) layout routines)
    (localBound : Caller.Bounds (base := base) (key := key) (val := .pair scalar scalar) layout setup caller)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    {drawTime drawWords drawSlots : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (drawReserve : drawSlots + 5 < 2 ^ w)
    (handlerReserve : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words) + 1 < 2 ^ w)
    (generator : G) (keyGenerator : K₀)
    -- the public-key resampling
    (preparation : WeightedBadSetup.Layouts w (scalar.Value base) G K₀)
    (resample : Implementation .unit preparation.arguments preparation.key (fun value => value.1 • value.2))
    {resampleSlots : Nat} (resampleBuffers : resample.program.code.memBound ≤ resampleSlots) (resampleReserve : resampleSlots + 5 < 2 ^ w)
    {resampleTime resampleWords : Nat} (resampleBound : resample.BoundedBy resampleTime resampleWords)
    {resampleNameSlots : Nat} (resampleNames : NamesAccounted resample.program.code resampleNameSlots)
    (outerDraw : Interactive.Code w) (outerSource : ProbComp preparation.scalar.Value)
    (outerCorrect : Interactive.Refines layout.port .unit preparation.unit.representation preparation.scalar.representation (fun _ => outerSource) outerDraw)
    {outerTime outerWords outerSlots : Nat}
    (outerTimeBound : Interactive.TimeBound layout.port .unit preparation.unit.representation outerDraw outerTime)
    (outerWordsBound : (outerDraw.lower layout.port).descriptionWords ≤ outerWords)
    (outerNames : WordIO.NamesBound (outerDraw.lower layout.port) outerSlots)
    (outerFits : (outerDraw.lower layout.port).DescriptionFits) (outerReserve : outerSlots < 2 ^ w)
    -- the known-key draw over the resampled challenge
    (keyed : KeyedSetup.Layouts w (scalar.Value base) (scalar.Value base × (G × G)) K₀)
    (prepared : preparation.output = keyed.challenge) (compatible : keyed.output = setup.challenge)
    (scale : Implementation .unit keyed.arguments keyed.key (fun value => value.1 • value.2))
    {scaleSlots : Nat} (scaleBuffers : scale.program.code.memBound ≤ scaleSlots) (scaleReserve : scaleSlots + 5 < 2 ^ w)
    {scaleTime scaleWords : Nat} (scaleBound : scale.BoundedBy scaleTime scaleWords)
    {scaleNameSlots : Nat} (scaleNames : NamesAccounted scale.program.code scaleNameSlots)
    (keyDraw : Interactive.Code w) (keySource : ProbComp keyed.scalar.Value)
    (keyCorrect : Interactive.Refines layout.port .unit keyed.unit.representation keyed.scalar.representation (fun _ => keySource) keyDraw)
    {keyTime keyWords keySlots : Nat}
    (keyTimeBound : Interactive.TimeBound layout.port .unit keyed.unit.representation keyDraw keyTime)
    (keyWordsBound : (keyDraw.lower layout.port).descriptionWords ≤ keyWords)
    (keyNames : WordIO.NamesBound (keyDraw.lower layout.port) keySlots)
    (keyFits : (keyDraw.lower layout.port).DescriptionFits) (keyReserve : keySlots < 2 ^ w)
    (challengeValid : ∀ scalar : scalar.Value base,
      preparation.challenge.valid ((generator, scalar • generator), (keyGenerator, scalar • keyGenerator)))
    (post : Stage layout.port setup.challenge setup.challenge)
    (postFn : (scalar.Value base × (G × G)) × (((K₀ × K₀) × scalar.Value base) × ((K₀ × K₀) × scalar.Value base)) →
      (scalar.Value base × (G × G)) × (((K₀ × K₀) × scalar.Value base) × ((K₀ × K₀) × scalar.Value base)))
    (postLaw : ∀ value, Subtype.val <$> post.source value = pure (postFn value.val))

/-- Resample the public key, then draw the known key, then rearrange. -/
def badKeyedStage : Stage layout.port preparation.challenge setup.challenge :=
  (((WeightedBadSetup.stage preparation resample resampleBuffers resampleReserve resampleBound resampleNames layout.port outerDraw outerSource
    outerCorrect outerTimeBound outerWordsBound outerNames outerFits outerReserve).cast prepared).seq layout.service.evaluation.cache.wordFits
    ((KeyedSetup.stage keyed scale scaleBuffers scaleReserve scaleBound scaleNames layout.port keyDraw keySource keyCorrect keyTimeBound
      keyWordsBound keyNames keyFits keyReserve).cast compatible)).seq layout.service.evaluation.cache.wordFits post

include coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw cacheRoom hashRoom signRoom termsEqual same
    correct drawCorrect drawTimeBound drawWordsBound drawNames drawFits drawReserve handlerReserve challengeValid
    resample resampleBuffers resampleReserve resampleBound resampleNames outerDraw outerCorrect outerTimeBound outerWordsBound outerNames outerFits outerReserve
    prepared compatible scale scaleBuffers scaleReserve scaleBound scaleNames keyDraw keyCorrect keyTimeBound keyWordsBound keyNames keyFits keyReserve
    postLaw in
/-- **The keyed bad solver.** Resampling the public key and drawing the known key, then
running the complete bad program on the keyed challenge, is the fixed bad program on the keyed
adversary with both scalars from their certified sources. -/
theorem keyed_bad_dlogWithin : dlogWithin layout.port preparation.challenge layout.extraction.scalar generator keyGenerator
    (WeightedBadSetup.codeBudget preparation outerWords resampleWords + KeyedSetup.codeBudget keyed keyWords scaleWords + 1 + post.words + 1 +
      codeBudget layout setup routines caller bound localBound false drawWords fuel + 1)
    (5 * (WeightedBadSetup.codeBudget preparation outerWords resampleWords + KeyedSetup.codeBudget keyed keyWords scaleWords + 1 + post.words + 1 +
        codeBudget layout setup routines caller bound localBound false drawWords fuel + 1) +
      4 * max (max (max (max (max 3 outerSlots) resampleNameSlots) (max (max 3 keySlots) scaleNameSlots)) post.slots)
        (nameBudget layout setup routines caller localBound drawSlots) + 3 +
      preparation.challenge.representation.encoding.words +
      (WeightedBadSetup.timeBudget preparation outerTime resampleTime + KeyedSetup.timeBudget keyed keyTime scaleTime + post.time +
        timeBudget layout setup routines caller bound localBound false drawTime fuel))
    (WeightedBadSetup.timeBudget preparation outerTime resampleTime + KeyedSetup.timeBudget keyed keyTime scaleTime + post.time +
      timeBudget layout setup routines caller bound localBound false drawTime fuel)
    (fun g X g₂ _ => outerSource >>= fun kappa => keySource >>= fun scalar =>
      let keyedValue := postFn ((kappa.val, (g, X)), (((kappa.val • g₂, scalar.val • g₂), scalar.val), ((kappa.val • g₂, scalar.val • g₂), scalar.val)))
      (simulateQ BLS.LazyAGM.Reduction.privateListOracle
        (WeightedReduction.badProgram terms keyedValue.1.2.1 keyedValue.1.2.2 keyedValue.2.2 keyedValue.1.1 adversary)).run' []) := by
  refine ⟨challengeValid, ?_⟩
  have within := stage_within layout setup routines caller bound localBound P comparison correct draw fuel false source drawCorrect drawTimeBound
    drawWordsBound drawNames invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform drawFits drawReserve handlerReserve
    (badKeyedStage layout setup preparation resample resampleBuffers resampleReserve resampleBound resampleNames outerDraw outerSource outerCorrect
      outerTimeBound outerWordsBound outerNames outerFits outerReserve keyed prepared compatible scale scaleBuffers scaleReserve scaleBound scaleNames
      keyDraw keySource keyCorrect keyTimeBound keyWordsBound keyNames keyFits keyReserve post)
  simp only [badKeyedStage, Stage.seq, Stage.cast_words, Stage.cast_time, Stage.cast_slots, WeightedBadSetup.stage, KeyedSetup.stage] at within
  refine within.congr ?_
  intro value
  simp only [Stage.cast_source, WeightedBadSetup.denote, KeyedSetup.denote, map_bind, bind_assoc, Functor.map_map, bind_map_left]
  refine bind_congr fun kappa => ?_
  refine bind_congr fun scalar => ?_
  have inner : ∀ s : setup.challenge.Value, Subtype.val <$> denote layout setup routines P comparison correct caller fuel false source s =
      (simulateQ BLS.LazyAGM.Reduction.privateListOracle
        (WeightedReduction.badProgram terms s.val.1.2.1 s.val.1.2.2 s.val.2.2 s.val.1.1 adversary)).run' [] :=
    bad_fixed_source layout setup routines P comparison correct caller fuel source coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw
      invariant cacheRoom hashRoom signRoom keys terms termsEqual witness adversary same
  simp only [inner]
  trans ((Subtype.val <$> post.source (compatible ▸ KeyedSetup.result keyed scale scaleBuffers scaleReserve (KeyedSetup.sampledValue keyed
      (prepared ▸ WeightedBadSetup.result preparation resample resampleBuffers resampleReserve (WeightedBadSetup.sampledValue preparation value kappa)
        : keyed.challenge.Value) scalar) : setup.challenge.Value)) >>= fun v => (simulateQ BLS.LazyAGM.Reduction.privateListOracle
    (WeightedReduction.badProgram terms v.1.2.1 v.1.2.2 v.2.2 v.1.1 adversary)).run' [])
  · rw [bind_map_left]
  rw [postLaw, pure_bind, Preparation.cast_val]
  simp only [KeyedSetup.result, KeyedSetup.sampledValue, Preparation.cast_val, WeightedBadSetup.result, WeightedBadSetup.sampledValue]
  rfl
end Bad

end Signatures.Runtime.CaliperBackend.WeightedFull

import Proofs.Runtime.Caliper.CoronTerminal

/-! Complete time, stored-code and memory bounds for the terminal cache read
and extraction, derived from scalar sampling and group implementations. -/
namespace Signatures.Runtime.CaliperBackend.CoronTerminal
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    [DecidableEq M] [SampleableType F] [SMul F G] [Sub G]
    (layout : CoronService.Layouts w M F G randomBound qS)
    (sampler : CoronService.Sampler layout) (arithmetic : Arithmetic layout)

def timeBudget : Nat :=
  CoronCache.timeBudget layout.cache randomBound layout.randomFits qS layout.pairFits sampler.time +
    arithmetic.scaleTime + arithmetic.subTime + 292 * width layout
def codeBudget : Nat :=
  CoronCache.codeBudget layout.cache randomBound layout.randomFits qS layout.pairFits sampler.words +
    arithmetic.scaleWords + arithmetic.subWords + 949 * width layout + 395
def nameBudget : Nat := max (max 5 sampler.slots) arithmetic.slots
def memoryBudget : Nat :=
  5 * codeBudget layout sampler arithmetic + 4 * nameBudget layout sampler arithmetic + 3 +
    (input layout).representation.encoding.words + timeBudget layout sampler arithmetic

theorem time_bound : Interactive.TimeBound layout.port .unit (input layout).representation
    (code layout sampler arithmetic) (timeBudget layout sampler arithmetic) := by
  have read := CoronCache.time_bound layout.cache randomBound layout.randomFits qS layout.pairFits sampler.correct sampler.timeBound
  have retained := read.retain (read_refines layout sampler) (by decide) layout.response.points.representation
    layout.cache.wordFits (input layout).representation.fits
  have viewed := retained.viewInput (input layout).representation
    (productView layout.service.cache.input layout.response.points) (fun _ => rfl)
  have retainedBound : Interactive.TimeBound layout.port .unit (input layout).representation (retainedCode layout sampler)
      (CoronCache.timeBudget layout.cache randomBound layout.randomFits qS layout.pairFits sampler.time + 28 * width layout) := by
    apply viewed.mono
    apply (Interactive.retain_time_unit_le _ _ _ _ _).trans
    have := inputSize layout
    have := base_sizes layout
    omega
  have extracted := extract_bounded layout arithmetic.scale arithmetic.scaleBound arithmetic.scaleNames.buffers arithmetic.reserve
    arithmetic.sub arithmetic.subBound
  apply (retainedBound.seq (retained_refines layout sampler)
    (Interactive.TimeBound.compute (port := layout.port) (cost := .unit)
      (extract layout arithmetic.scale arithmetic.scaleNames.buffers arithmetic.reserve arithmetic.sub).program _ extracted.time_le)).mono
  unfold timeBudget
  omega

theorem code_words : ((code layout sampler arithmetic).lower layout.port).descriptionWords ≤
    codeBudget layout sampler arithmetic := by
  have read := CoronCache.code_words layout.cache randomBound layout.randomFits qS layout.pairFits sampler.codeBound
  have retained := Interactive.retain_descriptionWords_le layout.port (readCode layout sampler)
    (Interactive.savedBuffer layout.port (readCode layout sampler)) layout.service.cache.input.representation.encoding.words
    (CacheRead.output layout.service.cache).representation.encoding.words layout.response.points.representation.encoding.words
  change ((retainedCode layout sampler).lower layout.port).descriptionWords ≤ _ at retained
  change ((readCode layout sampler).lower layout.port).descriptionWords ≤ _ at read
  have extracted := (extract_bounded layout arithmetic.scale arithmetic.scaleBound arithmetic.scaleNames.buffers arithmetic.reserve
    arithmetic.sub arithmetic.subBound).code_le
  have := inputSize layout
  have := base_sizes layout
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names : WordIO.NamesAccounted ((code layout sampler arithmetic).lower layout.port)
    (nameBudget layout sampler arithmetic) := by
  have read := (CoronCache.names layout.cache randomBound layout.randomFits qS layout.pairFits sampler.names).mono
    (Nat.le_max_left (max 5 sampler.slots) arithmetic.slots)
  have retained := Interactive.retain_names layout.port read layout.service.cache.input.representation.encoding.words
    (CacheRead.output layout.service.cache).representation.encoding.words layout.response.points.representation.encoding.words
  exact retained.seq (.compute (extract_names layout (nameBudget layout sampler arithmetic) arithmetic.scale
    arithmetic.scaleNames.buffers arithmetic.reserve arithmetic.sub
    (arithmetic.scaleNames.accounted.mono (Nat.le_max_right _ _))
    (arithmetic.subNames.accounted.mono (Nat.le_max_right _ _))))

theorem descriptionFits : ((code layout sampler arithmetic).lower layout.port).DescriptionFits := by
  have readFits := CoronCache.descriptionFits layout.cache randomBound layout.randomFits qS layout.pairFits sampler.descriptionFits
    sampler.names (by have := sampler.reserve; omega)
  have savedFits : Interactive.savedBuffer layout.port (readCode layout sampler) < 2 ^ w := by
    have read := EncodedCacheRead.buffers (base := cryptoBase F Unit Unit M M) (key := message) (val := CoronCache.valueTy qS.val)
      layout.service.cache (CoronCache.primitives F M) CoronCache.comparison (CoronCache.comparison_correct F M)
      layout.port (sampler.pairCode layout)
    change ((readCode layout sampler).lower layout.port).memBound ≤ _ at read
    have := (sampler.pair_names layout).buffers
    have := sampler.reserve
    have := layout.cache.wordFits
    unfold Interactive.savedBuffer
    omega
  have retained := Interactive.retain_descriptionFits layout.port (readCode layout sampler)
    (Interactive.savedBuffer layout.port (readCode layout sampler)) layout.service.cache.input.representation.encoding.words
    (CacheRead.output layout.service.cache).representation.encoding.words layout.response.points.representation.encoding.words
    layout.cache.wordFits readFits savedFits layout.service.cache.input.representation.fits layout.response.points.representation.fits
    (returned layout).representation.fits
  exact .seq layout.cache.wordFits retained
    (.compute (extract layout arithmetic.scale arithmetic.scaleNames.buffers arithmetic.reserve arithmetic.sub).program.description_fits)

/-- The sole source query is the lazy paired read: a hit uses no randomness,
while a miss samples both scalar and coin. The result is the extracted point. -/
theorem within : Interactive.Within layout.port (input layout) layout.point
    (codeBudget layout sampler arithmetic) (memoryBudget layout sampler arithmetic) (timeBudget layout sampler arithmetic)
    (fun value => (fun result => value.val.2.1 - result.1.1 • value.val.2.2) <$>
      ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
        (.inr value.val.1.1)).run value.val.1.2.2.1) :=
  (Interactive.within_of_refines_accounted (refines layout sampler arithmetic) (time_bound layout sampler arithmetic)
    (code_words layout sampler arithmetic) (names layout sampler arithmetic) (descriptionFits layout sampler arithmetic)).congr
    (source_eq layout sampler arithmetic)

end Signatures.Runtime.CaliperBackend.CoronTerminal

namespace Signatures.Runtime.CaliperBackend.CoronTerminal
open BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G : Type}
    [DecidableEq M] [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    (layout : CoronService.Layouts w M F G randomBound qS)
    (sampler : CoronService.Sampler layout) (arithmetic : Arithmetic layout)

/-- The resource witness implements the same terminal computation that
`Coron.Paired.reduction_finish` factors out of the original co-CDH reduction. -/
theorem within_finish : Interactive.Within layout.port (input layout) layout.point
    (codeBudget layout sampler arithmetic) (memoryBudget layout sampler arithmetic) (timeBudget layout sampler arithmetic)
    (fun value => Coron.Paired.finish value.val.2.2 (value.val.1.1, value.val.2.1) value.val.1.2.2.1) :=
  within layout sampler arithmetic

end Signatures.Runtime.CaliperBackend.CoronTerminal

import Proofs.Runtime.Caliper.CoronSampling
import Proofs.Runtime.Caliper.BLSCache
import Proofs.Runtime.Caliper.CacheReadMemory
import Proofs.Runtime.Arithmetic

/-! An actual Caliper cache for Coron's scalar/coin entries. Only the scalar
sampler is supplied: the independent coin draw, lazy lookup, insertion, retained
frames, and complete time/code/memory bounds are constructed. Paired source
semantics is related to the original co-CDH reduction in CoronPairedCache. -/
namespace Signatures.Runtime.CaliperBackend.BoundedSource.CacheLayout
variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

theorem coinValueFits : layout.value.representation.encoding.words + 1 < 2 ^ w :=
  layout.lookup.fits_of_le (by dsimp [LookupLayout.width, lookup]; omega)

def coinStorageWords : Nat :=
  8 * (1 + (layout.capacityPred + 1) * (layout.key.representation.encoding.words +
    (layout.value.representation.encoding.words + 1)) +
      layout.key.representation.encoding.words + (layout.value.representation.encoding.words + 1))

def coinValues (bound : Nat) (fits : bound + 1 ≤ 2 ^ w) (qS : Fin (bound + 1))
    (storageFits : layout.coinStorageWords < 2 ^ w) : CacheLayout w K (V × Fin (qS.val + 1)) where
  key := layout.key
  value := CoronSampling.output layout.value bound layout.wordFits fits qS layout.coinValueFits
  capacityPred := layout.capacityPred
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := storageFits

end Signatures.Runtime.CaliperBackend.BoundedSource.CacheLayout

namespace Signatures.Runtime.CaliperBackend.CoronCache
open Caliper BoundedSource OracleComp OracleSpec

inductive Comparison : Ty CryptoAtom → Ty CryptoAtom → Type
  | equal : Comparison (.pair message message) .bool

def primitives (F M : Type) [DecidableEq M] : Primitives (cryptoBase F Unit Unit M M) Comparison where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
def comparison : Expr Comparison [message, message] .bool :=
  .op .equal (.pair (.var .here) (.var (.there .here)))
theorem comparison_correct (F M : Type) [DecidableEq M] (left right : M) :
    comparison.denote (primitives F M) (left, right, ()) = decide (left = right) := rfl

abbrev valueTy (qS : Nat) : Ty CryptoAtom := .pair scalar (boundedNat qS)

variable {w : Nat} {F M : Type} [DecidableEq M] (layout : CacheLayout w M F)
    (bound : Nat) (fits : bound + 1 ≤ 2 ^ w) (qS : Fin (bound + 1))
    (storageFits : layout.coinStorageWords < 2 ^ w)

def code (scalarDraw : Interactive.Code w) : Interactive.Code w :=
  EncodedCacheRead.code (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M)
    (UniformQuery.port bound layout.wordFits fits)
    (CoronSampling.code layout.value bound layout.wordFits fits qS layout.coinValueFits scalarDraw)

def source (scalarSource : ProbComp layout.value.Value)
    (input : (layout.coinValues bound fits qS storageFits).input.Value) :
    ProbComp (CacheRead.output (layout.coinValues bound fits qS storageFits)).Value :=
  EncodedCacheRead.denote (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M)
    (CoronSampling.source layout.value bound layout.wordFits fits qS layout.coinValueFits scalarSource) input

def timeBudget (scalarTime : Nat) : Nat :=
  EncodedCacheRead.timeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (CoronSampling.timeBudget layout.value scalarTime)

def codeBudget (scalarWords : Nat) : Nat :=
  EncodedCacheRead.codeBudget (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (CoronSampling.codeBudget layout.value scalarWords)

def memoryBudget (scalarTime scalarWords scalarSlots : Nat) : Nat :=
  5 * codeBudget layout bound fits qS storageFits scalarWords + 4 * max 5 scalarSlots + 3 +
    (layout.coinValues bound fits qS storageFits).input.representation.encoding.words +
      timeBudget layout bound fits qS storageFits scalarTime

variable {scalarDraw : Interactive.Code w} {scalarSource : ProbComp layout.value.Value}
    (scalarCorrect : Interactive.Refines (UniformQuery.port bound layout.wordFits fits) .unit
      layout.lookup.unit.representation layout.value.representation (fun _ => scalarSource) scalarDraw)

include scalarCorrect in
theorem refines : Interactive.Refines (UniformQuery.port bound layout.wordFits fits) .unit
    (layout.coinValues bound fits qS storageFits).input.representation
    (CacheRead.output (layout.coinValues bound fits qS storageFits)).representation
    (source layout bound fits qS storageFits scalarSource) (code layout bound fits qS storageFits scalarDraw) :=
  EncodedCacheRead.refines (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M) _ _ _
    (CoronSampling.refines layout.value bound layout.wordFits fits qS layout.coinValueFits scalarCorrect)

include scalarCorrect in
theorem time_bound {scalarTime : Nat}
    (scalarTimeBound : Interactive.TimeBound (UniformQuery.port bound layout.wordFits fits) .unit
      layout.lookup.unit.representation scalarDraw scalarTime) :
    Interactive.TimeBound (UniformQuery.port bound layout.wordFits fits) .unit
      (layout.coinValues bound fits qS storageFits).input.representation
      (code layout bound fits qS storageFits scalarDraw) (timeBudget layout bound fits qS storageFits scalarTime) :=
  EncodedCacheRead.time_bound (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M) _
    (CoronSampling.refines layout.value bound layout.wordFits fits qS layout.coinValueFits scalarCorrect)
    (CoronSampling.time_bound layout.value bound layout.wordFits fits qS layout.coinValueFits scalarCorrect scalarTimeBound)

theorem code_words {scalarWords : Nat}
    (scalarWordsBound : (scalarDraw.lower (UniformQuery.port bound layout.wordFits fits)).descriptionWords ≤ scalarWords) :
    ((code layout bound fits qS storageFits scalarDraw).lower (UniformQuery.port bound layout.wordFits fits)).descriptionWords ≤
      codeBudget layout bound fits qS storageFits scalarWords :=
  EncodedCacheRead.code_bound (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M) _ _
    (CoronSampling.code_words layout.value bound layout.wordFits fits qS layout.coinValueFits scalarWordsBound)

theorem names {scalarSlots : Nat}
    (scalarNames : WordIO.NamesBound (scalarDraw.lower (UniformQuery.port bound layout.wordFits fits)) scalarSlots) :
    WordIO.NamesAccounted ((code layout bound fits qS storageFits scalarDraw).lower
      (UniformQuery.port bound layout.wordFits fits)) (max 5 scalarSlots) := by
  have bounded := EncodedCacheRead.names (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M) _ _
    (CoronSampling.names layout.value bound layout.wordFits fits qS layout.coinValueFits scalarNames)
  exact bounded.mono (by omega)

theorem descriptionFits
    (scalarFits : (scalarDraw.lower (UniformQuery.port bound layout.wordFits fits)).DescriptionFits)
    {scalarSlots : Nat}
    (scalarNames : WordIO.NamesBound (scalarDraw.lower (UniformQuery.port bound layout.wordFits fits)) scalarSlots)
    (slotsFit : scalarSlots < 2 ^ w) :
    ((code layout bound fits qS storageFits scalarDraw).lower (UniformQuery.port bound layout.wordFits fits)).DescriptionFits :=
  EncodedCacheRead.descriptionFits (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M) _ _
    (CoronSampling.descriptionFits layout.value bound layout.wordFits fits qS layout.coinValueFits scalarFits)
    (CoronSampling.names layout.value bound layout.wordFits fits qS layout.coinValueFits scalarNames)
    (by have := layout.wordFits; omega)

theorem source_eq [SampleableType F]
    (scalarLaw : Subtype.val <$> scalarSource = ($ᵗ F : ProbComp F))
    (input : (layout.coinValues bound fits qS storageFits).input.Value) :
    Subtype.val <$> source layout bound fits qS storageFits scalarSource input =
      ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
        (.inr input.val.1)).run input.val.2.2.1 :=
  BLSCache.denote_privateOracle (base := cryptoBase F Unit Unit M M) (key := message) (val := valueTy qS.val)
    (layout.coinValues bound fits qS storageFits) (primitives F M) comparison (comparison_correct F M) _
    (CoronSampling.uniform layout.value bound layout.wordFits fits qS layout.coinValueFits scalarLaw) input

include scalarCorrect in
/-- One fixed program implements every admitted cache access, including full
cache hits. Memory counts the initial table and every intermediate copy. -/
theorem within [SampleableType F]
    (scalarLaw : Subtype.val <$> scalarSource = ($ᵗ F : ProbComp F))
    {scalarTime scalarWords scalarSlots : Nat}
    (scalarTimeBound : Interactive.TimeBound (UniformQuery.port bound layout.wordFits fits) .unit
      layout.lookup.unit.representation scalarDraw scalarTime)
    (scalarWordsBound : (scalarDraw.lower (UniformQuery.port bound layout.wordFits fits)).descriptionWords ≤ scalarWords)
    (scalarNames : WordIO.NamesBound (scalarDraw.lower (UniformQuery.port bound layout.wordFits fits)) scalarSlots)
    (scalarFits : (scalarDraw.lower (UniformQuery.port bound layout.wordFits fits)).DescriptionFits)
    (slotsFit : scalarSlots < 2 ^ w) :
    Interactive.Within (UniformQuery.port bound layout.wordFits fits)
      (layout.coinValues bound fits qS storageFits).input (CacheRead.output (layout.coinValues bound fits qS storageFits))
      (codeBudget layout bound fits qS storageFits scalarWords)
      (memoryBudget layout bound fits qS storageFits scalarTime scalarWords scalarSlots)
      (timeBudget layout bound fits qS storageFits scalarTime)
      (fun input => ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × Fin (qS.val + 1)))
        (.inr input.val.1)).run input.val.2.2.1) := by
  have bounded := Interactive.within_of_refines_accounted
    (refines layout bound fits qS storageFits scalarCorrect)
    (time_bound layout bound fits qS storageFits scalarCorrect scalarTimeBound)
    (code_words layout bound fits qS storageFits scalarWordsBound)
    (names layout bound fits qS storageFits scalarNames)
    (descriptionFits layout bound fits qS storageFits scalarFits scalarNames slotsFit)
  exact bounded.congr (source_eq layout bound fits qS storageFits scalarLaw)

end Signatures.Runtime.CaliperBackend.CoronCache

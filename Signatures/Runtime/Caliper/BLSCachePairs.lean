import Signatures.Runtime.Caliper.PairSamplingMemory
import Signatures.Runtime.Caliper.CacheReadMemory
import Signatures.Runtime.Caliper.BLSCache

/-! BLS's pair-valued private cache from a single certified scalar sampler.
Both scalar draws and every cache/control/copy operation are constructed.
The larger table representation must satisfy its own storage-width bound. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.CacheLayout

variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

theorem pairValueFits : layout.value.representation.encoding.words + layout.value.representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by dsimp [LookupLayout.width, lookup]; nlinarith)

def pairStorageWords : Nat :=
  8 * (1 + (layout.capacityPred + 1) * (layout.key.representation.encoding.words +
    (layout.value.representation.encoding.words + layout.value.representation.encoding.words)) +
      layout.key.representation.encoding.words + (layout.value.representation.encoding.words + layout.value.representation.encoding.words))

def pairValues (storageFits : layout.pairStorageWords < 2 ^ w) : CacheLayout w K (V × V) where
  key := layout.key
  value := layout.value.prod layout.value layout.pairValueFits
  capacityPred := layout.capacityPred
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := storageFits

end Signatures.Runtime.CaliperBackend.BoundedSource.CacheLayout

namespace Signatures.Runtime.CaliperBackend.BLSCache

open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)]
    (layout : CacheLayout w (key.Value base) (val.Value base))
    (storageFits : layout.pairStorageWords < 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (port : Interactive.Port w unifSpec) (scalar : Interactive.Code w)

def pairSampler : Interactive.Code w :=
  PairSampling.code layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar

def pairCode : Interactive.Code w :=
  EncodedCacheRead.code (base := base) (key := key) (val := .pair val val)
    (layout.pairValues storageFits) P comparison correct port (pairSampler layout port scalar)

theorem pair_time {source : ProbComp layout.value.Value}
    (scalarCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => source) scalar) {time : Nat}
    (scalarTime : Interactive.TimeBound port .unit layout.lookup.unit.representation scalar time) :
    Interactive.TimeBound port .unit (layout.pairValues storageFits).input.representation
      (pairCode layout storageFits P comparison correct port scalar)
      (EncodedCacheRead.timeBudget (base := base) (key := key) (val := .pair val val)
        (layout.pairValues storageFits) (PairSampling.timeBudget layout.value layout.value time time)) :=
  EncodedCacheRead.time_bound (base := base) (key := key) (val := .pair val val) (layout.pairValues storageFits) P comparison correct port
    (PairSampling.refines (hw := layout.wordFits) (fits := layout.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.time_bound (hw := layout.wordFits) (fits := layout.pairValueFits) scalarCorrect scalarCorrect scalarTime scalarTime)

theorem pair_words {words : Nat} (scalarWords : (scalar.lower port).descriptionWords ≤ words) :
    ((pairCode layout storageFits P comparison correct port scalar).lower port).descriptionWords ≤
      EncodedCacheRead.codeBudget (base := base) (key := key) (val := .pair val val)
        (layout.pairValues storageFits) (PairSampling.codeBudget layout.value layout.value words words) :=
  EncodedCacheRead.code_bound (base := base) (key := key) (val := .pair val val) (layout.pairValues storageFits) P comparison correct port _
    (PairSampling.code_bound layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar scalarWords scalarWords)

theorem pair_descriptionFits (scalarFits : (scalar.lower port).DescriptionFits)
    {scalarSlots : Nat} (scalarNames : WordIO.NamesBound (scalar.lower port) scalarSlots)
    (slotsFit : PairSampling.slots scalarSlots scalarSlots < 2 ^ w) :
    ((pairCode layout storageFits P comparison correct port scalar).lower port).DescriptionFits := by
  apply EncodedCacheRead.descriptionFits (base := base) (key := key) (val := .pair val val)
    (layout.pairValues storageFits) P comparison correct port (pairSampler layout port scalar)
  · exact PairSampling.descriptionFits layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar
      scalarFits scalarFits scalarNames (by unfold PairSampling.slots at slotsFit; omega)
  · exact PairSampling.names layout.value layout.value layout.wordFits layout.pairValueFits port scalar scalar scalarNames scalarNames
  · exact slotsFit

theorem pair_observe [SampleableType (val.Value base)]
    (source : ProbComp layout.value.Value)
    (scalarCorrect : Interactive.Refines port .unit layout.lookup.unit.representation layout.value.representation
      (fun _ => source) scalar)
    (scalarLaw : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (tape : RandomTape w) (value : (layout.pairValues storageFits).input.Value) (before : State w)
    (holds : (layout.pairValues storageFits).input.representation.Holds value before) :
    (fun result => Subtype.val <$> Interactive.observe (CacheRead.output (layout.pairValues storageFits)).representation result) <$>
      (pairCode layout storageFits P comparison correct port scalar).execute port .unit tape before =
        some <$> ((BLS.LazyAGM.Reduction.privateListOracle (M := key.Value base) (R := val.Value base × val.Value base))
          (.inr value.val.1)).run value.val.2.2.1 :=
  observe_privateOracle (base := base) (key := key) (val := .pair val val)
    (layout.pairValues storageFits) P comparison correct port
    (PairSampling.denote layout.value layout.value layout.pairValueFits source source) (pairSampler layout port scalar)
    (PairSampling.refines (hw := layout.wordFits) (fits := layout.pairValueFits) scalarCorrect scalarCorrect)
    (PairSampling.uniform layout.value layout.value layout.pairValueFits source source scalarLaw scalarLaw) tape value before holds

end Signatures.Runtime.CaliperBackend.BLSCache

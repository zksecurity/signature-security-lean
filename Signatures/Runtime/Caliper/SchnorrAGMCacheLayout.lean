import Signatures.Runtime.Caliper.SchnorrAGMLayout
import Signatures.Runtime.Caliper.StatefulCacheMemory

/-! Instantiate the stateful cache with Schnorr's affine explanation and bad
flag. The explanation is fixed before the fresh challenge; the resulting entry
and mutable flag have explicit represented source values. SchnorrAGMFresh
implements the fresh routine; the full metadata read wrapper remains separate. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Cache
open Caliper BoundedSource OracleComp OracleSpec
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def saved : Layout w ((F × F) × Bool) := layout.affine.prod layout.boolean
  (layout.fits_of_le (by change (_ + _) + 1 ≤ _; dsimp only [Layouts.width, storageWidth]; omega))

def model : StatefulCacheRead.Layouts w (M × G) (EncodedEntry F) (saved layout).Value where
  cache := layout.cache
  saved := (saved layout).representation
  storageFits := layout.fits_of_le (by
    change 8 * (layout.cache.lookup.width + (layout.affine.representation.encoding.words + 1) +
      layout.entry.representation.encoding.words + 1) ≤ _
    dsimp only [CacheLayout.lookup, LookupLayout.width, Layouts.cache]
    rw [Layouts.affine_words, Layouts.key_words, Layouts.entry_words]
    dsimp only [Layouts.width, storageWidth]
    nlinarith)

variable [Zero F] [Add F] [DecidableEq F]

def freshValue (challenge : layout.scalar.Value) (state : (saved layout).Value) :
    layout.entry.Value × (saved layout).Value :=
  (⟨(challenge.val, true, state.val.1), challenge.property, trivial, state.property.1⟩,
    ⟨(state.val.1, state.val.2 || decide (state.val.1.2 + challenge.val = 0)), state.property.1, trivial⟩)

def freshSource (sampler : ProbComp layout.scalar.Value) (state : (saved layout).Value) :
    ProbComp (layout.entry.Value × (saved layout).Value) :=
  (fun challenge => freshValue layout challenge state) <$> sampler

theorem freshSource_value (sampler : ProbComp layout.scalar.Value) (state : (saved layout).Value) :
    (fun result => (result.1.val, result.2.val)) <$> freshSource layout sampler state =
      (fun challenge => ((challenge, true, state.val.1), state.val.1,
        state.val.2 || decide (state.val.1.2 + challenge = 0))) <$> (Subtype.val <$> sampler) := by
  simp only [freshSource, Functor.map_map]
  rfl

theorem freshSource_uniform [SampleableType F] (sampler : ProbComp layout.scalar.Value)
    (law : Subtype.val <$> sampler = ($ᵗ F : ProbComp F)) (state : (saved layout).Value) :
    (fun result => (result.1.val, result.2.val)) <$> freshSource layout sampler state =
      (fun challenge => ((challenge, true, state.val.1), state.val.1,
        state.val.2 || decide (state.val.1.2 + challenge = 0))) <$> ($ᵗ F : ProbComp F) := by
  rw [freshSource_value, law]

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Cache

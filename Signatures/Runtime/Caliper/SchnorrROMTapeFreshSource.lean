import Signatures.Runtime.Caliper.SchnorrROMTapeFresh
import Signatures.Runtime.Caliper.SchnorrROMTapeReadSource

/-! The constructed draw supplies exactly the original raw oracle's encoded
reply. Only scalar sampling remains a local cryptographic routine. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

theorem denote_value (scalarSource : ProbComp layout.scalar.Value) (tag : layout.counter.Value) :
    Subtype.val <$> denote layout zeroValid scalarSource tag =
      if tag.val = 1 then (fun answer => (1, answer.val, 0)) <$> scalarSource
      else (fun answer : Fin (tag.val - 2 + 1) => (tag.val, (0 : F), answer.val)) <$> unifSpec.query (tag.val - 2) := by
  by_cases challenge : tag.val = 1 <;>
    simp [denote, branchDenote, Read.produced, Boolean.select, sumView, scalarDenote,
      privateDenote, privateDrawDenote, naturalSource, naturalView, UniformQueryDraw.source,
      challenge, bind_pure_comp, Functor.map_map]

def sample (scalarSource : ProbComp layout.scalar.Value) : QueryImpl (Schnorr.RawTape.Spec F) ProbComp
  | .inl n => unifSpec.query n
  | .inr () => Subtype.val <$> scalarSource

theorem rawDraw (scalarSource : ProbComp layout.scalar.Value) (i : (Schnorr.RawTape.Spec F).Domain)
    (valid : layout.counter.valid (Schnorr.RawTape.tag i)) :
    Subtype.val <$> denote layout zeroValid scalarSource ⟨Schnorr.RawTape.tag i, valid⟩ =
      Schnorr.RawTape.encode i <$> sample layout scalarSource i := by
  rw [denote_value]
  rcases i with n | ⟨⟩
  · have different : n + 2 ≠ 1 := by omega
    simp only [Schnorr.RawTape.tag, Schnorr.RawTape.family, Schnorr.SeedTape.familyTag, sample, different, ↓reduceIte]
    rw [Nat.add_sub_cancel]
    rfl
  · simp [Schnorr.RawTape.tag, Schnorr.RawTape.family, Schnorr.SeedTape.familyTag,
      Schnorr.RawTape.encode, Schnorr.encodeReply, sample, Functor.map_map]

/-- The replay handler no longer assumes a complete fresh-cell implementation. -/
theorem read_rawOracle (scalarSource : ProbComp layout.scalar.Value)
    (i : (Schnorr.RawTape.Spec F).Domain) (state : Schnorr.RawTape.State F)
    (valid : (Read.input layout).valid (Read.rawInput i state)) :
    (fun value => Read.rawOutput i value.val) <$>
      Read.denote layout (denote layout zeroValid scalarSource) ⟨Read.rawInput i state, valid⟩ =
        simulateQ (sample layout scalarSource) ((Schnorr.RawTape.oracle i).run state) :=
  Read.rawOracle layout (denote layout zeroValid scalarSource) (sample layout scalarSource) i state valid
    (rawDraw layout zeroValid scalarSource i valid.1)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh

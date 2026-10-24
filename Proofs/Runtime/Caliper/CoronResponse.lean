import Proofs.Runtime.Caliper.CoronResponseLayout
import Proofs.Runtime.Caliper.GuardedBranchBounds
import Proofs.Runtime.Caliper.EncodedConstant
import Proofs.Runtime.CoronPairedCache

/-! Constructed Coron response code. The scalar/coin and challenge points are
stored inputs. Coin testing, conditional dispatch, argument selection and
retained copies execute Caliper instructions. Only scaling and addition are
supplied group implementations; the represented zero is emitted as literal code. -/
namespace Signatures.Runtime.CaliperBackend.CoronResponse
open Caliper BoundedSource OracleComp OracleSpec

section Implementation
variable {w qS : Nat} {F G : Type} [SMul F G] [Add G] [Zero G]
    (layout : Layouts w F G qS) (zeroValid : layout.point.valid 0)
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))

def zeroPoint : Implementation .unit layout.input layout.point (fun _ => 0) :=
  Implementation.constant layout.input layout.point ⟨0, zeroValid⟩ layout.wordFits

def scaled (signing : Bool) : Implementation .unit layout.input layout.point
    (fun value => value.1.1 • (if signing then value.2.2.1 else value.2.1)) :=
  (arguments layout signing).then scale

def offset : Implementation .unit layout.input layout.point
    (fun value => if value.1.2 = 0 then value.2.2.2 else 0) :=
  (GuardedBranch.implementation (hw := layout.wordFits) (test layout) (by decide)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((challengePoint layout).restrictInput (fun value => condition value = true))
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = false))).castFunction (by
      funext value; simp [condition])

omit [SMul F G] [Add G] in
theorem offset_buffers : (offset layout zeroValid).program.code.memBound ≤ 3 := by
  have bounded := GuardedBranch.implementation_buffers (hw := layout.wordFits) (test layout)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((challengePoint layout).restrictInput (fun value => condition value = true))
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = false))
    (test_buffers layout) (challengePoint_buffers layout)
    (Implementation.constant_buffers layout.input layout.point ⟨0, zeroValid⟩ layout.wordFits)
  exact bounded

def sign : Implementation .unit layout.input layout.point
    (fun value => if value.1.2 = 0 then 0 else value.1.1 • value.2.2.1) :=
  (GuardedBranch.implementation (hw := layout.wordFits) (test layout) (by decide)
    (nameFits layout _ (test_buffers layout) (by have := layout.wordFits; omega)) layout.duplicateFits layout.tagFits
    ((zeroPoint layout zeroValid).restrictInput (fun value => condition value = true))
    ((scaled layout scale true).restrictInput (fun value => condition value = false))).castFunction (by
      funext value; simp [condition])

variable {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

include scaleBuffers in
omit [Add G] [Zero G] in
theorem scaled_buffers (signing : Bool) : (scaled layout scale signing).program.code.memBound ≤ max 3 slots :=
  max_le ((arguments_buffers layout signing).trans (Nat.le_max_left _ _)) (scaleBuffers.trans (Nat.le_max_right _ _))

def hashArguments : Implementation .unit layout.input layout.points
    (fun value => (value.1.1 • value.2.1, if value.1.2 = 0 then value.2.2.2 else 0)) :=
  (scaled layout scale false).pair (offset layout zeroValid) (by decide) layout.wordFits
    (nameFits layout _ (scaled_buffers layout scale scaleBuffers false) (by have := layout.wordFits; omega))
    (nameFits layout _ (offset_buffers layout zeroValid) (by have := layout.wordFits; omega))
    layout.duplicateFits (layout.fits_of_le (by rw [Layouts.input_words]; unfold Layouts.width; omega)) _

def hash : Implementation .unit layout.input layout.point
    (fun value => value.1.1 • value.2.1 + if value.1.2 = 0 then value.2.2.2 else 0) :=
  (hashArguments layout zeroValid scale scaleBuffers reserve).then add

def replyValue (signing : Bool) (value : (F × Fin (qS + 1)) × (G × (G × G))) : G :=
  if signing then (if value.1.2 = 0 then 0 else value.1.1 • value.2.2.1)
  else value.1.1 • value.2.1 + if value.1.2 = 0 then value.2.2.2 else 0

def reply (signing : Bool) : Implementation .unit layout.input layout.point (replyValue signing) := by
  cases signing
  · exact hash layout zeroValid scale add scaleBuffers reserve
  · exact sign layout zeroValid scale

end Implementation

/-- The sampler's full support and implemented scaling already represent the
group zero. A higher-level caller need not supply a new zero-coverage contract. -/
theorem zero_valid {w qS : Nat} {F G : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] (layout : Layouts w F G qS)
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (source : ProbComp layout.scalar.Value)
    (law : Subtype.val <$> source = ($ᵗ F : ProbComp F))
    (point : layout.point.Value) : layout.point.valid 0 := by
  have supported : (0 : F) ∈ support (Subtype.val <$> source) := by
    rw [law]
    exact mem_support_uniformSample F
  rw [support_map, Set.mem_image] at supported
  obtain ⟨scalar, _, equal⟩ := supported
  have scalarValid : layout.scalar.valid (0 : F) := equal ▸ scalar.property
  simpa only [zero_smul] using scale.preserves (0, point.val) ⟨scalarValid, point.property⟩

theorem reply_source {F G : Type} [Field F] [AddCommGroup G] [Module F G]
    {qS : Nat} (signing : Bool) (value : (F × Fin (qS + 1)) × (G × (G × G))) :
    replyValue signing value = Coron.Paired.response value.2.1 value.2.2.1 value.2.2.2 signing value.1 := rfl

end Signatures.Runtime.CaliperBackend.CoronResponse

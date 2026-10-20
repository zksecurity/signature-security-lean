import Signatures.Runtime.Caliper.WeightedBadSetupBounds
import Signatures.Runtime.Caliper.WeightedFullBounds
import Signatures.Runtime.Caliper.WeightedFullSource

/-! Join outer scalar sampling and actual key computation to the complete
initialized weighted program. The compatibility equation identifies byte
layouts; it does not assume a source or resource theorem for a solver. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G F M A PK : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G F (val.Value base) (F × (G × G)) A)
    (setup : WeightedSetup.Layouts layout.service PK)

structure Resampling [SMul F PK] where
  preparation : WeightedBadSetup.Layouts w F G PK
  compatible : preparation.output = setup.challenge
  scale : Implementation .unit preparation.arguments preparation.key (fun value => value.1 • value.2)
  slots : Nat
  reserve : slots + 5 < 2 ^ w
  names : NamesBound scale.program.code slots
  budget : Budget
  bounded : scale.BoundedBy budget.time budget.words

private def transport {X : Type} {left right : Layout w X} (same : left = right) (value : left.Value) : right.Value :=
  same ▸ value
private theorem transport_val {X : Type} {left right : Layout w X} (same : left = right) (value : left.Value) :
    (transport same value).val = value.val := by cases same; rfl
private theorem transport_bytes {X : Type} {left right : Layout w X} (same : left = right) (value : left.Value) :
    right.representation.encoding.encode (transport same value) = left.representation.encoding.encode value := by
  cases same
  rfl
namespace Resampling
variable [SMul F PK] (resampling : Resampling layout setup)
def view (value : resampling.preparation.output.Value) : setup.challenge.Value :=
  transport resampling.compatible value
@[simp] theorem view_val (value : resampling.preparation.output.Value) :
    (Resampling.view layout setup resampling value).val = value.val := transport_val resampling.compatible value
theorem view_bytes (value : resampling.preparation.output.Value) :
    setup.challenge.representation.encoding.encode (Resampling.view layout setup resampling value) =
      resampling.preparation.output.representation.encoding.encode value := transport_bytes resampling.compatible value
end Resampling

variable [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] [SMul F PK]
    (resampling : Resampling layout setup)
    (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout setup.key.representation)
    (draw outerDraw : Interactive.Code w) (fuel : Nat)

def resampleCode := WeightedBadSetup.code resampling.preparation resampling.scale resampling.names.buffers resampling.reserve layout.port outerDraw
def badCode : Interactive.Code w :=
  .seq (resampleCode layout setup resampling outerDraw)
    (code layout setup routines P comparison correct caller draw fuel false)

variable (source : ProbComp layout.service.evaluation.cache.value.Value)
    (outerSource : ProbComp resampling.preparation.scalar.Value)
def resampleSource (value : resampling.preparation.challenge.Value) : ProbComp setup.challenge.Value :=
  Resampling.view layout setup resampling <$> WeightedBadSetup.denote resampling.preparation resampling.scale resampling.names.buffers resampling.reserve outerSource value
def badSource (value : resampling.preparation.challenge.Value) : ProbComp layout.extraction.scalar.Value :=
  resampleSource layout setup resampling outerSource value >>=
    denote layout setup routines P comparison correct caller fuel false source

variable (outerCorrect : Interactive.Refines layout.port .unit resampling.preparation.unit.representation
    resampling.preparation.scalar.representation (fun _ => outerSource) outerDraw)
omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include outerCorrect in
theorem resample_refines : Interactive.Refines layout.port .unit resampling.preparation.challenge.representation
    setup.challenge.representation (resampleSource layout setup resampling outerSource) (resampleCode layout setup resampling outerDraw) :=
  (WeightedBadSetup.refines resampling.preparation resampling.scale resampling.names.buffers resampling.reserve
    layout.port outerDraw outerSource outerCorrect).viewOutput setup.challenge.representation
      (Resampling.view layout setup resampling) (Resampling.view_bytes layout setup resampling)

variable (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (invariant : Invariant layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)

include outerCorrect drawCorrect combineLaw zeroLaw uniform invariant cacheRoom hashRoom signRoom in
theorem bad_refines : Interactive.Refines layout.port .unit resampling.preparation.challenge.representation
    layout.extraction.scalar.representation (badSource layout setup resampling routines P comparison correct caller fuel source outerSource)
    (badCode layout setup resampling routines P comparison correct caller draw outerDraw fuel) :=
  (resample_refines layout setup resampling outerDraw outerSource outerCorrect).seq
    (refines layout setup routines P comparison correct caller draw fuel false source invariant cacheRoom hashRoom signRoom
      drawCorrect combineLaw zeroLaw uniform)
end Signatures.Runtime.CaliperBackend.WeightedFull

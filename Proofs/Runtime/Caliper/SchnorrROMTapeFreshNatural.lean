import Proofs.Runtime.Caliper.SchnorrROMTapeFreshPrepare
import Proofs.Runtime.Caliper.UniformQueryDraw

/-! The full word range for runtime private sampling. The fixed-size query
adapter forwards the requested range without enumerating its possible values. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F : Type} (layout : Layouts w F)

def randomBound : Nat := 2 ^ w - 1
theorem randomSize : randomBound (w := w) + 1 = 2 ^ w := by
  unfold randomBound
  have : 0 < 2 ^ w := by positivity
  omega
theorem randomFits : randomBound (w := w) + 1 ≤ 2 ^ w := (randomSize (w := w)).le
def port := UniformQuery.port (randomBound (w := w)) layout.wordFits randomFits
def naturalCode := UniformQueryDraw.code (randomBound (w := w)) layout.wordFits randomFits

def naturalView : layout.counter.Value ≃ (UniformQueryDraw.value (randomBound (w := w)) layout.wordFits randomFits).Value where
  toFun value := ⟨value.val, by change value.val < randomBound + 1; rw [randomSize]; exact value.property⟩
  invFun value := ⟨value.val, by
    change value.val < 2 ^ w
    have valid : value.val < randomBound (w := w) + 1 := value.property
    rwa [randomSize] at valid⟩
  left_inv _ := rfl
  right_inv _ := rfl
def naturalSource (request : layout.counter.Value) : ProbComp layout.counter.Value :=
  (naturalView layout).symm <$> UniformQueryDraw.source (randomBound (w := w)) layout.wordFits randomFits (naturalView layout request)

theorem natural_refines : Interactive.Refines (port layout) .unit layout.counter.representation layout.counter.representation
    (naturalSource layout) (naturalCode layout) :=
  ((UniformQueryDraw.refines (randomBound (w := w)) layout.wordFits randomFits).viewInput layout.counter.representation
    (naturalView layout) (fun _ => rfl)).viewOutput layout.counter.representation (naturalView layout).symm (fun _ => rfl)
theorem natural_time : Interactive.TimeBound (port layout) .unit layout.counter.representation (naturalCode layout) 18 :=
  (UniformQueryDraw.time_bound (randomBound (w := w)) layout.wordFits randomFits).viewInput layout.counter.representation
    (naturalView layout) (fun _ => rfl)
theorem natural_words : ((naturalCode layout).lower (port layout)).descriptionWords ≤ 85 :=
  UniformQueryDraw.code_bound (randomBound (w := w)) layout.wordFits randomFits
theorem natural_names : WordIO.NamesBound ((naturalCode layout).lower (port layout)) 3 :=
  UniformQueryDraw.names (randomBound (w := w)) layout.wordFits randomFits
theorem natural_buffers : ((naturalCode layout).lower (port layout)).memBound ≤ 2 :=
  UniformQueryDraw.buffers (randomBound (w := w)) layout.wordFits randomFits
theorem natural_fits : ((naturalCode layout).lower (port layout)).DescriptionFits :=
  UniformQueryDraw.descriptionFits (randomBound (w := w)) layout.wordFits randomFits

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh

import Signatures.Runtime.Caliper.BLSTokensSource
import Signatures.Runtime.Caliper.BLSFinalFrameNames
import Signatures.Runtime.Caliper.BLSFinalTargetOracle

/-! Stored forgery context across signature-transcript evaluation. The two
representations are the exact product encodings used by executed retain code;
viewing its result as the final frame changes only subtype witnesses. -/
namespace Signatures.Runtime.CaliperBackend.BLSSignatureTail
open Caliper BoundedSource
variable {w : Nat} {M G F : Type} (layout : BLSTokens.Layouts w M G F)
abbrev goodContext := BLSFinalFrame.context layout.rows.accumulation
abbrev badContext := CacheTargetFrame.context layout.rows.accumulation.bad
abbrev GoodInput := layout.good.input.Value × (goodContext layout).Value
abbrev BadInput := layout.bad.input.Value × (badContext layout).Value
abbrev GoodReturned := layout.rows.good.state.Value × (goodContext layout).Value
abbrev BadReturned := layout.rows.bad.state.Value × (badContext layout).Value

def goodInput (fits : layout.good.input.representation.encoding.words + (goodContext layout).representation.encoding.words < 2 ^ w) :
    Representation w (GoodInput layout) := layout.good.input.representation.prod (goodContext layout).representation fits
def badInput (fits : layout.bad.input.representation.encoding.words + (badContext layout).representation.encoding.words < 2 ^ w) :
    Representation w (BadInput layout) := layout.bad.input.representation.prod (badContext layout).representation fits
theorem goodOutputFits : layout.rows.good.state.representation.encoding.words + (goodContext layout).representation.encoding.words < 2 ^ w :=
  (BLSFinalFrame.returned layout.rows.accumulation).representation.fits
theorem badOutputFits : layout.rows.bad.state.representation.encoding.words + (badContext layout).representation.encoding.words < 2 ^ w :=
  (CacheTargetFrame.returned layout.rows.accumulation.bad).representation.fits
def goodReturned : Representation w (GoodReturned layout) :=
  layout.rows.good.state.representation.prod (goodContext layout).representation (goodOutputFits layout)
def badReturned : Representation w (BadReturned layout) :=
  layout.rows.bad.state.representation.prod (badContext layout).representation (badOutputFits layout)
def goodView (value : GoodReturned layout) : (BLSFinalFrame.returned layout.rows.accumulation).Value :=
  ⟨(value.1.val, value.2.val), value.1.property, value.2.property⟩
def badView (value : BadReturned layout) : (CacheTargetFrame.returned layout.rows.accumulation.bad).Value :=
  ⟨(value.1.val, value.2.val), value.1.property, value.2.property⟩
theorem goodView_bytes (value : GoodReturned layout) :
    (BLSFinalFrame.returned layout.rows.accumulation).representation.encoding.encode (goodView layout value) =
      (goodReturned layout).encoding.encode value := rfl
theorem badView_bytes (value : BadReturned layout) :
    (CacheTargetFrame.returned layout.rows.accumulation.bad).representation.encoding.encode (badView layout value) =
      (badReturned layout).encoding.encode value := rfl

def goodReady (value : GoodInput layout) : Prop :=
  value.1.val.2.length + value.1.val.1.1.length + 1 ≤ layout.rows.accumulation.cache.capacityPred + 1
def badReady (value : BadInput layout) : Prop :=
  value.1.val.2.length + value.1.val.1.1.length + 1 ≤ layout.rows.accumulation.bad.cache.capacityPred + 1

theorem good_evaluation_ready (value : GoodInput layout) (ready : goodReady layout value) : layout.good.ready value.1 := by
  change value.1.val.2.length + value.1.val.1.1.length ≤ _
  unfold goodReady at ready
  exact Nat.le_trans (Nat.le_add_right _ _) ready
theorem bad_evaluation_ready (value : BadInput layout) (ready : badReady layout value) : layout.bad.ready value.1 := by
  change value.1.val.2.length + value.1.val.1.1.length ≤ _
  unfold badReady at ready
  exact Nat.le_trans (Nat.le_add_right _ _) ready

variable [Zero F] [DecidableEq M] (zeroValid : layout.rows.accumulation.cache.value.valid 0)
def goodFinalReady (value : GoodReturned layout) : Prop := BLSFinalFrame.admissible layout.rows.accumulation (goodView layout value).val
def badFinalReady (value : BadReturned layout) : Prop :=
  CacheTargetFrame.admissible layout.rows.accumulation.bad (BLSFinalFrame.pairZero layout.rows.accumulation zeroValid) (badView layout value).val
instance (value : GoodReturned layout) : Decidable (goodFinalReady layout value) := inferInstanceAs (Decidable (BLSFinalFrame.admissible _ _))
instance (value : BadReturned layout) : Decidable (badFinalReady layout zeroValid value) := inferInstanceAs (Decidable (CacheTargetFrame.admissible _ _ _))
def goodAdmitted (value : {value : GoodReturned layout // goodFinalReady layout value}) : (BLSFinalFrame.goodInput layout.rows.accumulation).Value :=
  ⟨(goodView layout value.val).val, (goodView layout value.val).property, value.property⟩
def badAdmitted (value : {value : BadReturned layout // badFinalReady layout zeroValid value}) :
    (BLSFinalFrame.badInput layout.rows.accumulation zeroValid).Value :=
  ⟨(badView layout value.val).val, (badView layout value.val).property, value.property⟩
end Signatures.Runtime.CaliperBackend.BLSSignatureTail

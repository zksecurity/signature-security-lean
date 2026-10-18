import VCVio.OracleComp.Constructions.SampleableType.Basic
import Signatures.Runtime.Caliper.RestrictedLayout
import Signatures.Runtime.Caliper.InteractiveControlBounds
import Signatures.Runtime.Caliper.InteractiveNames
import Signatures.Runtime.Caliper.InteractiveAcceptance

/-! Runtime-selected uniform queries with a fixed word interface. The request
stores the range minus one. The dependent reply stores that range and its sampled
index. No sampler table is indexed by all possible ranges. This is a forwarding
interface to the original uniform oracle, not a fair-bit sampling implementation. -/

namespace Signatures.Runtime.CaliperBackend.UniformQuery
open Caliper BoundedSource OracleComp OracleSpec

variable {w : Nat} (bound : Nat) (hw : 16 < 2 ^ w) (fits : bound + 1 ≤ 2 ^ w)

abbrev Reply (bound : Nat) := Σ n : Fin (bound + 1), Fin (n.val + 1)

def request : Representation w (Fin (bound + 1)) := Representation.fin w (bound + 1) (width_pos hw) fits

def packet : Layout w (Nat × Nat) :=
  ((Layout.counter w (bound + 1) (width_pos hw) fits).prod
    (Layout.counter w (bound + 1) (width_pos hw) fits) (by change 1 + 1 < 2 ^ w; omega)).restrict
      (fun value => value.2 ≤ value.1)

def replyView : Reply bound ≃ (packet bound hw fits).Value where
  toFun value := ⟨(value.1.val, value.2.val), ⟨value.1.isLt, by change value.2.val < bound + 1; have := value.2.isLt; have := value.1.isLt; omega⟩,
    Nat.le_of_lt_succ value.2.isLt⟩
  invFun value := ⟨⟨value.val.1, value.property.1.1⟩, ⟨value.val.2, Nat.lt_succ_of_le value.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def reply : Representation w (Reply bound) := (packet bound hw fits).representation.transport (replyView bound hw fits)

def port : Interactive.Port w unifSpec where
  Request := Fin (bound + 1)
  source := Fin.val
  request := request bound hw fits
  reply := reply bound hw fits

@[simp] theorem request_words : (request bound hw fits).encoding.words = 1 := rfl
@[simp] theorem reply_words : (reply bound hw fits).encoding.words = 2 := rfl

def source (n : Fin (bound + 1)) : ProbComp (Reply bound) :=
  (fun answer => (⟨n, answer⟩ : Reply bound)) <$> (unifSpec.query n.val)

theorem refines : Interactive.Refines (port bound hw fits) .unit (request bound hw fits) (reply bound hw fits)
    (source bound) .query := Interactive.Refines.query _ _

theorem time_bound : Interactive.TimeBound (port bound hw fits) .unit (request bound hw fits) .query 10 := by
  have bounded := Interactive.TimeBound.query (port := port bound hw fits) (cost := .unit)
  rw [WordIO.exchangeTime_unit] at bounded
  exact bounded

theorem code_words : ((Interactive.Code.query : Interactive.Code w).lower (port bound hw fits)).descriptionWords = 41 :=
  WordIO.exchange_descriptionWords 1 2

theorem names : WordIO.NamesBound ((Interactive.Code.query : Interactive.Code w).lower (port bound hw fits)) 3 := by
  constructor
  · change (WordIO.exchange (w := w) 1 2).registerSlots ≤ 3
    simp [WordIO.exchange, WordIO.send, WordIO.receive, WordIO.Code.registerSlots, registerSlots]
  · change (WordIO.exchange (w := w) 1 2).memBound ≤ 3
    simp [WordIO.exchange, WordIO.send, WordIO.receive, WordIO.Code.memBound, Stmt.memBound]

theorem descriptionFits : ((Interactive.Code.query : Interactive.Code w).lower (port bound hw fits)).DescriptionFits :=
  WordIO.exchange_descriptionFits 1 2 (by omega) (by omega)

variable {S : Type} (saved : Representation w S) (storage : 2 + saved.encoding.words < 2 ^ w)

def input : Representation w (Fin (bound + 1) × S) := (request bound hw fits).prod saved (by simp; omega)
def output : Representation w (Reply bound × S) := (reply bound hw fits).prod saved storage

def forward : Interactive.Code w :=
  Interactive.retain .query (Interactive.savedBuffer (port bound hw fits) .query) 1 2 saved.encoding.words

def forwardSource (value : Fin (bound + 1) × S) : ProbComp (Reply bound × S) :=
  (fun answer => (answer, value.2)) <$> source bound value.1

theorem forward_refines : Interactive.Refines (port bound hw fits) .unit
    (input bound hw fits saved storage) (output bound hw fits saved storage)
    (forwardSource bound) (forward bound hw fits saved) :=
  (refines bound hw fits).retain (by decide) saved hw (by simp; omega) storage

theorem forward_time : Interactive.TimeBound (port bound hw fits) .unit
    (input bound hw fits saved storage) (forward bound hw fits saved) (34 + 12 * saved.encoding.words) :=
  ((time_bound bound hw fits).retain (refines bound hw fits) (by decide) saved hw (by simp; omega)).mono
    (by
      change (Retain.prepare (w := w) _ 1 saved.encoding.words).staticTime .unit +
        (10 + (Retain.finish (w := w) _ 2 saved.encoding.words).staticTime .unit) ≤ _
      have h := Interactive.retain_time_unit_le (w := w) (Interactive.savedBuffer (port bound hw fits) .query) 1 2 saved.encoding.words 10
      omega)

theorem forward_words : ((forward bound hw fits saved).lower (port bound hw fits)).descriptionWords ≤ 160 + 39 * saved.encoding.words := by
  have bounded := Interactive.retain_descriptionWords_le (port bound hw fits) .query
    (Interactive.savedBuffer (port bound hw fits) .query) 1 2 saved.encoding.words
  rw [code_words] at bounded
  dsimp only [forward]
  omega

theorem forward_names : WordIO.NamesBound ((forward bound hw fits saved).lower (port bound hw fits)) 3 := by
  have prepared := Retain.prepare_names (w := w) 2 1 saved.encoding.words
  have finished := Retain.finish_names (w := w) 2 2 saved.encoding.words
  have body := names bound hw fits
  constructor
  · change max (registerSlots (Retain.prepare 2 1 saved.encoding.words))
      (max ((Interactive.Code.query : Interactive.Code w).lower (port bound hw fits)).registerSlots
        (registerSlots (Retain.finish 2 2 saved.encoding.words))) ≤ 3
    have := body.registers
    omega
  · have bounded := Interactive.retain_buffers (port bound hw fits) .query 1 2 saved.encoding.words
    exact bounded

include storage in
theorem forward_descriptionFits : ((forward bound hw fits saved).lower (port bound hw fits)).DescriptionFits :=
  Interactive.retain_descriptionFits (port bound hw fits) .query 2 1 2 saved.encoding.words hw
    (descriptionFits bound hw fits) (by omega) (by omega) saved.fits storage

end Signatures.Runtime.CaliperBackend.UniformQuery

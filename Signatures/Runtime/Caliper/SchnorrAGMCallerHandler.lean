import Signatures.Runtime.Caliper.SchnorrAGMCallerPacketBounds
import Signatures.Runtime.Caliper.InteractiveInvariantBounds

/-! The constructed Schnorr handler in the caller's independent request/reply
interface. Its admission guard constrains reachable private states, while all
packet conversion, query handling and output conversion execute charged code. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
variable {w qH qS randomBound : Nat} {M F G : Type}
    [Zero F] [Mul F] [Add F] [Neg F] [SMul F G] [Sub G]
    [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (layout : Handler.Layouts w M F G qH qS randomBound) (ops : Handler.Operations layout)

def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (prepare layout).code) (.seq (Handler.code layout ops sampler) (.compute (finish layout).code))

def emptyRandom : layout.random.reply.Value := ⟨(0, []), Nat.succ_pos _, by exact ⟨by change 0 ≤ 1; decide, by simp⟩⟩
def emptyGroup : layout.signing.reply.Value := ⟨(0, []), ops.zeroValid, by exact ⟨by change 0 ≤ 1; decide, by simp⟩⟩
def fallback : Request layout → Reply layout
  | .inl args => .inl (emptyRandom layout, args)
  | .inr (.inl args) => .inr (.inl (emptyGroup layout ops, args))
  | .inr (.inr args) => .inr (.inr (emptyGroup layout ops, args))

/-- Total source extension. No execution claim uses its unready branch. -/
def source (sampler : ProbComp layout.scheme.scalar.Value) (value : Packet layout) :
    ProbComp (Reply layout × layout.scheme.store.Value) :=
  if valid : ready layout value then
    finished layout <$> Handler.source layout ops sampler (serviceRequest layout value valid)
  else pure (fallback layout ops value.1, value.2)

variable {sampler : Interactive.Code w} {sampleSource : ProbComp layout.scheme.scalar.Value}
    (sampleCorrect : Interactive.Refines layout.random.port .unit (PairSampling.input w).representation layout.scheme.scalar.representation
      (fun _ => sampleSource) sampler)

include sampleCorrect in
theorem refines : Interactive.RefinesOn (ready layout) layout.random.port .unit (input layout) (output layout)
    (source layout ops sampleSource) (code layout ops sampler) := by
  have prepared := Interactive.Refines.compute layout.random.port .unit (prepareService layout)
  have service := Handler.refines layout ops sampleCorrect
  have converted := Interactive.Refines.compute layout.random.port .unit (finish layout)
  have combined := prepared.seq (service.seq converted)
  intro tape value valid before holds
  have checked := combined tape ⟨value, valid⟩ before holds
  simpa only [source, dite_eq_left valid, pure_bind, bind_pure_comp, code, prepareService,
    Realizer.viewInput, Realizer.viewOutput] using checked

variable (budget : Handler.Budget layout ops)
def timeBudget (sampleTime : Nat) := Handler.timeBudget layout ops budget sampleTime + 174 * width layout + 14
def codeBudget (sampleWords : Nat) := Handler.codeBudget layout ops budget sampleWords + 1120 * width layout + 774

include sampleCorrect in
theorem time_bound {sampleTime : Nat}
    (sampleBound : Interactive.TimeBound layout.random.port .unit (PairSampling.input w).representation sampler sampleTime) :
    Interactive.TimeBoundOn (ready layout) layout.random.port .unit (input layout) (code layout ops sampler)
      (timeBudget layout ops budget sampleTime) := by
  have prepared := Interactive.Refines.compute layout.random.port .unit (prepareService layout)
  have service := Handler.refines layout ops sampleCorrect
  have preparedTime := Interactive.TimeBound.compute (port := layout.random.port) (cost := .unit)
    (prepareService layout) (64 * width layout + 6) (fun value => prepare_time layout value.val)
  have serviceTime := Handler.time_bound layout ops sampleCorrect budget sampleBound
  have convertedTime := Interactive.TimeBound.compute (port := layout.random.port) (cost := .unit)
    (finish layout) (110 * width layout + 8) (finish_time layout)
  have combined := (preparedTime.seq prepared (serviceTime.seq service convertedTime)).mono
    (larger := timeBudget layout ops budget sampleTime) (by unfold timeBudget; omega)
  intro tape value valid before holds finished reached
  exact combined tape ⟨value, valid⟩ before holds finished reached

theorem code_bound {sampleWords : Nat} (sampleBound : (sampler.lower layout.random.port).descriptionWords ≤ sampleWords) :
    ((code layout ops sampler).lower layout.random.port).descriptionWords ≤ codeBudget layout ops budget sampleWords := by
  have prepared := prepare_words layout
  have converted := finish_words layout
  have service := Handler.code_bound layout ops budget sampleBound
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names {sampleSlots : Nat} (sampleNames : WordIO.NamesBound (sampler.lower layout.random.port) sampleSlots) :
    WordIO.NamesAccounted ((code layout ops sampler).lower layout.random.port) (Handler.nameBudget layout ops sampleSlots) :=
  ((WordIO.NamesAccounted.compute (prepare_names layout)).mono (by unfold Handler.nameBudget; omega)).seq
    ((Handler.names layout ops sampleNames).seq
      ((WordIO.NamesAccounted.compute (finish_names layout)).mono (by unfold Handler.nameBudget; omega)))

theorem descriptionFits {sampleSlots : Nat} (sampleFits : (sampler.lower layout.random.port).DescriptionFits)
    (sampleNames : WordIO.NamesBound (sampler.lower layout.random.port) sampleSlots)
    (reserve : max ops.slots sampleSlots + 5 < 2 ^ w) :
    ((code layout ops sampler).lower layout.random.port).DescriptionFits :=
  .seq layout.scheme.wordFits (.compute (prepare layout).description_fits)
    (.seq layout.scheme.wordFits (Handler.descriptionFits layout ops sampleFits sampleNames reserve)
      (.compute (finish layout).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerHandler

import Proofs.Runtime.Caliper.SchnorrAGMCallerFinishRoute
import Proofs.Runtime.Caliper.EncodedConstant

/-! Executed return/cutoff dispatch, terminal routing and scalar projection.
The source's admission test only makes its mathematical function total outside
the proved domain; the machine routes admitted returns directly to extraction. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS : Nat} {M F G P : Type} (layout : HashDispatch.Layouts w M F G qH qS)
    (pending : Representation w P)
    (fits : 1 + max (forgery layout).representation.encoding.words pending.encoding.words +
      layout.hash.scheme.store.representation.encoding.words < 2 ^ w)

def project : Realizer .unit (Read.output layout.hash.scheme).representation layout.hash.scheme.scalar.representation
    (fun value => ⟨value.val.1, value.property.1⟩) :=
  (Implementation.first (cost := .unit) (by decide) layout.hash.scheme.scalar layout.hash.scheme.state
    layout.hash.scheme.wordFits (Read.output layout.hash.scheme).representation.fits).program

def fallback (zero : layout.hash.scheme.scalar.Value) :
    Realizer .unit (cutoff layout pending fits) layout.hash.scheme.scalar.representation (fun _ => zero) :=
  Assembly.realizer .unit (by decide) _ _ _
    ((layout.hash.scheme.scalar.representation.encoding.encode zero).map Assembly.Operand.literal)
    layout.hash.scheme.wordFits
    (by simp only [List.length_map, Encoding.encode_length])
    (by intro operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)
    (by intro value state represented operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)
    (by intro value state represented; simp only [Assembly.values, List.map_map]; exact List.map_id _)

variable [DecidableEq M] [DecidableEq G]
def successCode (extractor : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (route layout pending fits).code) (.seq extractor (.compute (project layout).code))
def code (zero : layout.hash.scheme.scalar.Value) (extractor : Interactive.Code w) : Interactive.Code w :=
  Interactive.dispatch (successCode layout pending fits extractor) (.compute (fallback layout pending fits zero).code)
    (returned layout pending fits).encoding.words (cutoff layout pending fits).encoding.words

variable {I : Type} {spec : OracleSpec I}
def success (zero : layout.hash.scheme.scalar.Value)
    (extract : (Extraction.input layout).Value → OracleComp spec (Read.output layout.hash.scheme).Value)
    (value : Success layout) : OracleComp spec layout.hash.scheme.scalar.Value :=
  if valid : admitted layout value then
    (fun answer => ⟨answer.val.1, answer.property.1⟩) <$> extract (extractInput layout ⟨value, valid⟩)
  else pure zero
def denote (zero : layout.hash.scheme.scalar.Value)
    (extract : (Extraction.input layout).Value → OracleComp spec (Read.output layout.hash.scheme).Value)
    (value : Packet layout P) : OracleComp spec layout.hash.scheme.scalar.Value :=
  match value.1 with | .inl forgery => success layout zero extract (forgery, value.2) | .inr _ => pure zero

variable (port : Interactive.Port w spec)
    {extract : (Extraction.input layout).Value → OracleComp spec (Read.output layout.hash.scheme).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.Refines port .unit (Extraction.input layout).representation
      (Read.output layout.hash.scheme).representation extract extractor)

include extractCorrect in
theorem success_refines (zero : layout.hash.scheme.scalar.Value) :
    Interactive.RefinesOn (admitted layout) port .unit (returned layout pending fits) layout.hash.scheme.scalar.representation
      (success layout zero extract) (successCode layout pending fits extractor) := by
  have projected := extractCorrect.seq (Interactive.Refines.compute port .unit (project layout))
  have routed := (Interactive.Refines.compute port .unit (route layout pending fits)).seq projected
  intro tape value valid before represented
  have result := routed tape ⟨value, valid⟩ before represented
  simpa only [pure_bind, bind_pure_comp, success, dite_eq_left valid, successCode] using result

include extractCorrect in
theorem refines (zero : layout.hash.scheme.scalar.Value) :
    Interactive.RefinesOn (ready layout) port .unit (input layout pending fits) layout.hash.scheme.scalar.representation
      (denote layout zero extract) (code layout pending fits zero extractor) := by
  have branches := Interactive.RefinesOn.dispatch (returned layout pending fits) (cutoff layout pending fits)
    layout.hash.scheme.scalar.representation (success_refines layout pending fits port extractCorrect zero)
    ((Interactive.Refines.compute port .unit (fallback layout pending fits zero)).on (fun _ => True))
    (width_pos layout.hash.scheme.wordFits) (choice_fits layout pending fits)
  have viewed := branches.viewInput (input layout pending fits) SumContext.view (input_bytes layout pending fits)
  convert viewed using 1
  · funext value; rcases value with ⟨forgery | next, stored⟩ <;> rfl
  · funext value; rcases value with ⟨forgery | next, stored⟩ <;> rfl
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerFinish

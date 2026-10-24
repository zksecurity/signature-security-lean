import Proofs.Runtime.Caliper.WordFuel

/-! Linking the executed word packet adapter to an ideal typed oracle.

The oracle decodes only words actually sent by the machine, and supplies the
encoded reply as external input. Encoding/decoding here specify the oracle's
external representation convention; they are not free local instructions. All
local request loads, reply allocation and reply stores execute in `exchange`.
-/

namespace Signatures.Runtime.CaliperBackend.WordIO

open Caliper OracleComp OracleSpec

variable {w : Nat} {I : Type} (spec : OracleSpec I)

def outputs : List (Event w) → List (Word w)
  | [] => []
  | .output value :: rest => value :: outputs rest
  | .input _ :: rest | .invoke :: rest => outputs rest

theorem outputs_map (values : List (Word w)) : outputs (values.map Event.output) = values := by
  induction values <;> simp [outputs, *]

private def receiveReply (words : Nat) : Code w :=
  .seq .invoke (.seq (.compute (.memAllocI 0 words)) (receive 0 words))

/-- The ideal oracle is invoked after the outgoing instructions have executed.
Only the external oracle boundary interprets those bytes. Local continuation is
again evaluated by the verified word/Caliper interpreter. -/
def oracleCall (cost : Costs) (tape : RandomTape w) (request : Representation w I)
    (reply : Representation w (Σ i, spec.Range i)) (before : State w) : OracleComp spec (Option (Result w)) :=
  match run cost tape 2 (send 0 0 request.encoding.words) before [] with
  | none => pure none
  | some sent => match request.encoding.decode (outputs sent.trace) with
    | none => pure none
    | some position => do
      let answer ← (liftM (spec.query position) : OracleComp spec (spec.Range position))
      pure ((run cost tape 2 (receiveReply reply.encoding.words) sent.state
        (reply.encoding.encode ⟨position, answer⟩)).map fun result =>
          ⟨result.state, sent.time + result.time, sent.net + result.net,
            max sent.peak (sent.net + result.peak), sent.trace ++ result.trace, result.remaining⟩)

/-- The linked adapter performs exactly the source query and then executes the
complete charged packet program with the oracle's reply words. -/
theorem oracleCall_eq (cost : Costs) (tape : RandomTape w) (request : Representation w I)
    (reply : Representation w (Σ i, spec.Range i)) (position : I) (before : State w)
    (represented : request.Holds position before) :
    oracleCall spec cost tape request reply before = (do
      let answer ← (liftM (spec.query position) : OracleComp spec (spec.Range position))
      pure (run cost tape 2 (exchange request.encoding.words reply.encoding.words) before
        (reply.encoding.encode ⟨position, answer⟩))) := by
  have size := Assembly.represented_size request represented
  obtain ⟨sent, sending, _, _⟩ := send_exec cost tape 0 request.encoding.words 0 before
    (by omega) (by simpa [size] using request.fits)
  have sending' : Exec cost tape (send 0 0 request.encoding.words) before sent
      ((request.encoding.encode position).map Event.output)
      (request.encoding.words * (cost.machine.imm + cost.machine.memLoad + cost.write)) 0 0 := by
    simpa only [List.drop_zero, represented.2.1, ← request.encoding.encode_length position,
      List.take_length] using sending
  have noInput (values : List (Word w)) : inputs (values.map Event.output) = [] := by
    induction values <;> simp [inputs, *]
  have sentRun (suffix : List (Word w)) := sending'.run_atFuel (send_fuel _ _ _).2 2 (send_fuel _ _ _).1 suffix
  simp only [noInput, List.nil_append] at sentRun
  simp only [oracleCall, sentRun [], outputs_map, request.encoding.decode_encode]
  congr 1
  funext answer
  conv_rhs => rw [exchange, run, sentRun (reply.encoding.encode ⟨position, answer⟩)]
  change pure ((run cost tape 2 (receiveReply reply.encoding.words) sent
      (reply.encoding.encode ⟨position, answer⟩)).map _) =
    pure ((run cost tape 2 (receiveReply reply.encoding.words) sent
      (reply.encoding.encode ⟨position, answer⟩)).bind _)
  cases run cost tape 2 (receiveReply reply.encoding.words) sent (reply.encoding.encode ⟨position, answer⟩) <;> rfl

/-- Observing the decoded result gives precisely the original dependent oracle
query, with no failure on represented packets. This is an equality of oracle
computations, so it can be used inside adaptive source continuations. -/
theorem oracleCall_value (cost : Costs) (tape : RandomTape w) (request : Representation w I)
    (reply : Representation w (Σ i, spec.Range i)) (position : I) (before : State w)
    (represented : request.Holds position before) :
    (fun result => result.bind (fun finished => reply.encoding.decode (finished.state.bufs 0).toList)) <$>
      oracleCall spec cost tape request reply before =
    (fun answer => some (Sigma.mk position answer)) <$>
      (liftM (spec.query position) : OracleComp spec (spec.Range position)) := by
  rw [oracleCall_eq spec cost tape request reply position before represented]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext answer
  obtain ⟨result, execution, decoded, _⟩ := exchange_run cost tape request reply position ⟨position, answer⟩ before represented []
  simp only [List.append_nil] at execution
  simp [execution, decoded.2.1, reply.encoding.decode_encode]

end Signatures.Runtime.CaliperBackend.WordIO

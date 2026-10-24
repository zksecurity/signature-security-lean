import Proofs.Runtime.Caliper.WordIO

/-! Executable fixed-width oracle packets. Each outgoing word is loaded by
Caliper before being sent; each incoming word is received into a scratch register
and pushed by Caliper into previously allocated storage. Packet lengths are
compile-time bounds and all unrolled code is charged.
-/

namespace Signatures.Runtime.CaliperBackend.WordIO

open Caliper

variable {w : Nat}

def receive (buffer : BufId) : Nat → Code w
  | 0 => .compute .skip
  | count + 1 => .seq (.read 2) (.seq (.compute (.memPush buffer 2)) (receive buffer count))

def send (buffer : BufId) (start : Nat) : Nat → Code w
  | 0 => .compute .skip
  | count + 1 => .seq (.compute (.imm 1 (BitVec.ofNat w start) ;; .memLoad 2 buffer 1))
      (.seq (.write 2) (send buffer (start + 1) count))

theorem receive_descriptionWords (buffer count : Nat) :
    (receive (w := w) buffer count).descriptionWords = 8 * count + 2 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [Code.descriptionWords] at *
    simp only [receive, Code.description, description, List.length_cons, List.length_append,
      List.length_nil]
    omega

theorem send_descriptionWords (buffer start count : Nat) :
    (send (w := w) buffer start count).descriptionWords = 13 * count + 2 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    have h := ih (start + 1)
    simp only [Code.descriptionWords] at *
    simp only [send, Code.description, description, List.length_cons, List.length_append,
      List.length_nil]
    omega

theorem receive_descriptionFits (buffer count : Nat) (hw : 16 < 2 ^ w) (hb : buffer < 2 ^ w) :
    (receive (w := w) buffer count).DescriptionFits := by
  induction count with
  | zero => simp [Code.DescriptionFits, receive, Code.description, description]
  | succ count ih =>
    intro token member
    simp only [receive, Code.description, description, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false, or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | member <;>
      first | omega | exact ih token member

theorem send_descriptionFits (buffer start count : Nat) (hw : 16 < 2 ^ w) (hb : buffer < 2 ^ w) :
    (send (w := w) buffer start count).DescriptionFits := by
  induction count generalizing start with
  | zero => simp [Code.DescriptionFits, send, Code.description, description]
  | succ count ih =>
    intro token member
    simp only [send, Code.description, description, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false, or_assoc] at member
    have hword := (BitVec.ofNat w start).isLt
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | member <;>
      first | omega | exact ih (start + 1) token member

theorem receive_touches (buffer count other : Nat) :
    (receive (w := w) buffer count).Touches other → other = buffer := by
  induction count with
  | zero => simp [receive, Code.Touches, Stmt.Touches]
  | succ count ih =>
    intro touched
    simp only [receive, Code.Touches, Stmt.Touches, false_or] at touched
    exact touched.elim id ih

theorem send_touches (buffer start count other : Nat) :
    ¬ (send (w := w) buffer start count).Touches other := by
  induction count generalizing start <;> simp_all [send, Code.Touches, Stmt.Touches]

theorem receive_preserves_zero (buffer count : Nat) :
    ¬ (receive (w := w) buffer count).Writes 0 := by
  induction count <;> simp_all [receive, Code.Writes, Stmt.Writes]

theorem send_preserves_zero (buffer start count : Nat) :
    ¬ (send (w := w) buffer start count).Writes 0 := by
  induction count generalizing start <;> simp_all [send, Code.Writes, Stmt.Writes]

theorem receive_randomFree (buffer count : Nat) : (receive (w := w) buffer count).RandomFree := by
  induction count <;> simp_all [receive, Code.RandomFree, Stmt.RandomFree]

theorem send_randomFree (buffer start count : Nat) : (send (w := w) buffer start count).RandomFree := by
  induction count generalizing start <;> simp_all [send, Code.RandomFree, Stmt.RandomFree]

theorem receive_exec (cost : Costs) (tape : RandomTape w) (buffer : BufId)
    (values : List (Word w)) (before : State w)
    (room : (before.bufs buffer).size + values.length ≤ before.caps buffer) :
    ∃ after, Exec cost tape (receive buffer values.length) before after (values.map Event.input)
      (values.length * (cost.read + cost.machine.memPush)) 0 0 ∧
      (after.bufs buffer).toList = (before.bufs buffer).toList ++ values ∧ after.caps = before.caps := by
  induction values generalizing before with
  | nil => exact ⟨before, by simpa [receive] using (Exec.compute (Caliper.Exec.skip)), by simp, rfl⟩
  | cons value values ih =>
    let loaded := before.setReg 2 value
    let pushed := loaded.setBuf buffer ((before.bufs buffer).push value)
    have roomOne : (loaded.bufs buffer).size < loaded.caps buffer := by
      simp only [loaded, bufs_setReg, caps_setReg]
      simp only [List.length_cons] at room
      omega
    have push : Caliper.Exec cost.machine tape (.memPush buffer 2) loaded pushed cost.machine.memPush 0 0 := by
      simpa [pushed, loaded] using (Caliper.Exec.memPush (src := 2) roomOne)
    obtain ⟨after, execution, contents, capacities⟩ := ih pushed (by
      simp only [pushed, loaded, bufs_setBuf_self, Array.size_push, caps_setBuf, caps_setReg]
      simp only [List.length_cons] at room
      omega)
    refine ⟨after, ?_, ?_, capacities⟩
    · simpa [receive, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Exec.seq (Exec.read (destination := 2) (value := value)) (Exec.seq (Exec.compute push) execution)
    · simpa [pushed, Array.toList_push, List.append_assoc] using contents

theorem send_exec (cost : Costs) (tape : RandomTape w) (buffer : BufId)
    (count start : Nat) (before : State w)
    (span : start + count ≤ (before.bufs buffer).size) (fits : (before.bufs buffer).size < 2 ^ w) :
    ∃ after, Exec cost tape (send buffer start count) before after
      ((((before.bufs buffer).toList.drop start).take count).map Event.output)
      (count * (cost.machine.imm + cost.machine.memLoad + cost.write)) 0 0 ∧
      after.bufs = before.bufs ∧ after.caps = before.caps := by
  induction count generalizing start before with
  | zero => exact ⟨before, by simpa [send] using (Exec.compute (Caliper.Exec.skip)), rfl, rfl⟩
  | succ count ih =>
    have index : start < (before.bufs buffer).size := by omega
    have word : (BitVec.ofNat w start).toNat = start := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (index.trans fits)]
    let indexed := before.setReg 1 (BitVec.ofNat w start)
    let loaded := indexed.setReg 2 (before.bufs buffer)[start]
    have load : Caliper.Exec cost.machine tape (.memLoad 2 buffer 1) indexed loaded cost.machine.memLoad 0 0 := by
      have bound : (indexed.regs 1).toNat < (indexed.bufs buffer).size := by simpa [indexed, word] using index
      simpa [indexed, loaded, word] using (Caliper.Exec.memLoad (d := 2) bound)
    obtain ⟨after, execution, contents, capacities⟩ := ih (start + 1) loaded
      (by simp only [loaded, indexed, bufs_setReg]; omega) fits
    refine ⟨after, ?_, contents, capacities⟩
    have first : Exec cost tape (.compute (.imm 1 (BitVec.ofNat w start) ;; .memLoad 2 buffer 1))
        before loaded [] (cost.machine.imm + cost.machine.memLoad) 0 0 := by
      simpa using Exec.compute (Caliper.Exec.seq Caliper.Exec.imm load)
    have written : Exec cost tape (.write 2) loaded loaded
        [.output (before.bufs buffer)[start]] cost.write 0 0 := by simpa [loaded] using (Exec.write (source := 2) (before := loaded))
    have joined := Exec.seq first (Exec.seq written execution)
    rw [List.drop_eq_getElem_cons (i := start) (l := (before.bufs buffer).toList) (by simpa using index)]
    simpa [send, loaded, indexed, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- A synchronous packet exchange reuses the input buffer only after all request
words have been sent. Other buffers can hold suspended caller state. -/
def exchange (requestWords replyWords : Nat) : Code w :=
  .seq (send 0 0 requestWords)
    (.seq .invoke (.seq (.compute (.memAllocI 0 replyWords)) (receive 0 replyWords)))

def exchangeTime (cost : Costs) (requestWords replyWords : Nat) : Nat :=
  requestWords * (cost.machine.imm + cost.machine.memLoad + cost.write) + cost.invoke +
    (cost.machine.memAlloc + replyWords * cost.machine.allocPerWord) +
    replyWords * (cost.read + cost.machine.memPush)

theorem exchangeTime_unit (requestWords replyWords : Nat) :
    exchangeTime .unit requestWords replyWords = 3 * requestWords + 3 * replyWords + 1 := by
  simp [exchangeTime, Costs.unit, CostModel.unit]
  omega

theorem exchange_descriptionWords (requestWords replyWords : Nat) :
    (exchange (w := w) requestWords replyWords).descriptionWords = 13 * requestWords + 8 * replyWords + 12 := by
  have hs := send_descriptionWords (w := w) 0 0 requestWords
  have hr := receive_descriptionWords (w := w) 0 replyWords
  simp only [Code.descriptionWords] at *
  simp only [exchange, Code.description, description, List.length_cons, List.length_append, List.length_nil]
  omega

theorem exchange_descriptionFits (requestWords replyWords : Nat) (hw : 16 < 2 ^ w)
    (fits : replyWords < 2 ^ w) : (exchange (w := w) requestWords replyWords).DescriptionFits := by
  have hs := send_descriptionFits (w := w) 0 0 requestWords hw (by omega)
  have hr := receive_descriptionFits (w := w) 0 replyWords hw (by omega)
  intro token member
  simp only [exchange, Code.description, description, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false, or_assoc] at member
  rcases member with rfl | member | rfl | rfl | rfl | rfl | rfl | rfl | rfl | member <;>
    first | omega | exact hs token member | exact hr token member

theorem exchange_frame {cost : Costs} {tape : RandomTape w} {requestWords replyWords : Nat}
    {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    (execution : Exec cost tape (exchange requestWords replyWords) before after trace time net peak) :
    (∀ buffer, buffer ≠ 0 → after.bufs buffer = before.bufs buffer ∧ after.caps buffer = before.caps buffer) ∧
    after.regs 0 = before.regs 0 ∧ after.tapePos = before.tapePos := by
  refine ⟨?_, ?_, ?_⟩
  · intro buffer distinct
    apply execution.frame_buf
    simp only [exchange, Code.Touches, Stmt.Touches, false_or]
    rintro (sent | allocated | received)
    · exact send_touches 0 0 requestWords buffer sent
    · exact distinct allocated
    · exact distinct (receive_touches 0 replyWords buffer received)
  · apply execution.frame_reg
    simp [exchange, Code.Writes, Stmt.Writes, send_preserves_zero, receive_preserves_zero]
  · apply execution.tapePos_eq
    simp [exchange, Code.RandomFree, Stmt.RandomFree, send_randomFree, receive_randomFree]

/-- For each actual reply packet, the boundary yields its represented value and
an exact request/reply trace. The oracle supplies the reply words; the local
program allocates and stores every one of them, with the full cost below. -/
theorem exchange_exec {A B : Type} (cost : Costs) (tape : RandomTape w)
    (request : Representation w A) (reply : Representation w B) (value : A) (answer : B)
    (before : State w) (represented : request.Holds value before) :
    ∃ after, Exec cost tape (exchange request.encoding.words reply.encoding.words) before after
      ((request.encoding.encode value).map Event.output ++ .invoke :: (reply.encoding.encode answer).map Event.input)
      (exchangeTime cost request.encoding.words reply.encoding.words)
      ((reply.encoding.words : Int) - before.caps 0) (max ((reply.encoding.words : Int) - before.caps 0) 0) ∧
      reply.Holds answer after := by
  have size := Assembly.represented_size request represented
  obtain ⟨sent, sending, bufs, caps⟩ := send_exec cost tape 0 request.encoding.words 0 before
    (by omega) (by simpa [size] using request.fits)
  have sending' : Exec cost tape (send 0 0 request.encoding.words) before sent
      ((request.encoding.encode value).map Event.output)
      (request.encoding.words * (cost.machine.imm + cost.machine.memLoad + cost.write)) 0 0 := by
    simpa only [List.drop_zero, represented.2.1, ← request.encoding.encode_length value,
      List.take_length] using sending
  let allocated := sent.allocBuf 0 reply.encoding.words
  obtain ⟨after, receiving, contents, capacities⟩ :=
    receive_exec cost tape 0 (reply.encoding.encode answer) allocated (by
      simp [allocated, State.allocBuf, reply.encoding.encode_length])
  have allocation : Exec cost tape (.compute (.memAllocI 0 reply.encoding.words)) sent allocated []
      (cost.machine.memAlloc + reply.encoding.words * cost.machine.allocPerWord)
      ((reply.encoding.words : Int) - before.caps 0) (max ((reply.encoding.words : Int) - before.caps 0) 0) := by
    simpa [caps] using (Exec.compute (Caliper.Exec.memAllocI (s := sent) (b := 0) (n := reply.encoding.words)))
  have joined := Exec.seq sending' (Exec.seq Exec.invoke (Exec.seq allocation receiving))
  have execution : Exec cost tape (exchange request.encoding.words reply.encoding.words) before after
      ((request.encoding.encode value).map Event.output ++ .invoke :: (reply.encoding.encode answer).map Event.input)
      (exchangeTime cost request.encoding.words reply.encoding.words)
      ((reply.encoding.words : Int) - before.caps 0) (max ((reply.encoding.words : Int) - before.caps 0) 0) := by
    simpa [exchange, exchangeTime, reply.encoding.encode_length, Nat.add_assoc,
      max_eq_left (le_max_left ((reply.encoding.words : Int) - before.caps 0) 0),
      max_eq_right (le_max_right ((reply.encoding.words : Int) - before.caps 0) 0)] using joined
  refine ⟨after, execution, (exchange_frame execution).2.1.trans represented.1, ?_,
    execution.wellFormed_preserved represented.2.2.1, ?_⟩
  · simpa [allocated, State.allocBuf] using contents
  · intro buffer
    rw [capacities]
    by_cases zero : buffer = 0
    · simpa [allocated, State.allocBuf, zero] using reply.fits
    · simpa [allocated, State.allocBuf, zero, caps] using represented.2.2.2 buffer

end Signatures.Runtime.CaliperBackend.WordIO

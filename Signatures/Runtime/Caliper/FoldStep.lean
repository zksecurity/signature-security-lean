import Signatures.Runtime.Caliper.ListFoldBounds

/-! One executed fold stage. The accumulator may change representation and
width across the body call. Empty input executes the supplied final conversion;
nonempty input executes preparation, the body, restoration and the next stage. -/

namespace Signatures.Runtime.CaliperBackend.FoldStep

open Caliper Assembly

variable {w : Nat} {A B D E R : Type}

def code (body following stop : Stmt w) (buffer entry state next env capacity : Nat) : Stmt w :=
  .memLoad 1 0 0 ;; .ifNZ 1
    (ListFold.prepare entry state env capacity ;;
      Retain.code body buffer (entry + (state + env)) next (1 + capacity * entry + env) ;;
      Assembly.code (Reorder.operands next (1 + capacity * entry) env) ;;
      following)
    (selectSlice (1 + (capacity + 1) * entry) state ;; stop)

def result {capacity : Nat} (body : A × (B × E) → D) (following : BoundedList A capacity × (D × E) → R)
    (stop : B → R) (value : BoundedList A (capacity + 1) × (B × E)) : R :=
  match value.1 with
  | ⟨[], _⟩ => stop value.2.1
  | ⟨head :: tail, valid⟩ => following (⟨tail, by simpa using valid⟩, body (head, value.2.1, value.2.2), value.2.2)

def time {capacity : Nat} (cost : CostModel) (body : A × (B × E) → D) (bodyTime : A × (B × E) → Nat)
    (followingTime : BoundedList A capacity × (D × E) → Nat) (stopTime : B → Nat)
    (buffer entry state next env : Nat) (value : BoundedList A (capacity + 1) × (B × E)) : Nat :=
  match value.1 with
  | ⟨[], _⟩ => cost.memLoad + (cost.branch +
      ((selectSlice (w := w) (1 + (capacity + 1) * entry) state).staticTime cost + stopTime value.2.1))
  | ⟨head :: tail, valid⟩ => cost.memLoad + (cost.branch +
      ((ListFold.prepare (w := w) entry state env capacity).staticTime cost +
        (ListFold.callerTime (w := w) cost buffer (entry + (state + env)) next (1 + capacity * entry + env)
          (bodyTime (head, value.2.1, value.2.2)) +
          ((Assembly.code (Reorder.operands (w := w) next (1 + capacity * entry) env)).staticTime cost +
            followingTime (⟨tail, by simpa using valid⟩, body (head, value.2.1, value.2.2), value.2.2)))))

variable (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (state : Representation w B) (next : Representation w D)
    (env : Representation w E) (output : Representation w R) (capacity : Nat)
    (hw : 16 < 2 ^ w) (countFits : capacity + 1 < 2 ^ w)
    (argFits : entry.encoding.words + state.encoding.words + env.encoding.words < 2 ^ w)
    (inputFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w)
    (nextFits : 1 + capacity * entry.encoding.words + next.encoding.words + 2 * env.encoding.words < 2 ^ w)
    {f : A × (B × E) → D} {g : BoundedList A capacity × (D × E) → R} {h : B → R}
    (body : Realizer cost (ListFold.argument entry state env argFits) next f)
    (following : Realizer cost (ListFold.frame entry next env capacity (by omega) nextFits) output g)
    (stop : Realizer cost state output h) (nameFits : body.savedBuffer < 2 ^ w)

include allocation hw nameFits in
theorem exec (tape : RandomTape w) (value : BoundedList A (capacity + 1) × (B × E)) (before : State w)
    (represented : (ListFold.frame entry state env (capacity + 1) countFits inputFits).Holds value before) :
    ∃ after net peak,
      Caliper.Exec cost tape
        (code body.code following.code stop.code body.savedBuffer entry.encoding.words state.encoding.words next.encoding.words env.encoding.words capacity)
        before after (time (w := w) cost f body.time following.time stop.time body.savedBuffer entry.encoding.words state.encoding.words
          next.encoding.words env.encoding.words value) net peak ∧
      output.Holds (result f g h value) after := by
  rcases value with ⟨⟨values, valid⟩, accumulator, context⟩
  have smallerCount : capacity < 2 ^ w := by omega
  have contents : (before.bufs 0).toList = BitVec.ofNat w values.length ::
      (entry.encoding.pack values ++ List.replicate (((capacity + 1) - values.length) * entry.encoding.words) 0) ++
      (state.encoding.encode accumulator ++ env.encoding.encode context) := represented.2.1
  have loaded := Dispatch.load_tag cost tape (BitVec.ofNat w values.length) _ before represented.1 contents
  cases values with
  | nil =>
    have input : (ListFold.frame entry state env (capacity + 1) countFits inputFits).Holds (⟨[], valid⟩, accumulator, context)
        (before.setReg 1 0) :=
      ⟨represented.1, represented.2.1, loaded.wellFormed_preserved represented.2.2.1, represented.2.2.2⟩
    let finish := (ListFold.finish cost allocation entry state env (capacity + 1) hw countFits inputFits).then stop
    obtain ⟨after, net, peak, called, outputValue, _, _⟩ := finish.correct tape _ _ input
    have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_false (c := 1)
      (thn := ListFold.prepare entry.encoding.words state.encoding.words env.encoding.words capacity ;;
        Retain.code body.code body.savedBuffer (entry.encoding.words + (state.encoding.words + env.encoding.words))
          next.encoding.words (1 + capacity * entry.encoding.words + env.encoding.words) ;;
        Assembly.code (Reorder.operands next.encoding.words (1 + capacity * entry.encoding.words) env.encoding.words) ;;
        following.code) (by simp) called)
    exact ⟨after, _, _, execution, outputValue⟩
  | cons head tail =>
    have tailValid : tail.length ≤ capacity := by simpa using valid
    let tailValue : BoundedList A capacity := ⟨tail, tailValid⟩
    let payload := entry.encoding.pack tail ++ List.replicate ((capacity - tail.length) * entry.encoding.words) 0
    have payloadSize : payload.length = capacity * (entry.encoding.encode head).length := by
      simp only [payload, List.length_append, Encoding.pack_length, List.length_replicate, entry.encoding.encode_length]
      rw [← Nat.add_mul, Nat.add_sub_of_le tailValid]
    have stored : ((before.setReg 1 (BitVec.ofNat w (head :: tail).length)).bufs 0).toList =
        BitVec.ofNat w (tail.length + 1) :: (entry.encoding.encode head ++ payload ++
          state.encoding.encode accumulator ++ env.encoding.encode context) := by
      simpa [Encoding.pack, payload, List.append_assoc] using contents
    obtain ⟨prepared, elapsed, net, peak, preparedExec, preparedBytes, preparedZero, preparedCaps⟩ :=
      ListFold.prepare_exec cost tape (entry.encoding.encode head) payload (state.encoding.encode accumulator)
        (env.encoding.encode context) tail.length capacity payloadSize _ stored
        (by simpa [ListFold.prepareWords, entry.encoding.encode_length, state.encoding.encode_length, env.encoding.encode_length] using inputFits)
        represented.2.2.2
    rw [entry.encoding.encode_length, state.encoding.encode_length, env.encoding.encode_length] at preparedExec
    have preparedTime := preparedExec.straight_time_eq (ListFold.prepare_straight _ _ _ _)
    subst elapsed
    let savedRep := ListFold.saved entry env capacity smallerCount (by nlinarith)
    have argumentSize : (ListFold.argument entry state env argFits).encoding.words = entry.encoding.words + (state.encoding.words + env.encoding.words) := rfl
    have savedSize : savedRep.encoding.words = 1 + capacity * entry.encoding.words + env.encoding.words := rfl
    have inFits : (ListFold.argument entry state env argFits).encoding.words + savedRep.encoding.words < 2 ^ w := by
      rw [argumentSize, savedSize]; nlinarith
    have outFits : next.encoding.words + savedRep.encoding.words < 2 ^ w := by rw [savedSize]; nlinarith
    let retained := body.retain allocation savedRep hw nameFits inFits outFits
    have preparedInput : ((ListFold.argument entry state env argFits).prod savedRep inFits).Holds
        ((head, accumulator, context), (tailValue, context)) prepared := by
      refine ⟨preparedZero.trans represented.1, ?_, preparedExec.wellFormed_preserved
        (loaded.wellFormed_preserved represented.2.2.1), preparedCaps⟩
      simpa [ListFold.argument, savedRep, ListFold.saved, Representation.prod, Representation.boundedList,
        Encoding.prod, Encoding.boundedList, Encoding.checked, payload, tailValue, List.append_assoc] using preparedBytes
    obtain ⟨called, callNet, callPeak, callExec, callOutput, _, _⟩ := retained.correct tape _ prepared preparedInput
    let listRep := entry.boundedList capacity smallerCount (by nlinarith)
    let restored := Reorder.realizer cost allocation next listRep env hw (by
      change next.encoding.words + (1 + capacity * entry.encoding.words) + env.encoding.words < 2 ^ w
      nlinarith)
    obtain ⟨continued, restoreNet, restorePeak, restoreExec, restoreOutput, _, _⟩ := restored.correct tape _ called callOutput
    obtain ⟨after, finalNet, finalPeak, followingExec, outputValue, _, _⟩ := following.correct tape
      (tailValue, f (head, accumulator, context), context) continued restoreOutput
    have nonzero : BitVec.ofNat w (head :: tail).length ≠ 0 := by
      have fits : (head :: tail).length < 2 ^ w := valid.trans_lt countFits
      intro equal
      have natural := congrArg BitVec.toNat equal
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at natural
      simp at natural
    have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_true (c := 1)
      (els := selectSlice (1 + (capacity + 1) * entry.encoding.words) state.encoding.words ;; stop.code)
      (by simpa using nonzero) (Caliper.Exec.seq preparedExec (Caliper.Exec.seq callExec (Caliper.Exec.seq restoreExec followingExec))))
    refine ⟨after, 0 + (net + (callNet + (restoreNet + finalNet))),
      max 0 (0 + max peak (net + max callPeak (callNet + max restorePeak (restoreNet + finalPeak)))), ?_, outputValue⟩
    simpa only [code, time, ListFold.callerTime, retained, Realizer.retain, argumentSize, savedSize,
      restored, Reorder.realizer, Assembly.realizer, ListFold.argument, savedRep, ListFold.saved, listRep,
      Representation.prod, Representation.boundedList, Encoding.prod, Encoding.boundedList, Encoding.checked] using execution

end Signatures.Runtime.CaliperBackend.FoldStep

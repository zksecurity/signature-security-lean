import Proofs.Runtime.Caliper.Reorder
import Proofs.Runtime.Caliper.Retain

/-! A list fold implemented by Caliper instructions. The maximum capacity bounds
the generated code, while the stored length controls calls to the compiled body.
The remaining list and environment are copied and retained across each call. -/

namespace Signatures.Runtime.CaliperBackend.ListFold

open Caliper Assembly

variable {w : Nat} {A B E : Type}

def argument (entry : Representation w A) (state : Representation w B) (env : Representation w E)
    (fits : entry.encoding.words + state.encoding.words + env.encoding.words < 2 ^ w) : Representation w (A × (B × E)) :=
  entry.prod (state.prod env (by omega)) (by change entry.encoding.words + (state.encoding.words + env.encoding.words) < 2 ^ w; omega)

def frame (entry : Representation w A) (state : Representation w B) (env : Representation w E)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w) :
    Representation w (BoundedList A capacity × (B × E)) :=
  (entry.boundedList capacity countFits (by omega)).prod (state.prod env (by omega))
    (by change (1 + capacity * entry.encoding.words) + (state.encoding.words + env.encoding.words) < 2 ^ w; omega)

def saved (entry : Representation w A) (env : Representation w E) (capacity : Nat)
    (countFits : capacity < 2 ^ w) (fits : 1 + capacity * entry.encoding.words + env.encoding.words < 2 ^ w) :
    Representation w (BoundedList A capacity × E) :=
  (entry.boundedList capacity countFits (by omega)).prod env fits

def code (body : Stmt w) (buffer entry state env : Nat) : Nat → Stmt w
  | 0 => selectSlice 1 state
  | capacity + 1 => .memLoad 1 0 0 ;; .ifNZ 1
      (prepare entry state env capacity ;;
        Retain.code body buffer (entry + (state + env)) state (1 + capacity * entry + env) ;;
        Assembly.code (Reorder.operands state (1 + capacity * entry) env) ;;
        code body buffer entry state env capacity)
      (selectSlice (1 + (capacity + 1) * entry) state)

def callerTime (cost : CostModel) (buffer input output saved body : Nat) : Nat :=
  (Retain.save (w := w) buffer input saved).staticTime cost +
    ((selectSlice (w := w) 0 input).staticTime cost +
      (body + ((Assembly.code (Retain.restoreOperands (w := w) buffer output saved)).staticTime cost + cost.memFree)))

def time (cost : CostModel) (body : A × (B × E) → B) (bodyTime : A × (B × E) → Nat)
    (buffer entry state env : Nat) : Nat → List A → B → E → Nat
  | 0, _, _, _ => (selectSlice (w := w) 1 state).staticTime cost
  | capacity + 1, [], _, _ => cost.memLoad + (cost.branch +
      (selectSlice (w := w) (1 + (capacity + 1) * entry) state).staticTime cost)
  | capacity + 1, head :: tail, value, context => cost.memLoad + (cost.branch +
      ((prepare (w := w) entry state env capacity).staticTime cost +
        (callerTime (w := w) cost buffer (entry + (state + env)) state (1 + capacity * entry + env) (bodyTime (head, value, context)) +
          ((Assembly.code (Reorder.operands (w := w) state (1 + capacity * entry) env)).staticTime cost +
            time cost body bodyTime buffer entry state env capacity tail (body (head, value, context)) context))))

def denote (body : A × (B × E) → B) {capacity : Nat} (value : BoundedList A capacity × (B × E)) : B :=
  value.1.val.foldl (fun accumulator head => body (head, accumulator, value.2.2)) value.2.1

def finish (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (state : Representation w B) (env : Representation w E)
    (capacity : Nat) (hw : 16 < 2 ^ w) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w) :
    Realizer cost (frame entry state env capacity countFits fits) state (fun value => value.2.1) :=
  selectSliceRealizer cost allocation _ _ _ (1 + capacity * entry.encoding.words) hw
    (by change 1 + capacity * entry.encoding.words + state.encoding.words ≤
      (1 + capacity * entry.encoding.words) + (state.encoding.words + env.encoding.words); omega)
    (by
      intro value
      change (((entry.boundedList capacity countFits (by omega)).encoding.encode value.1 ++
        (state.encoding.encode value.2.1 ++ env.encoding.encode value.2.2)).drop (1 + capacity * entry.encoding.words)).take state.encoding.words = _
      have size : ((entry.boundedList capacity countFits (by omega)).encoding.encode value.1).length =
          1 + capacity * entry.encoding.words := (entry.boundedList capacity countFits (by omega)).encoding.encode_length value.1
      simpa only [size, state.encoding.encode_length] using
        (show (((entry.boundedList capacity countFits (by omega)).encoding.encode value.1 ++
          (state.encoding.encode value.2.1 ++ env.encoding.encode value.2.2)).drop
          ((entry.boundedList capacity countFits (by omega)).encoding.encode value.1).length).take
          (state.encoding.encode value.2.1).length = state.encoding.encode value.2.1 by simp))

variable (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (state : Representation w B) (env : Representation w E)
    (argFits : entry.encoding.words + state.encoding.words + env.encoding.words < 2 ^ w)
    (hw : 16 < 2 ^ w) {f : A × (B × E) → B}
    (body : Realizer cost (argument entry state env argFits) state f)
    (nameFits : body.savedBuffer < 2 ^ w)

include allocation hw nameFits in
theorem exec (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w)
    (tape : RandomTape w) (value : BoundedList A capacity × (B × E)) (before : State w)
    (represented : (frame entry state env capacity countFits storageFits).Holds value before) :
    ∃ after net peak,
      Caliper.Exec cost tape (code body.code body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity)
        before after (time (w := w) cost f body.time body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity value.1.val value.2.1 value.2.2) net peak ∧
      state.Holds (denote f value) after := by
  induction capacity generalizing before with
  | zero =>
    have empty : value.1.val = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero value.1.property)
    obtain ⟨after, net, peak, execution, result, _, _⟩ :=
      (finish cost allocation entry state env 0 hw countFits storageFits).correct tape value before represented
    refine ⟨after, net, peak, ?_, ?_⟩
    · simpa [finish, selectSliceRealizer, code, time] using execution
    · simpa [denote, empty] using result
  | succ capacity ih =>
    rcases value with ⟨⟨values, valid⟩, accumulator, context⟩
    have smallerCount : capacity < 2 ^ w := by omega
    have smallerStorage : 1 + capacity * entry.encoding.words + state.encoding.words + 2 * env.encoding.words < 2 ^ w := by nlinarith
    have contents : (before.bufs 0).toList = BitVec.ofNat w values.length ::
        (entry.encoding.pack values ++ List.replicate (((capacity + 1) - values.length) * entry.encoding.words) 0) ++
        (state.encoding.encode accumulator ++ env.encoding.encode context) := represented.2.1
    have loaded := Dispatch.load_tag cost tape (BitVec.ofNat w values.length) _ before represented.1 contents
    cases values with
    | nil =>
      have input : (frame entry state env (capacity + 1) countFits storageFits).Holds (⟨[], valid⟩, accumulator, context)
          (before.setReg 1 0) :=
        ⟨represented.1, represented.2.1, loaded.wellFormed_preserved represented.2.2.1, represented.2.2.2⟩
      obtain ⟨after, net, peak, called, result, _, _⟩ :=
        (finish cost allocation entry state env (capacity + 1) hw countFits storageFits).correct tape _ _ input
      have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_false (c := 1)
        (thn := prepare entry.encoding.words state.encoding.words env.encoding.words capacity ;;
          Retain.code body.code body.savedBuffer (entry.encoding.words + (state.encoding.words + env.encoding.words))
            state.encoding.words (1 + capacity * entry.encoding.words + env.encoding.words) ;;
          Assembly.code (Reorder.operands state.encoding.words (1 + capacity * entry.encoding.words) env.encoding.words) ;;
          code body.code body.savedBuffer entry.encoding.words state.encoding.words env.encoding.words capacity) (by simp) called)
      exact ⟨after, _, _, execution, result⟩
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
        prepare_exec cost tape (entry.encoding.encode head) payload (state.encoding.encode accumulator)
          (env.encoding.encode context) tail.length capacity payloadSize _ stored
          (by simpa [prepareWords, entry.encoding.encode_length, state.encoding.encode_length, env.encoding.encode_length] using storageFits)
          represented.2.2.2
      rw [entry.encoding.encode_length, state.encoding.encode_length, env.encoding.encode_length] at preparedExec
      have preparedTime := preparedExec.straight_time_eq (prepare_straight _ _ _ _)
      subst elapsed
      let savedRep := saved entry env capacity smallerCount (by nlinarith)
      have argumentSize : (argument entry state env argFits).encoding.words = entry.encoding.words + (state.encoding.words + env.encoding.words) := rfl
      have savedSize : savedRep.encoding.words = 1 + capacity * entry.encoding.words + env.encoding.words := rfl
      have inFits : (argument entry state env argFits).encoding.words + savedRep.encoding.words < 2 ^ w := by
        rw [argumentSize, savedSize]; nlinarith
      have outFits : state.encoding.words + savedRep.encoding.words < 2 ^ w := by rw [savedSize]; nlinarith
      let retained := body.retain allocation savedRep hw nameFits inFits outFits
      have preparedInput : ((argument entry state env argFits).prod savedRep inFits).Holds
          ((head, accumulator, context), (tailValue, context)) prepared := by
        refine ⟨preparedZero.trans represented.1, ?_, preparedExec.wellFormed_preserved
          (loaded.wellFormed_preserved represented.2.2.1), preparedCaps⟩
        simpa [argument, savedRep, saved, Representation.prod, Representation.boundedList,
          Encoding.prod, Encoding.boundedList, Encoding.checked, payload, tailValue, List.append_assoc] using preparedBytes
      obtain ⟨called, callNet, callPeak, callExec, callOutput, _, _⟩ := retained.correct tape _ prepared preparedInput
      let listRep := entry.boundedList capacity smallerCount (by nlinarith)
      let restored := Reorder.realizer cost allocation state listRep env hw (by
        change state.encoding.words + (1 + capacity * entry.encoding.words) + env.encoding.words < 2 ^ w
        nlinarith)
      obtain ⟨next, restoreNet, restorePeak, restoreExec, restoreOutput, _, _⟩ := restored.correct tape _ called callOutput
      obtain ⟨after, finalNet, finalPeak, following, result⟩ := ih smallerCount smallerStorage
        (tailValue, f (head, accumulator, context), context) next restoreOutput
      have nonzero : BitVec.ofNat w (head :: tail).length ≠ 0 := by
        have fits : (head :: tail).length < 2 ^ w := valid.trans_lt countFits
        intro equal
        have natural := congrArg BitVec.toNat equal
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at natural
        simp at natural
      have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_true (c := 1)
        (els := selectSlice (1 + (capacity + 1) * entry.encoding.words) state.encoding.words)
        (by simpa using nonzero) (Caliper.Exec.seq preparedExec (Caliper.Exec.seq callExec (Caliper.Exec.seq restoreExec following))))
      refine ⟨after, 0 + (net + (callNet + (restoreNet + finalNet))),
        max 0 (0 + max peak (net + max callPeak (callNet + max restorePeak (restoreNet + finalPeak)))), ?_, result⟩
      simpa only [code, time, callerTime, retained, Realizer.retain, argumentSize, savedSize,
        restored, Reorder.realizer, Assembly.realizer, argument, savedRep, saved, listRep,
        Representation.prod, Representation.boundedList, Encoding.prod, Encoding.boundedList, Encoding.checked] using execution

end Signatures.Runtime.CaliperBackend.ListFold

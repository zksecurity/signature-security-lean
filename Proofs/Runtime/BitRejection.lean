import Proofs.Runtime.HeapLoop
import Proofs.Runtime.RejectionSampling
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! Bounded rejection with bit-list control and explicit cell costs. The only
random instruction is one fair bit; word width and retry fuel are static unary
code. Numeric decoding occurs in specifications, never in the executable test.
Costs below include one step per bit draw, not an arbitrary coin implementation. -/

namespace Signatures.Runtime.BitRejection

open HeapBits SharedHeap PrimeFieldCircuit OracleComp

/-- Compare equal-width little-endian words, inspecting their high bits first. -/
def compare : List Bool → List Bool → Run Ordering
  | [], [] => ⟨.eq, 1⟩
  | x :: xs, y :: ys =>
    let r := compare xs ys
    ⟨match r.value with
      | .eq => if x == y then .eq else if x then .gt else .lt
      | c => c, r.steps + 4⟩
  | [], _ :: _ => ⟨.lt, 1⟩
  | _ :: _, [] => ⟨.gt, 1⟩

theorem compare_steps (xs ys : List Bool) (h : xs.length = ys.length) :
    (compare xs ys).steps = 4*xs.length+1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [compare]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have ht := ih ys (by simpa using h)
      simp only [compare, List.length_cons]
      omega

theorem compare_spec (xs ys : List Bool) (h : xs.length = ys.length) :
    match (compare xs ys).value with
    | .lt => exponent xs < exponent ys
    | .eq => exponent xs = exponent ys
    | .gt => exponent ys < exponent xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [compare, exponent]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have ht := ih ys (by simpa using h)
      cases hc : (compare xs ys).value <;>
        cases x <;> cases y <;> simp_all [compare, exponent] <;> omega

theorem exponent_lt (xs : List Bool) : exponent xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih => cases b <;> simp only [exponent, List.length_cons, Nat.pow_succ,
      Bool.toNat_false, Bool.toNat_true] <;> omega

theorem exponent_injective (xs ys : List Bool)
    (hl : xs.length = ys.length) (he : exponent xs = exponent ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hl.symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      cases x <;> cases y <;> simp only [exponent, Bool.toNat_false, Bool.toNat_true] at he
      · exact congrArg (false :: ·) (ih ys hl' (by omega))
      · omega
      · omega
      · exact congrArg (true :: ·) (ih ys hl' (by omega))

structure Code where
  width : List Unit
  limit : Option (List Bool)
  attempts : List Unit
  deriving Repr

/-- A full-width modulus accepts every word; it must not be truncated to zero. -/
def compile (n w k : Nat) : Code :=
  ⟨List.replicate w (), if n < 2^w then some (natBits w n) else none, List.replicate k ()⟩

def accepts (limit : Option (List Bool)) (word : List Bool) : Run Bool :=
  match limit with
  | none => ⟨true, 1⟩
  | some bound => let c := compare word bound; ⟨c.value == .lt, c.steps+1⟩

theorem accepts_compile (n w k : Nat) (word : List Bool) (hw : word.length = w) :
    (accepts (compile n w k).limit word).value = decide (exponent word < n) ∧
    (accepts (compile n w k).limit word).steps ≤ 4*w+2 := by
  by_cases hn : n < 2^w
  · simp only [compile, hn, ite_true, accepts]
    have hlen : word.length = (natBits w n).length := by simp [natBits, hw]
    have hc := compare_spec word (natBits w n) hlen
    have hs := compare_steps word (natBits w n) hlen
    rw [HeapLoop.exponent_natBits w n hn] at hc
    cases hcmp : (compare word (natBits w n)).value <;> simp_all
    omega
  · have hx := exponent_lt word
    rw [hw] at hx
    have hxn : exponent word < n := by omega
    simp [compile, hn, accepts, hxn]

variable {m : Type → Type} [Monad m]

/-- The `coin` argument is a single-bit instruction, priced at one cell step. -/
def drawWord (coin : m Bool) : List Unit → m (Run (List Bool))
  | [] => pure ⟨[], 1⟩
  | _ :: width => do
    let b ← coin
    let tail ← drawWord coin width
    pure ⟨b :: tail.value, tail.steps+4⟩

def run (coin : m Bool) (width : List Unit) (limit : Option (List Bool)) :
    List Unit → m (Run (Option (List Bool)))
  | [] => pure ⟨none, 1⟩
  | _ :: fuel => do
    let word ← drawWord coin width
    let test := accepts limit word.value
    if test.value then
      let out := copy word.value
      pure ⟨some out.value, word.steps+test.steps+out.steps+2⟩
    else
      let out ← run coin width limit fuel
      pure ⟨out.value, word.steps+test.steps+out.steps+2⟩

abbrev bitSpec : OracleSpec Unit := fun _ => Bool

open scoped OracleSpec.PrimitiveQuery in
def execute (code : Code) : OracleComp bitSpec (Run (Option (List Bool))) :=
  run (liftM (bitSpec.query ())) code.width code.limit code.attempts

theorem drawWord_support {I : Type} {spec : OracleSpec I} (coin : OracleComp spec Bool)
    (width : List Unit) (out : Run (List Bool)) (hout : out ∈ support (drawWord coin width)) :
    out.value.length = width.length ∧ out.steps = 4*width.length+1 := by
  induction width generalizing out with
  | nil =>
    simp only [drawWord, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact ⟨rfl, rfl⟩
  | cons u width ih =>
    simp only [drawWord, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
    obtain ⟨b, _, tail, ht, rfl⟩ := hout
    have h := ih tail ht
    simp only [List.length_cons]
    exact ⟨by omega, by omega⟩

/-- Every path terminates within the CPU bound, including exhaustion and success
on the final attempt. Width is independent of how soon the sampler accepts. -/
theorem run_support {I : Type} {spec : OracleSpec I} (coin : OracleComp spec Bool)
    (n w k : Nat) (fuel : List Unit) (out : Run (Option (List Bool)))
    (hout : out ∈ support (run coin (List.replicate w ()) (compile n w k).limit fuel)) :
    (∀ word, out.value = some word → word.length = w ∧ exponent word < n) ∧
    out.steps ≤ fuel.length*(10*w+6)+1 := by
  induction fuel generalizing out with
  | nil =>
    simp only [run, support_pure, Set.mem_singleton_iff] at hout
    subst out
    simp
  | cons u fuel ih =>
    simp only [run, mem_support_bind_iff] at hout
    obtain ⟨word, hword, hout⟩ := hout
    have hw := drawWord_support coin _ word hword
    simp only [List.length_replicate] at hw
    have ht := accepts_compile n w k word.value hw.1
    split at hout
    · rename_i hyes
      simp only [support_pure, Set.mem_singleton_iff] at hout
      subst out
      constructor
      · intro xs hx
        simp only [copy_value, Option.some.injEq] at hx
        subst xs
        exact ⟨hw.1, of_decide_eq_true (ht.1.symm.trans hyes)⟩
      · simp only [copy_steps, List.length_cons]
        nlinarith
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
      obtain ⟨last, hlast, rfl⟩ := hout
      have h := ih last hlast
      constructor
      · exact h.1
      · simp only [List.length_cons]
        nlinarith

theorem execute_steps (n w k : Nat) (out : Run (Option (List Bool)))
    (hout : out ∈ support (execute (compile n w k))) : out.steps ≤ k*(10*w+6)+1 := by
  have h := run_support (liftM (bitSpec.query ())) n w k (List.replicate k ()) out hout
  simpa using h.2

theorem simulateQ_drawWord {I : Type} {spec : OracleSpec I} [LawfulMonad m]
    (impl : QueryImpl spec m) (coin : OracleComp spec Bool) (width : List Unit) :
    simulateQ impl (drawWord coin width) = drawWord (simulateQ impl coin) width := by
  induction width with
  | nil => rfl
  | cons u width ih => simp only [drawWord, simulateQ_bind, simulateQ_pure, ih]

theorem simulateQ_run {I : Type} {spec : OracleSpec I} [LawfulMonad m]
    (impl : QueryImpl spec m) (coin : OracleComp spec Bool)
    (width fuel : List Unit) (limit : Option (List Bool)) :
    simulateQ impl (run coin width limit fuel) = run (simulateQ impl coin) width limit fuel := by
  induction fuel with
  | nil => rfl
  | cons u fuel ih =>
    simp only [run, simulateQ_bind, simulateQ_drawWord]
    congr 1
    funext word
    split <;> simp only [simulateQ_pure, simulateQ_bind, ih]

theorem drawWord_queries {I : Type} {spec : OracleSpec I} (coin : OracleComp spec Bool)
    (hc : IsQueryBoundP coin (fun _ => True) 1) (width : List Unit) :
    IsQueryBoundP (drawWord coin width) (fun _ => True) width.length := by
  induction width with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons u width ih =>
    have h := isQueryBoundP_bind hc (fun b _ =>
      isQueryBoundP_bind ih (fun tail _ =>
        isQueryBoundP_pure (fun _ => True) (⟨b :: tail.value, tail.steps+4⟩ : Run (List Bool)) 0))
    simpa only [drawWord, List.length_cons, Nat.add_zero, Nat.add_comm] using h

theorem run_queries {I : Type} {spec : OracleSpec I} (coin : OracleComp spec Bool)
    (hc : IsQueryBoundP coin (fun _ => True) 1)
    (width fuel : List Unit) (limit : Option (List Bool)) :
    IsQueryBoundP (run coin width limit fuel) (fun _ => True) (fuel.length*width.length) := by
  induction fuel with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons u fuel ih =>
    have h : IsQueryBoundP (run coin width limit (u :: fuel)) (fun _ => True)
        (width.length+fuel.length*width.length) := by
      apply isQueryBoundP_bind (drawWord_queries coin hc width)
      intro word _
      dsimp only
      split
      · exact isQueryBoundP_pure _ _ _
      · simpa only [Nat.add_zero] using
          isQueryBoundP_bind ih (fun out _ => isQueryBoundP_pure (fun _ => True) _ 0)
    simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using h

theorem execute_queries (n w k : Nat) :
    IsQueryBoundP (execute (compile n w k)) (fun _ => True) (k*w) := by
  have hc : IsQueryBoundP (liftM (bitSpec.query ()) : OracleComp bitSpec Bool) (fun _ => True) 1 := by
    rw [isQueryBoundP_query_iff]
    intro _
    decide
  have h := run_queries (liftM (bitSpec.query ())) hc
    (List.replicate w ()) (List.replicate k ()) (compile n w k).limit
  simpa only [execute, compile, List.length_replicate] using h

def zeroWord : List Unit → Run (List Bool)
  | [] => ⟨[], 1⟩
  | _ :: width => let tail := zeroWord width; ⟨false :: tail.value, tail.steps+2⟩

theorem zeroWord_spec (width : List Unit) :
    (zeroWord width).value = natBits width.length 0 ∧ (zeroWord width).steps = 2*width.length+1 := by
  induction width with
  | nil => exact ⟨rfl, rfl⟩
  | cons u width ih =>
    simp only [zeroWord, List.length_cons]
    constructor
    · simp [ih.1, natBits, List.ofFn_succ]
    · omega

/-- Exhaustion returns zero and a true failure flag. The flag must be retained
by the machine; this is not an exactly uniform, non-aborting sampler. -/
def executeDefault (code : Code) : OracleComp bitSpec (Run (List Bool × Bool)) := do
  let out ← execute code
  match out.value with
  | some word => pure ⟨(word, false), out.steps+1⟩
  | none =>
    let zero := zeroWord code.width
    pure ⟨(zero.value, true), out.steps+zero.steps+1⟩

theorem executeDefault_support (n w k : Nat) (hn : 0 < n) (out : Run (List Bool × Bool))
    (hout : out ∈ support (executeDefault (compile n w k))) :
    out.value.1.length = w ∧ exponent out.value.1 < n ∧ out.steps ≤ k*(10*w+6)+2*w+3 := by
  simp only [executeDefault, mem_support_bind_iff] at hout
  obtain ⟨r, hr, hout⟩ := hout
  have h := run_support (liftM (bitSpec.query ())) n w k (List.replicate k ()) r hr
  simp only [List.length_replicate] at h
  cases hx : r.value with
  | none =>
    simp only [hx, support_pure, Set.mem_singleton_iff] at hout
    subst out
    have hz := zeroWord_spec (List.replicate w ())
    simp only [List.length_replicate] at hz
    simp only [compile, hz.1, hz.2]
    exact ⟨by simp [natBits], by simpa [HeapLoop.exponent_natBits _ _ (by positivity)] using hn, by omega⟩
  | some word =>
    simp only [hx, support_pure, Set.mem_singleton_iff] at hout
    subst out
    have hw := h.1 word hx
    exact ⟨hw.1, hw.2, by dsimp only; omega⟩

theorem executeDefault_queries (n w k : Nat) :
    IsQueryBoundP (executeDefault (compile n w k)) (fun _ => True) (k*w) := by
  have h : IsQueryBoundP (executeDefault (compile n w k)) (fun _ => True) (k*w+0) := by
    apply isQueryBoundP_bind (execute_queries n w k)
    intro out _
    cases out.value <;> exact isQueryBoundP_pure _ _ _
  simpa only [Nat.add_zero] using h

end Signatures.Runtime.BitRejection

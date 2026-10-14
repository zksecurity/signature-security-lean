import Signatures.Runtime.BitCircuit
import Signatures.Runtime.Language

/-! A cell-costed interpreter for compiled AIGs. Addresses in executable code
are unary lists, not unbounded integers with free arithmetic. Reads scan bit
lists, and appending a result explicitly copies the previous result list.
Every gate is evaluated once. This deliberately simple memory model gives a
quadratic bound; it is not a claim about Lean VM time or constant-time RAM.
Circuit construction and the surrounding cryptographic machine are separate. -/

namespace Signatures.Runtime.CircuitExecution

open Std.Sat

/-- One cell test at the end, and one step per address/data pair traversed. -/
def read : List Unit → List Bool → Run Bool
  | [], [] => ⟨false, 1⟩
  | [], b :: _ => ⟨b, 1⟩
  | _ :: _, [] => ⟨false, 1⟩
  | _ :: address, _ :: data =>
    let r := read address data
    ⟨r.value, r.steps + 1⟩

theorem read_value (address : List Unit) (data : List Bool) :
    (read address data).value = data[address.length]?.getD false := by
  induction address generalizing data with
  | nil => cases data <;> rfl
  | cons a address ih => cases data <;> simp [read, ih]

theorem read_steps (address : List Unit) (data : List Bool) :
    (read address data).steps ≤ address.length + 1 := by
  induction address generalizing data with
  | nil => cases data <;> simp [read]
  | cons a address ih =>
    cases data with
    | nil => simp [read]
    | cons b data => simpa [read, Nat.add_assoc] using Nat.add_le_add_right (ih data) 1

/-- Copy one existing bit cell per recursive call and append one new bit. -/
def snoc (b : Bool) : List Bool → Run (List Bool)
  | [] => ⟨[b], 1⟩
  | x :: xs =>
    let r := snoc b xs
    ⟨x :: r.value, r.steps + 2⟩

theorem snoc_value (b : Bool) (xs : List Bool) : (snoc b xs).value = xs ++ [b] := by
  induction xs <;> simp [snoc, *]

theorem snoc_steps (b : Bool) (xs : List Bool) : (snoc b xs).steps = 2 * xs.length + 1 := by
  induction xs <;> simp [snoc, *, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

inductive Instr where
  | zero
  | input (address : List Unit)
  | gate (left right : List Unit) (leftInvert rightInvert : Bool)
  deriving Repr

def Instr.eval (input memory : List Bool) : Instr → Run Bool
  | .zero => ⟨false, 1⟩
  | .input address =>
    let r := read address input
    ⟨r.value, r.steps + 1⟩
  | .gate left right li ri =>
    let l := read left memory
    let r := read right memory
    ⟨(l.value ^^ li) && (r.value ^^ ri), l.steps + r.steps + 4⟩

def Instr.Bounded (inputs nodes : Nat) : Instr → Prop
  | .zero => True
  | .input address => address.length ≤ inputs
  | .gate left right _ _ => left.length ≤ nodes ∧ right.length ≤ nodes

/-- Static code cells, including each unary address and complement bit. -/
def Instr.cells : Instr → Nat
  | .zero => 1
  | .input address => address.length + 1
  | .gate left right _ _ => left.length + right.length + 3

theorem Instr.cells_le (i : Instr) (m n : Nat) (h : i.Bounded m n) :
    i.cells ≤ 2 * n + m + 3 := by
  cases i <;> simp only [cells, Bounded] at * <;> omega

theorem Instr.eval_steps (input memory : List Bool) (i : Instr) (m n : Nat)
    (h : i.Bounded m n) : (i.eval input memory).steps ≤ 2 * n + m + 6 := by
  cases i with
  | zero => simp [Instr.eval]
  | input address =>
    have := read_steps address input
    simp only [Instr.eval]
    dsimp [Bounded] at h
    omega
  | gate left right li ri =>
    have hl := read_steps left memory
    have hr := read_steps right memory
    dsimp [Bounded] at h
    simp only [Instr.eval]
    omega

def step (input : List Bool) (i : Instr) (memory : List Bool) : Run (List Bool) :=
  let v := i.eval input memory
  let r := snoc v.value memory
  ⟨r.value, v.steps + r.steps⟩

theorem step_value (input : List Bool) (i : Instr) (memory : List Bool) :
    (step input i memory).value = memory ++ [(i.eval input memory).value] :=
  snoc_value _ _

theorem step_length (input : List Bool) (i : Instr) (memory : List Bool) :
    (step input i memory).value.length = memory.length + 1 := by
  simp [step_value]

def runFrom (input : List Bool) (code : List Instr) (memory : List Bool) : Run (List Bool) :=
  foldRun (step input) code memory

theorem runFrom_value (input : List Bool) (code : List Instr) (memory : List Bool) :
    (runFrom input code memory).value = code.foldl (fun mem i => (step input i mem).value) memory :=
  foldRun_value _ _ _

theorem runFrom_length (input : List Bool) (code : List Instr) (memory : List Bool) :
    (runFrom input code memory).value.length = memory.length + code.length := by
  induction code generalizing memory with
  | nil => simp [runFrom, foldRun]
  | cons i code ih =>
    simp only [runFrom, foldRun]
    change (runFrom input code (step input i memory).value).value.length = _
    rw [ih, step_length]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem runFrom_steps (input : List Bool) (code : List Instr) (memory : List Bool) (m n : Nat)
    (hc : ∀ i ∈ code, i.Bounded m n) (hm : memory.length + code.length ≤ n) :
    (runFrom input code memory).steps ≤ code.length * (4 * n + m + 10) + 1 := by
  induction code generalizing memory with
  | nil => simp [runFrom, foldRun]
  | cons i code ih =>
    have hs := Instr.eval_steps input memory i m n (hc i (by simp))
    have hn : (step input i memory).value.length + code.length ≤ n := by
      rw [step_length]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
    have ht := ih (step input i memory).value (fun j hj => hc j (by simp [hj])) hn
    have hm' : memory.length ≤ n := by simp only [List.length_cons] at hm; omega
    simp only [runFrom, foldRun]
    change (step input i memory).steps + (runFrom input code (step input i memory).value).steps + 3 ≤ _
    simp only [step, snoc_steps, List.length_cons]
    dsimp only [step] at ht
    nlinarith

/-- Static lowering replaces every node/input index by its unary address. -/
def compileDecl {m : Nat} : AIG.Decl (Fin m) → Instr
  | .false => .zero
  | .atom a => .input (List.replicate a.val ())
  | .gate l r => .gate (List.replicate l.gate ()) (List.replicate r.gate ()) l.invert r.invert

def compile {m : Nat} (aig : AIG (Fin m)) : List Instr := aig.decls.toList.map compileDecl

theorem compile_length {m : Nat} (aig : AIG (Fin m)) : (compile aig).length = aig.decls.size := by
  simp [compile]

theorem compile_bounded {m : Nat} (aig : AIG (Fin m)) :
    ∀ i ∈ compile aig, i.Bounded m aig.decls.size := by
  intro i hi
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
  obtain ⟨j, hj, hd⟩ := List.getElem_of_mem hd
  have hj' : j < aig.decls.size := by simpa using hj
  have he : aig.decls[j] = d := by simpa using hd
  cases d with
  | false => trivial
  | atom a => simp [compileDecl, Instr.Bounded, a.isLt.le]
  | gate l r =>
    have hb := aig.hdag hj' he
    simp only [compileDecl, Instr.Bounded, List.length_replicate]
    exact ⟨hb.1.le.trans hj'.le, hb.2.le.trans hj'.le⟩

theorem compile_cells {m : Nat} (aig : AIG (Fin m)) :
    ((compile aig).map Instr.cells).sum ≤ aig.decls.size * (2 * aig.decls.size + m + 3) := by
  have h (code : List Instr) (hc : ∀ i ∈ code, i.Bounded m aig.decls.size) :
      (code.map Instr.cells).sum ≤ code.length * (2 * aig.decls.size + m + 3) := by
    induction code with
    | nil => simp
    | cons i code ih =>
      have hi := Instr.cells_le i m aig.decls.size (hc i (by simp))
      have ht := ih (fun j hj => hc j (by simp [hj]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  simpa [compile_length] using h (compile aig) (compile_bounded aig)

/-- Compilation is static; `steps` counts execution of the resulting code. -/
def execute {m : Nat} (aig : AIG (Fin m)) (input : Vector Bool m) : Run (List Bool) :=
  runFrom input.toList (compile aig) []

theorem execute_length {m : Nat} (aig : AIG (Fin m)) (input : Vector Bool m) :
    (execute aig input).value.length = aig.decls.size := by
  simpa [execute, compile_length] using runFrom_length input.toList (compile aig) []

theorem execute_steps {m : Nat} (aig : AIG (Fin m)) (input : Vector Bool m) :
    (execute aig input).steps ≤ aig.decls.size * (4 * aig.decls.size + m + 10) + 1 := by
  simpa [execute, compile_length] using
    runFrom_steps input.toList (compile aig) [] m aig.decls.size (compile_bounded aig) (by simp [compile_length])

private theorem eval_decl {m n : Nat} (aig : AIG (Fin m)) (input : Vector Bool m)
    (hn : n < aig.decls.size) (memory : List Bool) (hlen : memory.length = n)
    (hmem : ∀ j (hj : j < n), memory[j]'(by omega) =
      AIG.denote.go j aig.decls (fun i => input[i]) (hj.trans hn) aig.hdag) :
    ((compileDecl aig.decls[n]).eval input.toList memory).value =
      AIG.denote.go n aig.decls (fun i => input[i]) hn aig.hdag := by
  have hread (j : Nat) (hj : j < n) :
      (read (List.replicate j ()) memory).value =
        AIG.denote.go j aig.decls (fun i => input[i]) (hj.trans hn) aig.hdag := by
    rw [read_value, List.length_replicate, List.getElem?_eq_getElem (by omega)]
    exact hmem j hj
  cases he : aig.decls[n] with
  | false =>
    have hg := AIG.denote_idx_false (assign := fun i => input[i]) (invert := false) he
    simpa [AIG.denote, compileDecl, Instr.eval] using hg.symm
  | atom a =>
    have hg := AIG.denote_idx_atom (assign := fun i => input[i]) (invert := false) he
    simpa [AIG.denote, compileDecl, Instr.eval, read_value] using hg.symm
  | gate l r =>
    have hd := aig.hdag hn he
    have hg := AIG.denote_idx_gate (assign := fun i => input[i]) (invert := false) he
    simp only [AIG.denote, Bool.xor_false] at hg
    rw [hg]
    simp only [compileDecl, Instr.eval]
    rw [hread l.gate hd.1, hread r.gate hd.2]

private def evalPrefix {m : Nat} (aig : AIG (Fin m)) (input : Vector Bool m) (n : Nat) : List Bool :=
  (runFrom input.toList ((compile aig).take n) []).value

private theorem prefix_values {m : Nat} (aig : AIG (Fin m)) (input : Vector Bool m)
    (n : Nat) (hn : n ≤ aig.decls.size) :
    evalPrefix aig input n = List.ofFn (fun i : Fin n =>
      AIG.denote.go i aig.decls (fun j => input[j]) (i.isLt.trans_le hn) aig.hdag) := by
  induction n with
  | zero => simp [evalPrefix, runFrom, foldRun]
  | succ n ih =>
    have hn' : n < aig.decls.size := by omega
    have hi := ih hn'.le
    have hlen : (evalPrefix aig input n).length = n := by rw [hi, List.length_ofFn]
    have hm : ∀ j (hj : j < n), (evalPrefix aig input n)[j]'(by omega) =
        AIG.denote.go j aig.decls (fun i => input[i]) (hj.trans hn') aig.hdag := by
      intro j hj
      simp only [hi, List.getElem_ofFn]
    have hv := eval_decl aig input hn' (evalPrefix aig input n) hlen hm
    have hnext : evalPrefix aig input (n + 1) =
        (step input.toList (compileDecl aig.decls[n]) (evalPrefix aig input n)).value := by
      have hc : n < (compile aig).length := by simpa [compile_length] using hn'
      simp only [evalPrefix, runFrom_value, List.take_succ_eq_append_getElem hc,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      congr 1
      simp [compile]
    rw [hnext, step_value, hv, hi, List.ofFn_succ_last]
    rfl

/-- The stored result of every declaration agrees with Std's AIG semantics. -/
theorem execute_correct {m : Nat} (aig : AIG (Fin m)) (input : Vector Bool m) :
    (execute aig input).value = List.ofFn (fun i : Fin aig.decls.size =>
      AIG.denote.go i aig.decls (fun j => input[j]) i.isLt aig.hdag) := by
  simpa [evalPrefix, execute, ← compile_length aig] using prefix_values aig input aig.decls.size le_rfl

/-- Output reads reuse the stored gate values. -/
def readOutputs (memory : List Bool) : List (List Unit × Bool) → Run (List Bool)
  | [] => ⟨[], 1⟩
  | (address, invert) :: outputs =>
    let b := read address memory
    let rest := readOutputs memory outputs
    ⟨(b.value ^^ invert) :: rest.value, b.steps + rest.steps + 3⟩

theorem readOutputs_value (memory : List Bool) (outputs : List (List Unit × Bool)) :
    (readOutputs memory outputs).value =
      outputs.map (fun (address, invert) => memory[address.length]?.getD false ^^ invert) := by
  induction outputs with
  | nil => rfl
  | cons output outputs ih => cases output; simp [readOutputs, read_value, ih]

theorem readOutputs_steps (memory : List Bool) (outputs : List (List Unit × Bool)) (n : Nat)
    (h : ∀ out ∈ outputs, out.1.length ≤ n) :
    (readOutputs memory outputs).steps ≤ outputs.length * (n + 4) + 1 := by
  induction outputs with
  | nil => simp [readOutputs]
  | cons output outputs ih =>
    obtain ⟨address, invert⟩ := output
    have hr := read_steps address memory
    have ha := h (address, invert) (by simp)
    have ht := ih (fun out ho => h out (by simp [ho]))
    simp only [readOutputs, List.length_cons]
    dsimp only at ha
    nlinarith

/-- Code and output addresses are compiled statically. All outputs share one
execution; `steps` counts the interpreter and output reads, not the compiler. -/
def evaluate {m : Nat} (aig : AIG (Fin m)) (refs : List (AIG.Ref aig)) (input : Vector Bool m) :
    Run (List Bool) :=
  let memory := execute aig input
  let outputs := readOutputs memory.value (refs.map (fun r => (List.replicate r.gate (), r.invert)))
  ⟨outputs.value, memory.steps + outputs.steps + 1⟩

theorem evaluate_correct {m : Nat} (aig : AIG (Fin m)) (refs : List (AIG.Ref aig)) (input : Vector Bool m) :
    (evaluate aig refs input).value = refs.map (fun r => AIG.denote (fun i => input[i]) ⟨aig, r⟩) := by
  simp only [evaluate, readOutputs_value, List.map_map]
  apply List.map_congr_left
  intro r _
  simp [execute_correct, AIG.denote, r.hgate]

theorem evaluate_steps {m : Nat} (aig : AIG (Fin m)) (refs : List (AIG.Ref aig)) (input : Vector Bool m) :
    (evaluate aig refs input).steps ≤ aig.decls.size * (4 * aig.decls.size + m + 10) +
      refs.length * (aig.decls.size + 4) + 3 := by
  have hm := execute_steps aig input
  have hr := readOutputs_steps (execute aig input).value
    (refs.map (fun r => (List.replicate r.gate (), r.invert))) aig.decls.size (by
      intro out ho
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp ho
      simpa using r.hgate.le)
  simp only [List.length_map] at hr
  simp only [evaluate]
  omega

/-- Executable code contains only finite instructions and unary addresses.
No AIG construction or semantic field/group value is consulted by `Code.run`. -/
structure Code where
  instructions : List Instr
  outputs : List (List Unit × Bool)

def Code.run (code : Code) (input : List Bool) : Run (List Bool) :=
  let memory := runFrom input code.instructions []
  let outputs := readOutputs memory.value code.outputs
  ⟨outputs.value, memory.steps + outputs.steps + 1⟩

theorem Code.run_length (code : Code) (input : List Bool) :
    (code.run input).value.length = code.outputs.length := by
  simp [Code.run, readOutputs_value]

def lower {m : Nat} (aig : AIG (Fin m)) (refs : List (AIG.Ref aig)) : Code :=
  ⟨compile aig, refs.map (fun r => (List.replicate r.gate (), r.invert))⟩

theorem lower_run {m : Nat} (aig : AIG (Fin m)) (refs : List (AIG.Ref aig))
    (input : Vector Bool m) :
    (lower aig refs).run input.toList = evaluate aig refs input := rfl

/-- Code cells include instruction/output list spines as well as addresses. -/
def Code.cells (code : Code) : Nat :=
  (code.instructions.map Instr.cells).sum + code.instructions.length +
    (code.outputs.map (fun out => out.1.length + 1)).sum + code.outputs.length + 2

theorem lower_cells {m : Nat} (aig : AIG (Fin m)) (refs : List (AIG.Ref aig)) :
    (lower aig refs).cells ≤ aig.decls.size * (2*aig.decls.size + m + 4) +
      refs.length * (aig.decls.size + 2) + 2 := by
  have ho : (refs.map (fun r => r.gate + 1)).sum ≤ refs.length * (aig.decls.size + 1) := by
    induction refs with
    | nil => simp
    | cons r refs ih =>
      have := r.hgate
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hc := compile_cells aig
  simp only [Code.cells, lower, List.length_map, List.map_map, Function.comp_def,
    List.length_replicate, compile_length]
  nlinarith

end Signatures.Runtime.CircuitExecution

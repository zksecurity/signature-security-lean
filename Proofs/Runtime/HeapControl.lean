import Proofs.Runtime.TypedHeap

/-! Bit-tape environments and heap control operations. Register slots contain
unary node indices. Reads parse those bits; extending a frame explicitly copies
the old frame and the new address. No arbitrary-size register value is free. -/

namespace Signatures.Runtime.SharedHeap

open HeapBits

def frameBits (roots : List Address) : List Bool := roots.flatMap unary

def frameGet : Address → List Bool → Run (Option Address)
  | [], frame =>
    let r := readUnary frame
    ⟨r.value.map Prod.fst, r.steps + 1⟩
  | _ :: slot, frame =>
    let r := readUnary frame
    match r.value with
    | none => ⟨none, r.steps + 1⟩
    | some (_, rest) =>
      let next := frameGet slot rest
      ⟨next.value, r.steps + next.steps + 2⟩

def framePush (addr : Address) (frame : List Bool) : Run (List Bool) :=
  let head := emitUnary addr
  let tail := HeapBits.copy frame
  let out := HeapBits.append head.value tail.value
  ⟨out.value, head.steps + tail.steps + out.steps + 1⟩

private theorem units_map (xs : Address) : xs.map (fun _ => ()) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [ih]

theorem frameGet_value (roots : List Address) (slot : Address) :
    (frameGet slot (frameBits roots)).value = roots[slot.length]? := by
  induction roots generalizing slot with
  | nil => cases slot <;> simp [frameBits, frameGet, readUnary]
  | cons root roots ih =>
    cases slot <;> simp [frameBits, frameGet, readUnary_value, units_map]
    exact ih _

theorem frameGet_steps (roots : List Address) (slot : Address) (nodes : Nat)
    (hr : ∀ root ∈ roots, root.length < nodes) :
    (frameGet slot (frameBits roots)).steps ≤ (slot.length+1)*(3*nodes+5) := by
  induction roots generalizing slot with
  | nil =>
    cases slot <;> simp [frameBits, frameGet, readUnary]
    nlinarith
  | cons root roots ih =>
    have hh := hr root (by simp)
    have ht := ih (hr := fun r h => hr r (by simp [h]))
    cases slot with
    | nil =>
      simp only [frameBits, List.flatMap_cons, frameGet, readUnary_steps, List.length_nil]
      omega
    | cons u slot =>
      have hs := ht slot
      simp only [frameBits, List.flatMap_cons, frameGet, readUnary_value, readUnary_steps,
        List.length_cons]
      simp only [frameBits] at hs
      nlinarith

theorem framePush_value (addr : Address) (roots : List Address) :
    (framePush addr (frameBits roots)).value = frameBits (addr :: roots) := by
  simp [framePush, emitUnary_value, copy_value, append_value, frameBits]

theorem framePush_steps (addr : Address) (frame : List Bool) :
    (framePush addr frame).steps = 4*addr.length + 2*frame.length + 6 := by
  simp [framePush, emitUnary_steps, copy_steps, append_steps, emitUnary_value, unary_length]
  omega

theorem frameBits_length (roots : List Address) (nodes : Nat)
    (hr : ∀ root ∈ roots, root.length < nodes) :
    (frameBits roots).length ≤ roots.length*(nodes+1) := by
  induction roots with
  | nil => simp [frameBits]
  | cons root roots ih =>
    have hh := hr root (by simp)
    have ht := ih (fun r h => hr r (by simp [h]))
    simp only [frameBits, List.flatMap_cons, List.length_append, unary_length,
      List.length_cons] at *
    nlinarith

def project (right : Bool) (memory : List Bool) (addr : Address) : Run (Option Address) :=
  let r := read addr memory
  ⟨match r.value with | some (.pair a b) => some (if right then b else a) | _ => none, r.steps + 2⟩

def readBool (memory : List Bool) (addr : Address) : Run (Option Bool) :=
  let r := read addr memory
  ⟨match r.value with | some (.word [b]) => some b | _ => none, r.steps + 2⟩

theorem project_value (right : Bool) (heap : List Node) (addr left rightAddr : Address)
    (h : heap[addr.length]? = some (.pair left rightAddr)) :
    (project right (tape heap) addr).value = some (if right then rightAddr else left) := by
  simp [project, read_value, h]

theorem project_steps (right : Bool) (heap : List Node) (addr : Address) :
    (project right (tape heap) addr).steps ≤ 3*(tape heap).length + 7*(heap.length+1) + 2 := by
  have h := read_steps heap addr
  simp only [project]
  omega

theorem readBool_value (heap : List Node) (addr : Address) (b : Bool)
    (h : heap[addr.length]? = some (.word [b])) : (readBool (tape heap) addr).value = some b := by
  simp [readBool, read_value, h]

theorem readBool_steps (heap : List Node) (addr : Address) :
    (readBool (tape heap) addr).steps ≤ 3*(tape heap).length + 7*(heap.length+1) + 2 := by
  have h := read_steps heap addr
  simp only [readBool]
  omega

variable {Atom : Type} {base : Atom → Type}

inductive EnvRep (w : Nat) (leaf : (a : Atom) → List Bool → base a → Prop) (heap : List Node) :
    {Γ : List (Ty Atom)} → List Address → Env base Γ → Prop
  | nil : EnvRep w leaf heap (Γ := []) [] ()
  | cons {Γ a root roots x env} : Represents w leaf heap a root x →
      EnvRep w leaf heap (Γ := Γ) roots env → EnvRep w leaf heap (Γ := a :: Γ) (root :: roots) (x, env)

variable {w : Nat} {leaf : (a : Atom) → List Bool → base a → Prop}
  {heap : List Node} {Γ : List (Ty Atom)} {roots : List Address} {env : Env base Γ}

theorem EnvRep.length (h : EnvRep w leaf heap roots env) : roots.length = Γ.length := by
  induction h <;> simp [*]

theorem EnvRep.addresses (h : EnvRep w leaf heap roots env) :
    ∀ root ∈ roots, root.length < heap.length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    intro root hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx.address_lt
    · exact ih root hr

theorem EnvRep.append (h : EnvRep w leaf heap roots env) (extra : List Node) :
    EnvRep w leaf (heap ++ extra) roots env := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (hx.append extra) ih

theorem EnvRep.get {a : Ty Atom} (h : EnvRep w leaf heap roots env) (v : Var Γ a) :
    ∃ root, roots[v.depth]? = some root ∧ Represents w leaf heap a root (v.get env) := by
  induction v generalizing roots with
  | here => cases h with | cons hx _ => exact ⟨_, rfl, hx⟩
  | there v ih =>
    cases h with
    | cons _ ht =>
      obtain ⟨root, hr, hv⟩ := ih ht
      exact ⟨root, hr, hv⟩

theorem frameGet_represents {a : Ty Atom} (h : EnvRep w leaf heap roots env) (v : Var Γ a) :
    ∃ root, (frameGet (List.replicate v.depth ()) (frameBits roots)).value = some root ∧
      Represents w leaf heap a root (v.get env) := by
  simpa only [frameGet_value, List.length_replicate] using h.get v

end Signatures.Runtime.SharedHeap

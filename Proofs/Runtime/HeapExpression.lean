import Proofs.Runtime.HeapControl
import Proofs.Runtime.HeapPrimitive

/-! First-order compiled expressions over heap roots and bit frames. Primitive
code is precompiled; no field/group values or host callbacks occur in Code.
List folds use a copied unary node counter as fuel, so malformed cyclic heaps
terminate with failure instead of invoking an unchecked recursive traversal. -/

namespace Signatures.Runtime.HeapExpression

open HeapBits SharedHeap FixedPorts WeierstrassCurve

def bind {A B : Type} (r : Run (Option A)) (next : A → Run (Option B)) : Run (Option B) :=
  match r.value with
  | none => ⟨none, r.steps + 1⟩
  | some a => let s := next a; ⟨s.value, r.steps + s.steps + 1⟩

def lift {A : Type} (r : Run A) : Run (Option A) := ⟨some r.value, r.steps + 1⟩

def map {A B : Type} (f : A → B) (r : Run (Option A)) : Run (Option B) :=
  ⟨r.value.map f, r.steps + 1⟩

abbrev Result := Option (Address × Store)

def foldLoop (step : Address → Address → Store → Run Result) :
    Address → Address → Address → Store → Run Result
  | [], _, _, _ => ⟨none, 1⟩
  | _ :: fuel, root, acc, store =>
    let node := read root store.memory
    match node.value with
    | some .nil =>
      let out := HeapBits.copy acc
      ⟨some (out.value, store), node.steps + out.steps + 2⟩
    | some (.cons head tail) =>
      let body := step head acc store
      let rest := bind body (fun p => foldLoop step fuel tail p.1 p.2)
      ⟨rest.value, node.steps + rest.steps + 2⟩
    | _ => ⟨none, node.steps + 1⟩

inductive Code where
  | var (slot : Address)
  | word (bits : List Bool)
  | nil
  | pair (left right : Code)
  | cons (head tail : Code)
  | project (right : Bool) (arg : Code)
  | branch (cond yes no : Code)
  | letE (arg body : Code)
  | primitive {a : Ty CryptoAtom} (layout : Layout a) (code : CircuitExecution.Code) (arg : Code)
  | fold (input init body : Code)

def Code.run : Code → List Bool → Store → Run Result
  | .var slot, frame, store => map (fun addr => (addr, store)) (frameGet slot frame)
  | .word bits, _, store => lift (alloc store (.word bits))
  | .nil, _, store => lift (alloc store .nil)
  | .pair left right, frame, store =>
    bind (left.run frame store) fun p =>
      bind (right.run frame p.2) fun q => lift (alloc q.2 (.pair p.1 q.1))
  | .cons head tail, frame, store =>
    bind (head.run frame store) fun p =>
      bind (tail.run frame p.2) fun q => lift (alloc q.2 (.cons p.1 q.1))
  | .project right arg, frame, store =>
    bind (arg.run frame store) fun p => map (fun addr => (addr, p.2)) (SharedHeap.project right p.2.memory p.1)
  | .branch cond yes no, frame, store =>
    bind (cond.run frame store) fun p =>
      bind (readBool p.2.memory p.1) fun b => if b then yes.run frame p.2 else no.run frame p.2
  | .letE arg body, frame, store =>
    bind (arg.run frame store) fun p =>
      let next := framePush p.1 frame
      let out := body.run next.value p.2
      ⟨out.value, next.steps + out.steps + 1⟩
  | .primitive layout code arg, frame, store =>
    bind (arg.run frame store) fun p => runPrimitive layout code p.2 p.1
  | .fold input init body, frame, store =>
    bind (input.run frame store) fun p =>
      bind (init.run frame p.2) fun q =>
        let fuel := HeapBits.copy q.2.count
        let out := foldLoop (fun head acc store =>
          let accFrame := framePush acc frame
          let headFrame := framePush head accFrame.value
          let out := body.run headFrame.value store
          ⟨out.value, accFrame.steps + headFrame.steps + out.steps + 2⟩)
            fuel.value p.1 q.1 q.2
        ⟨out.value, fuel.steps + out.steps + 1⟩

def compile {p₁ p₂ : Nat} (w r : Nat) (W₁ : Affine (ZMod p₁)) (W₂ : Affine (ZMod p₂))
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} : Expr CryptoOp Γ a → Code
  | .var v => .var (List.replicate v.depth ())
  | .unit => .word []
  | .bool b => .word [b]
  | .nat n => .word (natBits w n)
  | .pair l right => .pair (compile w r W₁ W₂ l) (compile w r W₁ W₂ right)
  | .fst p => .project false (compile w r W₁ W₂ p)
  | .snd p => .project true (compile w r W₁ W₂ p)
  | .nil => .nil
  | .cons x xs => .cons (compile w r W₁ W₂ x) (compile w r W₁ W₂ xs)
  | .branch c yes no => .branch (compile w r W₁ W₂ c) (compile w r W₁ W₂ yes) (compile w r W₁ W₂ no)
  | .letE x body => .letE (compile w r W₁ W₂ x) (compile w r W₁ W₂ body)
  | .op op arg => .primitive (inputLayout op) (CryptoCircuit.precompile w r W₁ W₂ op)
      (compile w r W₁ W₂ arg)
  | .fold xs init body => .fold (compile w r W₁ W₂ xs) (compile w r W₁ W₂ init) (compile w r W₁ W₂ body)

end Signatures.Runtime.HeapExpression

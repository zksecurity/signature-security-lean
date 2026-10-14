import Signatures.Runtime.Arithmetic
import Signatures.Runtime.FieldCircuitVector

/-! Typed circuit ports for the existing first-order language. Products and
lists here describe collections of wires in the compiler, not a runtime heap
representation. Runtime allocation and pointer lowering are separate. -/

namespace Signatures.Runtime.CircuitWires

open Std.Sat

variable {A : Type} [Hashable A] [DecidableEq A]

def Atom (w : Nat) (aig : AIG A) : CryptoAtom → Type
  | .point₁ | .point₂ => Fin 3 → AIG.RefVec aig w
  | .scalar | .key | .message | .fin _ => AIG.RefVec aig w

def Wires (w : Nat) (aig : AIG A) : Ty CryptoAtom → Type
  | .atom a => Atom w aig a
  | .unit => Unit
  | .bool => AIG.Ref aig
  | .nat => AIG.RefVec aig w
  | .pair a b => Wires w aig a × Wires w aig b
  | .list a => List (Wires w aig a)

def cast {w : Nat} {aig next : AIG A} (h : AIG.IsPrefix aig.decls next.decls) :
    {t : Ty CryptoAtom} → Wires w aig t → Wires w next t
  | .atom .point₁, x | .atom .point₂, x => fun i => (x i).cast h.size_le
  | .atom .scalar, x | .atom .key, x | .atom .message, x | .atom (.fin _), x => x.cast h.size_le
  | .unit, _ => ()
  | .bool, x => x.cast h.size_le
  | .nat, x => x.cast h.size_le
  | .pair _ _, x => (cast h x.1, cast h x.2)
  | .list _, xs => xs.map (cast h)

structure Compiled (w : Nat) (aig : AIG A) (t : Ty CryptoAtom) where
  graph : AIG A
  refs : Wires w graph t
  extension : AIG.IsPrefix aig.decls graph.decls

def Compiled.cast {w : Nat} {aig : AIG A} {t s : Ty CryptoAtom}
    (out : Compiled w aig t) (refs : Wires w aig s) : Wires w out.graph s :=
  CircuitWires.cast out.extension refs

/-- Port order only. List boundaries live in the typed compiler metadata;
this is not a serialization or runtime memory layout for arbitrary values. -/
def outputs {w : Nat} {aig : AIG A} : {t : Ty CryptoAtom} → Wires w aig t → List (AIG.Ref aig)
  | .atom .point₁, x | .atom .point₂, x =>
    (List.ofFn (fun i : Fin w => (x 0).get i i.isLt)) ++
    (List.ofFn (fun i : Fin w => (x 1).get i i.isLt)) ++
    (List.ofFn (fun i : Fin w => (x 2).get i i.isLt))
  | .atom .scalar, x | .atom .key, x | .atom .message, x | .atom (.fin _), x | .nat, x =>
    List.ofFn (fun i : Fin w => x.get i i.isLt)
  | .unit, _ => []
  | .bool, x => [x]
  | .pair _ _, x => outputs x.1 ++ outputs x.2
  | .list _, xs => xs.flatMap outputs

theorem prefix_trans {a b c : AIG A}
    (h : AIG.IsPrefix a.decls b.decls) (h' : AIG.IsPrefix b.decls c.decls) :
    AIG.IsPrefix a.decls c.decls where
  size_le := h.size_le.trans h'.size_le
  idx_eq i hi := (h'.idx_eq i (hi.trans_le h.size_le)).trans (h.idx_eq i hi)

end Signatures.Runtime.CircuitWires

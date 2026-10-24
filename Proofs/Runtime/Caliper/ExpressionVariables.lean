import Proofs.Runtime.Caliper.CheckedComposition

/-! Source variables are compiled by walking represented environment products.
Each projection executes its existing charged slice-copy implementation. -/

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type}

inductive Variable : {Γ : List (Ty Atom)} → {a : Ty Atom} → Var Γ a →
    Layout w (Env base Γ) → Layout w (a.Value base) → Type where
  | here {Γ : List (Ty Atom)} {a : Ty Atom} (head : Layout w (a.Value base)) (tail : Layout w (Env base Γ))
      (fits : head.representation.encoding.words + tail.representation.encoding.words < 2 ^ w) :
      Variable .here (head.prod tail fits) head
  | there {Γ : List (Ty Atom)} {a b : Ty Atom} {v : Var Γ a} {tail : Layout w (Env base Γ)} {result : Layout w (a.Value base)}
      (head : Layout w (b.Value base)) (rest : Variable v tail result)
      (fits : head.representation.encoding.words + tail.representation.encoding.words < 2 ^ w) :
      Variable (.there v) (head.prod tail fits) result

def Variable.compile {cost : CostModel} {Γ : List (Ty Atom)} {a : Ty Atom} {v : Var Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w) :
    Variable v input output → Implementation cost input output v.get
  | .here head tail fits => Implementation.first allocation head tail hw fits
  | .there (tail := tail) head rest fits =>
      (Implementation.second allocation head tail hw fits).then (rest.compile allocation hw)

end Signatures.Runtime.CaliperBackend.SourceExpression

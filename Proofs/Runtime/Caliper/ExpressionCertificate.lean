import Proofs.Runtime.Caliper.ExpressionVariables
import Proofs.Runtime.Caliper.SourceListData
import Proofs.Runtime.Caliper.Natural
import Proofs.Runtime.Caliper.StagedFold

/-! Bounded compilation certificates indexed by the original expression syntax.
Only fixed instruction leaves require primitive implementations. Layouts and
capacity proofs restrict representable domains; they are not executable data.
Generated scratch-name checks are performed by the compiler. -/

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    (P : Primitives base Op) (cost : CostModel) (hw : 16 < 2 ^ w)

inductive Compilation : {Γ : List (Ty Atom)} → {a : Ty Atom} → Expr Op Γ a →
    Layout w (Env base Γ) → Layout w (a.Value base) → Type where
  | var {Γ : List (Ty Atom)} {a : Ty Atom} {v : Var Γ a} {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
      (access : Variable v input output) : Compilation (.var v) input output
  | unit {Γ : List (Ty Atom)} (input : Layout w (Env base Γ)) : Compilation .unit input (DataImplementation.unitLayout w)
  | bool {Γ : List (Ty Atom)} (input : Layout w (Env base Γ)) (value : Bool) :
      Compilation (.bool value) input (DataImplementation.boolLayout w (width_pos hw))
  | nat {Γ : List (Ty Atom)} (input : Layout w (Env base Γ)) (value bound : Nat)
      (fits : bound ≤ 2 ^ w) (valid : value < bound) :
      Compilation (.nat value) input (Layout.counter w bound (width_pos hw) fits)
  | pair {Γ : List (Ty Atom)} {a b : Ty Atom} {first : Expr Op Γ a} {second : Expr Op Γ b}
      {input : Layout w (Env base Γ)} {left : Layout w (a.Value base)} {right : Layout w (b.Value base)}
      (firstCode : Compilation first input left) (secondCode : Compilation second input right)
      (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
      Compilation (.pair first second) input (left.prod right outputFits)
  | fst {Γ : List (Ty Atom)} {a b : Ty Atom} {value : Expr Op Γ (.pair a b)} {input : Layout w (Env base Γ)}
      (left : Layout w (a.Value base)) (right : Layout w (b.Value base))
      (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
      (code : Compilation value input (left.prod right fits)) : Compilation (.fst value) input left
  | snd {Γ : List (Ty Atom)} {a b : Ty Atom} {value : Expr Op Γ (.pair a b)} {input : Layout w (Env base Γ)}
      (left : Layout w (a.Value base)) (right : Layout w (b.Value base))
      (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
      (code : Compilation value input (left.prod right fits)) : Compilation (.snd value) input right
  | nil {Γ : List (Ty Atom)} {a : Ty Atom} (input : Layout w (Env base Γ)) (entry : Layout w (a.Value base)) (capacity : Nat)
      (countFits : capacity < 2 ^ w)
      (storageFits : 1 + capacity * entry.representation.encoding.words < 2 ^ w) :
      Compilation .nil input (entry.boundedList capacity countFits storageFits)
  | cons {Γ : List (Ty Atom)} {a : Ty Atom} {head : Expr Op Γ a} {tail : Expr Op Γ (.list a)} {input : Layout w (Env base Γ)}
      (entry : Layout w (a.Value base)) (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
      (storageFits : 1 + (capacity + 1) * entry.representation.encoding.words < 2 ^ w)
      (headCode : Compilation head input entry)
      (tailCode : Compilation tail input (entry.boundedList capacity (by omega) (by nlinarith)))
      (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (middleFits : entry.representation.encoding.words + input.representation.encoding.words < 2 ^ w) :
      Compilation (.cons head tail) input (entry.boundedList (capacity + 1) countFits storageFits)
  | branch {Γ : List (Ty Atom)} {a : Ty Atom} {condition : Expr Op Γ .bool} {yes no : Expr Op Γ a}
      {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
      (test : Compilation condition input (DataImplementation.boolLayout w (width_pos hw)))
      (left : Compilation yes input output) (right : Compilation no input output)
      (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (tagFits : 1 + input.representation.encoding.words < 2 ^ w) :
      Compilation (.branch condition yes no) input output
  | letE {Γ : List (Ty Atom)} {a b : Ty Atom} {value : Expr Op Γ a} {body : Expr Op (a :: Γ) b}
      {input : Layout w (Env base Γ)} (localValue : Layout w (a.Value base)) {output : Layout w (b.Value base)}
      (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (frameFits : localValue.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (binding : Compilation value input localValue) (code : Compilation body (localValue.prod input frameFits) output) :
      Compilation (.letE value body) input output
  | op {Γ : List (Ty Atom)} {a b : Ty Atom} (instr : Op a b) {value : Expr Op Γ a} {input : Layout w (Env base Γ)}
      {argument : Layout w (a.Value base)} {output : Layout w (b.Value base)}
      (implementation : Implementation cost argument output (P.execute instr))
      (code : Compilation value input argument) : Compilation (.op instr value) input output
  | fold {Γ : List (Ty Atom)} {a b : Ty Atom} {values : Expr Op Γ (.list a)} {initial : Expr Op Γ b} {body : Expr Op (a :: b :: Γ) b}
      (input : Layout w (Env base Γ)) (entry : Layout w (a.Value base)) (state : Layout w (b.Value base))
      (capacity : Nat) (countFits : capacity < 2 ^ w)
      (argFits : entry.representation.encoding.words + state.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (frameFits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words +
        2 * input.representation.encoding.words < 2 ^ w)
      (valueCode : Compilation values input (entry.boundedList capacity countFits (by omega)))
      (initialCode : Compilation initial input state)
      (bodyCode : Compilation body (FoldImplementation.bodyInput entry state input argFits) state) :
      Compilation (.fold values initial body) input state
  | foldStages {Γ : List (Ty Atom)} {a b : Ty Atom} {values : Expr Op Γ (.list a)} {initial : Expr Op Γ b} {body : Expr Op (a :: b :: Γ) b}
      (input : Layout w (Env base Γ)) (entry : Layout w (a.Value base)) (output : Layout w (b.Value base))
      (capacity : Nat) (states : Fin (capacity + 1) → Layout w (b.Value base))
      (countFits : capacity < 2 ^ w)
      (argFits : ∀ i : Fin capacity,
        entry.representation.encoding.words + (states i.castSucc).representation.encoding.words + input.representation.encoding.words < 2 ^ w)
      (frameFits : ∀ i : Fin (capacity + 1),
        1 + (capacity - i.val) * entry.representation.encoding.words + (states i).representation.encoding.words +
          2 * input.representation.encoding.words < 2 ^ w)
      (valueCode : Compilation values input (entry.boundedList capacity countFits (by
        have bound := frameFits 0
        simp only [Fin.val_zero, Nat.sub_zero] at bound
        omega)))
      (initialCode : Compilation initial input (states 0))
      (bodyCode : ∀ i : Fin capacity, Compilation body
        (FoldImplementation.bodyInput entry (states i.castSucc) input (argFits i)) (states i.succ))
      (stops : ∀ i : Fin (capacity + 1), Implementation cost (states i) output id) :
      Compilation (.fold values initial body) input output
  | view {Γ : List (Ty Atom)} {a : Ty Atom} {expression : Expr Op Γ a}
      {input : Layout w (Env base Γ)} {source target : Layout w (a.Value base)}
      (code : Compilation expression input source)
      (preserves : ∀ value, source.valid value → target.valid value)
      (sameBytes : ∀ value : source.Value,
        target.representation.encoding.encode ⟨value.val, preserves value.val value.property⟩ =
          source.representation.encoding.encode value) : Compilation expression input target
  | listWiden {Γ : List (Ty Atom)} {a : Ty Atom} {expression : Expr Op Γ (.list a)}
      {input : Layout w (Env base Γ)} (entry : Layout w (a.Value base))
      (source target : Nat) (increasing : source ≤ target) (countFits : target < 2 ^ w)
      (storageFits : 1 + target * entry.representation.encoding.words < 2 ^ w)
      (code : Compilation expression input (entry.boundedList source (by omega) (by nlinarith))) :
      Compilation expression input (entry.boundedList target countFits storageFits)

end Signatures.Runtime.CaliperBackend.SourceExpression

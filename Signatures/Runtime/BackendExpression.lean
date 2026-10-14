import Signatures.Runtime.BackendProgram

/-! Compile arithmetic expressions into the caller's quantitative backend.

The extra backend operations are generic data operations and list iteration with
an executable body. No operation accepts an arbitrary semantic callback without
its implementation. In particular the compiler constructs code recursively; an
implementation of a complete expression or reduction is not an input contract.
Their cost/description bounds must be justified separately for the fixed backend.
-/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}

/-- The data representations are fixed once for the wrapper and the caller. -/
structure DataRepresentation (C : StepClass.{0, v}) where
  unit : C.Str Unit
  bool : C.Str Bool
  nat : C.Str Nat
  list : {A : Type} → C.Str A → C.Str (List A)

/-- Executable constructors for ordinary data. The fold stores its body code;
its runtime depends on the list length and the work of every body invocation. -/
structure DataCode (Q : QuantitativeStepClass.{0, v, w} C) (data : DataRepresentation C) where
  unit : {A : Type} → (a : C.Str A) → Q.Realizer a data.unit (fun _ => ())
  bool : (b : Bool) → Q.Realizer data.unit data.bool (fun _ => b)
  nat : (n : Nat) → Q.Realizer data.unit data.nat (fun _ => n)
  nil : {A : Type} → (a : C.Str A) → Q.Realizer data.unit (data.list a) (fun _ => [])
  cons : {A : Type} → (a : C.Str A) →
    Q.Realizer (StepClass.HasProd.prod a (data.list a)) (data.list a) (fun p => p.1 :: p.2)
  select : {A : Type} → (a : C.Str A) →
    Q.Realizer (StepClass.HasProd.prod data.bool a) (StepClass.HasSum.sum a a)
      (fun p => if p.1 = true then Sum.inl p.2 else Sum.inr p.2)
  fold : {A B E : Type} → (a : C.Str A) → (b : C.Str B) → (e : C.Str E) →
    {f : A × (B × E) → B} →
    Q.Realizer (StepClass.HasProd.prod a (StepClass.HasProd.prod b e)) b f →
    Q.Realizer (StepClass.HasProd.prod (data.list a) (StepClass.HasProd.prod b e)) b
      (fun p => p.1.foldl (fun acc x => f (x, acc, p.2.2)) p.2.1)

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}

structure LanguageRepresentation (C : StepClass.{0, v}) (base : Atom → Type) where
  data : DataRepresentation C
  atom : (a : Atom) → C.Str (base a)

@[reducible] def LanguageRepresentation.ty (rep : LanguageRepresentation C base) :
    (a : Ty Atom) → C.Str (a.Value base)
  | .atom a => rep.atom a
  | .unit => rep.data.unit
  | .bool => rep.data.bool
  | .nat => rep.data.nat
  | .pair a b => StepClass.HasProd.prod (rep.ty a) (rep.ty b)
  | .list a => rep.data.list (rep.ty a)

@[reducible] def LanguageRepresentation.env (rep : LanguageRepresentation C base) :
    (Γ : List (Ty Atom)) → C.Str (Env base Γ)
  | [] => rep.data.unit
  | a :: Γ => StepClass.HasProd.prod (rep.ty a) (rep.env Γ)

namespace Expression

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))

def variableCode {Γ a} (v : Var Γ a) : Q.Realizer (rep.env Γ) (rep.ty a) v.get :=
  match v with
  | .here => QP.fst _ _
  | .there v => Q.compose (QP.snd _ _) (variableCode v)

/-- The semantic index of the resulting realizer proves expression correctness. -/
def compile {Γ a} (expression : Expr Op Γ a) :
    Q.Realizer (rep.env Γ) (rep.ty a) (expression.denote P) :=
  match expression with
  | .var v => variableCode rep v
  | .unit => data.unit _
  | .bool b => Q.compose (data.unit _) (data.bool b)
  | .nat n => Q.compose (data.unit _) (data.nat n)
  | .pair left right => QP.pair (compile left) (compile right)
  | .fst pair => Q.compose (compile pair) (QP.fst _ _)
  | .snd pair => Q.compose (compile pair) (QP.snd _ _)
  | .nil => Q.compose (data.unit _) (data.nil _)
  | .cons head tail => Q.compose
      (QP.pair (compile head) (compile tail)) (data.cons _)
  | .branch cond yes no =>
      (Q.compose (Q.compose (QP.pair (compile cond) (Q.identity _)) (data.select _))
        (QS.elim (compile yes) (compile no))).castFunction
          (by funext env; simp only [Function.comp_apply, Expr.denote]; split <;> rfl)
  | .letE value body => Q.compose (QP.pair (compile value) (Q.identity _))
      (compile body)
  | .op instr arg => Q.compose (compile arg) (primitive instr)
  | .fold values init body => Q.compose
      (QP.pair (compile values) (QP.pair (compile init) (Q.identity _)))
      (data.fold _ _ _ (compile body))

def arguments {Γ Δ} (args : Args Op Γ Δ) :
    Q.Realizer (rep.env Γ) (rep.env Δ) (args.denote P) :=
  match args with
  | .nil => data.unit _
  | .cons head tail => QP.pair (compile rep data P primitive head) (arguments tail)

end Expression

end Signatures.Runtime.BackendProgram

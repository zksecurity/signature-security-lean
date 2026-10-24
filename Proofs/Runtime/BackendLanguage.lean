import Proofs.Runtime.BackendExpression
import Proofs.Runtime.BackendAssembly

/-! State-passing compilation of the first-order wrapper language.

This compiler shares the backend and represented values used by the general
caller. State reads/writes and randomness are supplied as individually implemented
effects. All expression, argument, environment, and control-flow code is assembled
recursively. The source program's arbitrary input-bounded loops store one body.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.Language

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {I S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}

def contextReturn {B E : Type} (b : C.Str B) (e : C.Str E) (store : C.Str S) :
    Q.Realizer (StepClass.HasProd.prod (StepClass.HasProd.prod b store) e)
      (StepClass.HasProd.prod (StepClass.HasProd.prod b e) store)
      (fun p => ((p.1.1, p.2), p.1.2)) :=
  QP.pair (QP.pair (Q.compose (QP.fst _ _) (QP.fst _ _)) (QP.snd _ _))
    (Q.compose (QP.fst _ _) (QP.snd _ _))

def contextInput {A E : Type} (a : C.Str A) (e : C.Str E) (store : C.Str S)
    {f : A → E} (context : Q.Realizer a e f) :
    Q.Realizer (StepClass.HasProd.prod a store)
      (StepClass.HasProd.prod (StepClass.HasProd.prod a store) e) (fun p => (p, f p.1)) :=
  QP.pair (Q.identity _) (Q.compose (QP.fst _ _) context)

/-- Save a represented local context across a stateful computation. Copying and
rearranging that context executes actual structural code and remains charged. -/
def withContext {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    (store : C.Str S) {f : A → E} (context : Q.Realizer a e f)
    (body : Code Q spec iface (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store)) :
    Code Q spec iface (StepClass.HasProd.prod a store)
      (StepClass.HasProd.prod (StepClass.HasProd.prod b e) store) :=
  .seq (.atomic (contextInput a e store context))
    (.seq (.first e body) (.atomic (contextReturn b e store)))

omit QS in
theorem withContext_denote {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    (store : C.Str S) {f : A → E} (context : Q.Realizer a e f)
    (body : Code Q spec iface (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store))
    (input : A × S) :
    (withContext store context body).denote input =
      (fun p => ((p.1, f input.1), p.2)) <$> body.denote input := by
  simp only [withContext, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (store : C.Str S)
  (effect : {a b : Ty Atom} → Cmd a b →
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store))

def choose {Γ} (cond : Expr Op Γ .bool) :
    Q.Realizer (StepClass.HasProd.prod (rep.env Γ) store)
      (StepClass.HasSum.sum (StepClass.HasProd.prod (rep.env Γ) store)
        (StepClass.HasProd.prod (rep.env Γ) store))
      (fun p => if cond.denote P p.1 = true then Sum.inl p else Sum.inr p) :=
  Q.compose (QP.pair (Q.compose (QP.fst _ _) (Expression.compile rep data P primitive cond)) (Q.identity _))
    (data.select _)

def loopInput {Γ a} (count : Expr Op Γ .nat) (init : Expr Op Γ a) :
    Q.Realizer (StepClass.HasProd.prod (rep.env Γ) store)
      (StepClass.HasProd.prod rep.data.nat (StepClass.HasProd.prod (rep.env (a :: Γ)) store))
      (fun p => (count.denote P p.1, ((init.denote P p.1, p.1), p.2))) :=
  QP.pair (Q.compose (QP.fst _ _) (Expression.compile rep data P primitive count))
    (QP.pair (QP.pair (Q.compose (QP.fst _ _) (Expression.compile rep data P primitive init))
      (QP.fst _ _)) (QP.snd _ _))

def loopOutput {Γ a} :
    Q.Realizer (StepClass.HasProd.prod (rep.env (a :: Γ)) store)
      (StepClass.HasProd.prod (rep.ty a) store) (fun p => (p.1.1, p.2)) :=
  QP.pair (Q.compose (QP.fst _ _) (QP.fst _ _)) (QP.snd _ _)

def compile {Γ a} (program : Program Op Cmd Γ a) :
    Code Q spec iface (StepClass.HasProd.prod (rep.env Γ) store)
      (StepClass.HasProd.prod (rep.ty a) store) :=
  match program with
  | .ret expression => .first store (.atomic (Expression.compile rep data P primitive expression))
  | .query instr arg => .seq (.first store (.atomic (Expression.compile rep data P primitive arg)))
      (effect instr)
  | .bind initial following => .seq (withContext store (Q.identity _) (compile initial))
      (compile following)
  | .branch cond yes no => .seq (.atomic (choose rep data P primitive store cond))
      (.branch (compile yes) (compile no))
  | .loop (a := a) (Γ := Γ) count init body =>
      .seq (.atomic (loopInput rep data P primitive store count init))
        (.seq (.iterate rep.data.nat (withContext store (QP.snd (rep.ty a) (rep.env Γ)) (compile body)))
          (.atomic (loopOutput rep store)))
  | .call body args => .seq (.first store (.atomic (Expression.arguments rep data P primitive args)))
      (compile body)

end Signatures.Runtime.BackendProgram.Language

import Proofs.Runtime.BackendLocalBound

/-! Derive compiled expression costs from primitive and structural costs.

The bounds are generated recursively over the expression syntax. Only named
primitive instructions require supplied certificates. The resulting time
expression includes encoded-size overhead, variable traversal, selected branches,
and every fold-body invocation. A polynomial bound still requires bounds on the
reachable representations and on the backend overhead/primitive functions.
-/

open PFunctor

namespace Signatures.Runtime.BackendProgram.Expression

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty Atom} → (instr : Op a b) → LocalBound (primitive instr))

def variableBound {Γ a} (v : Var Γ a) : LocalBound (variableCode (Q := Q) rep v) :=
  match v with
  | .here => LocalBound.fst localLaws _ _
  | .there v => LocalBound.compose localLaws (LocalBound.snd localLaws _ _) (variableBound v)

def compileBound {Γ a} (expression : Expr Op Γ a) :
    LocalBound (compile rep data P primitive expression) :=
  match expression with
  | .var v => variableBound rep localLaws v
  | .unit => dataLaws.unitBound _
  | .bool b => LocalBound.compose localLaws (dataLaws.unitBound _) (dataLaws.boolBound b)
  | .nat n => LocalBound.compose localLaws (dataLaws.unitBound _) (dataLaws.natBound n)
  | .pair left right => LocalBound.pair localLaws (compileBound left) (compileBound right)
  | .fst pair => LocalBound.compose localLaws (compileBound pair) (LocalBound.fst localLaws _ _)
  | .snd pair => LocalBound.compose localLaws (compileBound pair) (LocalBound.snd localLaws _ _)
  | .nil => LocalBound.compose localLaws (dataLaws.unitBound _) (dataLaws.nilBound _)
  | .cons head tail => LocalBound.compose localLaws
      (LocalBound.pair localLaws (compileBound head) (compileBound tail)) (dataLaws.consBound _)
  | .branch cond yes no =>
      (LocalBound.compose localLaws
        (LocalBound.compose localLaws
          (LocalBound.pair localLaws (compileBound cond) (LocalBound.identity localLaws _))
          (dataLaws.selectBound _))
        (LocalBound.elim localLaws (compileBound yes) (compileBound no))).castFunction _
  | .letE value body => LocalBound.compose localLaws
      (LocalBound.pair localLaws (compileBound value) (LocalBound.identity localLaws _))
      (compileBound body)
  | .op instr arg => LocalBound.compose localLaws (compileBound arg) (primitiveBound instr)
  | .fold values init body => LocalBound.compose localLaws
      (LocalBound.pair localLaws (compileBound values)
        (LocalBound.pair localLaws (compileBound init) (LocalBound.identity localLaws _)))
      (dataLaws.foldBound _ _ _ (compileBound body))

def argumentsBound {Γ Δ} (args : Args Op Γ Δ) :
    LocalBound (arguments rep data P primitive args) :=
  match args with
  | .nil => dataLaws.unitBound _
  | .cons head tail => LocalBound.pair localLaws
      (compileBound rep data P primitive localLaws dataLaws primitiveBound head) (argumentsBound tail)

theorem cost_compile_le {Γ a} (expression : Expr Op Γ a) (env : Env base Γ) :
    Q.cost (compile rep data P primitive expression) env ≤
      (compileBound rep data P primitive localLaws dataLaws primitiveBound expression).time env :=
  (compileBound rep data P primitive localLaws dataLaws primitiveBound expression).cost_le env

theorem cost_arguments_le {Γ Δ} (args : Args Op Γ Δ) (env : Env base Γ) :
    Q.cost (arguments rep data P primitive args) env ≤
      (argumentsBound rep data P primitive localLaws dataLaws primitiveBound args).time env :=
  (argumentsBound rep data P primitive localLaws dataLaws primitiveBound args).cost_le env

end Signatures.Runtime.BackendProgram.Expression

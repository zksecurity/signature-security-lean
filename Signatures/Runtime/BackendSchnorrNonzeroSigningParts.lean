import Signatures.Runtime.BackendSchnorrNonzeroRepairCost
import Signatures.Runtime.BackendSchnorrROMSigningBudget

/-! Named continuations and local adapter costs for the existing three-draw
nonzero signer. These definitions preserve its exact compiled syntax. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroSigning.Native.Parts

open BackendProgram

abbrev Output : Ty CryptoAtom := .pair (.pair point₁ scalar) hashCache

def returnValue : Expr CryptoOp (hashCache :: Repaired) Output := .pair v1 v0

def finish : Program CryptoOp Draw Repaired Output :=
  .bind (.call (.ret (cacheProgram hashEq)) programArgs) (.ret returnValue)

def repairThen : Program CryptoOp Draw Committed Output :=
  .bind (.call (.ret repair) repairArgs) finish

def commitThen : Program CryptoOp Draw Sampled Output :=
  .bind (.call (.ret simulatedCommit) commitArgs) repairThen

def nonzeroThen : Program CryptoOp Draw (scalar :: scalar :: Input) Output :=
  .bind (.query .nonzero .unit) commitThen

def secondThen : Program CryptoOp Draw (scalar :: Input) Output :=
  .bind (.query .field .unit) nonzeroThen

theorem body_eq : body Draw.field Draw.nonzero = .bind (.query .field .unit) secondThen := rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes laws dataLaws primitiveBound mono

theorem commitArgs_cost (env : Env (cryptoBase F G₁ G₂ K M) Sampled)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env Sampled) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive commitArgs) env ≤
      128 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [commitArgs, Input, Sampled, Committed, Repaired, Output,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem repairArgs_cost (env : Env (cryptoBase F G₁ G₂ K M) Committed)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env Committed) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive repairArgs) env ≤
      128 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [repairArgs, Input, Sampled, Committed, Repaired, Output,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem programArgs_cost (env : Env (cryptoBase F G₁ G₂ K M) Repaired)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env Repaired) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive programArgs) env ≤
      128 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [programArgs, Input, Sampled, Committed, Repaired, Output,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem returnValue_cost (env : Env (cryptoBase F G₁ G₂ K M) (hashCache :: Repaired))
    (width : Nat) (hh : header ≤ width) (_hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env (hashCache :: Repaired)) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive returnValue) env ≤
      128 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  dsimp only [returnValue, Input, Sampled, Committed, Repaired, Output,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.Schnorr.NonzeroSigning.Native.Parts

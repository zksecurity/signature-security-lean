import Signatures.Runtime.BackendSchnorrROMLiveBudget
import Signatures.Runtime.BackendSchnorrROMProgrammingCost

/-! Named pieces of the existing ordinary-ROM cache/signing programs, and their
actual local adapter costs. The syntax equalities preserve the implemented code. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeCache.Parts

open BackendProgram

abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
abbrev v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
abbrev v6 {a b c d e f g Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there (.there .here))))))

abbrev ManagedEnv := [hashKey, scalar, hashCache, hashCache]
abbrev CheckedEnv := .pair .bool scalar :: ManagedEnv
abbrev FetchedEnv := .pair scalar hashCache :: CheckedEnv

def managedArgs : Args CryptoOp ManagedEnv [hashKey, scalar, hashCache] :=
  .cons v0 (.cons v1 (.cons v2 .nil))
def liveArgs : Args CryptoOp CheckedEnv [hashKey, scalar, hashCache] :=
  .cons v1 (.cons v2 (.cons v4 .nil))
def condition : Expr CryptoOp CheckedEnv .bool := .fst v0
def managedHit : Expr CryptoOp CheckedEnv (.pair scalar (.pair hashCache hashCache)) :=
  .pair (.snd v0) (.pair v3 v4)
def managedInsert : Expr CryptoOp FetchedEnv (.pair scalar (.pair hashCache hashCache)) :=
  .pair (.fst v0) (.pair (.cons (.pair v2 (.fst v0)) v4) (.snd v0))

variable {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

theorem managedGet_eq (draw : Cmd .unit scalar) :
    managedGet draw =
      .bind (.call (.ret (lookupExpr hashEq)) managedArgs)
        (.branch condition (.ret managedHit)
          (.bind (.call (cacheGetExpr hashEq draw) liveArgs) (.ret managedInsert))) := rfl

abbrev SigningEnv := [message, point₁, point₁, hashCache]
abbrev SampledEnv := scalar :: scalar :: SigningEnv
abbrev CommittedEnv := point₁ :: SampledEnv
abbrev ProgrammedEnv := hashCache :: CommittedEnv

def commitArgs : Args CryptoOp SampledEnv [scalar, scalar, point₁, point₁] :=
  .cons v0 (.cons v1 (.cons v3 (.cons v4 .nil)))
def programArgs : Args CryptoOp CommittedEnv [hashKey, scalar, hashCache] :=
  .cons (.pair v3 v0) (.cons v2 (.cons v6 .nil))
def signingReturn : Expr CryptoOp ProgrammedEnv (.pair (.pair point₁ scalar) hashCache) :=
  .pair (.pair v1 v2) v0

theorem signCached_eq (draw : Cmd .unit scalar) :
    signCached draw =
      .bind (.query draw .unit) (.bind (.query draw .unit)
        (.bind (.call (.ret simulatedCommit) commitArgs)
          (.bind (.call (.ret (cacheProgram hashEq)) programArgs) (.ret signingReturn)))) := rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
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

theorem managedArgs_cost (env : Env (cryptoBase F G₁ G₂ K M) ManagedEnv)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env ManagedEnv) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive managedArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [managedArgs, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem liveArgs_cost (env : Env (cryptoBase F G₁ G₂ K M) CheckedEnv)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env CheckedEnv) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive liveArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [liveArgs, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem condition_cost (env : Env (cryptoBase F G₁ G₂ K M) CheckedEnv)
    (width : Nat) (_hh : header ≤ width) (_hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env CheckedEnv) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive condition) env ≤
      8 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [condition, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem managedHit_cost (env : Env (cryptoBase F G₁ G₂ K M) CheckedEnv)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env CheckedEnv) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive managedHit) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [managedHit, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem commitArgs_cost (env : Env (cryptoBase F G₁ G₂ K M) SampledEnv)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env SampledEnv) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive commitArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [commitArgs, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem programArgs_cost (env : Env (cryptoBase F G₁ G₂ K M) CommittedEnv)
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env CommittedEnv) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive programArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [programArgs, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem signingReturn_cost (env : Env (cryptoBase F G₁ G₂ K M) ProgrammedEnv)
    (width : Nat) (hh : header ≤ width) (_hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env ProgrammedEnv) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive signingReturn) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [signingReturn, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem managedInsert_cost (lists : ListSizeLaws Q rep.data header)
    (env : Env (cryptoBase F G₁ G₂ K M) FetchedEnv)
    (width : Nat) (hh : header ≤ width) (_hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env FetchedEnv) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive managedInsert) env ≤
      128 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [managedInsert, v0, v1, v2, v3, v4, v6, ManagedEnv, CheckedEnv, FetchedEnv,
    SigningEnv, SampledEnv, CommittedEnv, ProgrammedEnv,
    Expression.argumentsBound, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, DataCostLaws.consBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem commit_cost (z c : F) (g pk : G₁) (width scaleTime subTime : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env [scalar, scalar, point₁, point₁]) (z, c, g, pk, ()) ≤ width)
    (hzg : Q.size (rep.ty point₁) (z • g) ≤ width)
    (hcp : Q.size (rep.ty point₁) (c • pk) ≤ width)
    (hr : Q.size (rep.ty point₁) (z • g - c • pk) ≤ width)
    (hz : (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hc : (primitiveBound .scale₁).time (c, pk) ≤ scaleTime)
    (ht : (primitiveBound .sub₁).time (z • g, c • pk) ≤ subTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive simulatedCommit)
      (z, c, g, pk, ()) ≤ 2 * scaleTime + subTime + 64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ h => mono h
  dsimp only [simulatedCommit, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.Schnorr.ListROM.NativeCache.Parts


import Proofs.Runtime.BackendCoronCacheCost
import Proofs.Runtime.BackendCoronArithmeticCost
import Proofs.Runtime.BackendMachineCost
import Proofs.Runtime.BackendExpressionSize

/-! Named pieces of the existing Coron reply syntax and their native routing
costs. The decomposition equals `machineReply` in each signing mode; it does not
replace the implementation or add a host-language cache/handler primitive. -/

open PFunctor

namespace Signatures.Runtime.Coron.ReplyCompiler

open BackendProgram

abbrev ScalarResult : Ty CryptoAtom := .pair scalar (.list (.pair message scalar))
abbrev CoinResult (qS : Nat) : Ty CryptoAtom := .pair (boundedNat qS) (.list (.pair message (boundedNat qS)))
abbrev ReadEnv (qS : Nat) := [machineStore qS, message]
abbrev ScalarEnv (qS : Nat) := ScalarResult :: ReadEnv qS
abbrev BothEnv (qS : Nat) := CoinResult qS :: ScalarEnv qS
abbrev WrittenEnv (qS : Nat) := Ty.unit :: BothEnv qS

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d := .var (.there (.there (.there .here)))

def scalarArgs (qS : Nat) : Args CryptoOp (ReadEnv qS) [message, scalar, .list (.pair message scalar)] :=
  .cons v1 (.cons (.op .zero .unit) (.cons (.fst (.snd v0)) .nil))

def coinArgs (qS : Nat) : Args CryptoOp (ScalarEnv qS)
    [message, boundedNat qS, .list (.pair message (boundedNat qS))] :=
  .cons v2 (.cons (.op (.finZero qS) .unit) (.cons (.fst (.snd (.snd v1))) .nil))

def writeState (qS : Nat) (signing : Bool) : Expr CryptoOp (BothEnv qS) (machineStore qS) :=
  if signing then
    .pair (.fst v2) (.pair (.snd v1) (.pair (.snd v0) (.cons v3 (.snd (.snd (.snd v2))))))
  else
    .pair (.fst v2) (.pair (.snd v1) (.pair (.snd v0) (.snd (.snd (.snd v2)))))

def signArgs (qS : Nat) : Args CryptoOp (WrittenEnv qS) [scalar, point₁, .nat] :=
  .cons (.fst v2) (.cons (.fst (.snd (.fst v3))) (.cons (.op (.finVal qS) (.fst v1)) .nil))

def hashArgs (qS : Nat) : Args CryptoOp (WrittenEnv qS) [scalar, point₁, point₁, .nat] :=
  .cons (.fst v2) (.cons (.fst (.fst v3)) (.cons (.snd (.snd (.fst v3)))
    (.cons (.op (.finVal qS) (.fst v1)) .nil)))

def body (qS : Nat) (signing : Bool) : Program CryptoOp (Machine.Effect (machineStore qS)) [message] point₁ :=
  .bind (.query .read .unit)
    (.bind (.call (cacheGet .messageEq .scalar) (scalarArgs qS))
      (.bind (.call (cacheGet .messageEq (.uniform qS)) (coinArgs qS))
        (.bind (.query .write (writeState qS signing))
          (if signing then .call (.ret signReply) (signArgs qS)
            else .call (.ret hashReply) (hashArgs qS)))))

theorem machineReply_eq (qS : Nat) (signing : Bool) : machineReply qS signing = body qS signing := by
  cases signing <;> rfl

theorem scalarArgs_description (allowance qS : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) :
    Expression.argumentsDescription allowance primitiveSize (scalarArgs qS) =
      primitiveSize CryptoOp.zero + 14 * allowance := by
  simp only [scalarArgs, v0, v1, Expression.argumentsDescription, Expression.descriptionBound, Expression.variableDescription]
  omega

theorem coinArgs_description (allowance qS : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) :
    Expression.argumentsDescription allowance primitiveSize (coinArgs qS) =
      primitiveSize (CryptoOp.finZero qS) + 20 * allowance := by
  simp only [coinArgs, v1, v2, Expression.argumentsDescription, Expression.descriptionBound, Expression.variableDescription]
  omega

theorem writeState_description (allowance qS : Nat) (signing : Bool)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) :
    Expression.descriptionBound allowance primitiveSize (writeState qS signing) =
      (if signing then 39 else 29) * allowance := by
  cases signing <;>
    simp only [writeState, Bool.false_eq_true, ite_false, ite_true, v0, v1, v2, v3,
      Expression.descriptionBound, Expression.variableDescription] <;> omega

theorem signArgs_description (allowance qS : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) :
    Expression.argumentsDescription allowance primitiveSize (signArgs qS) =
      primitiveSize (CryptoOp.finVal qS) + 30 * allowance := by
  simp only [signArgs, v1, v2, v3, Expression.argumentsDescription, Expression.descriptionBound, Expression.variableDescription]
  omega

theorem hashArgs_description (allowance qS : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) :
    Expression.argumentsDescription allowance primitiveSize (hashArgs qS) =
      primitiveSize (CryptoOp.finVal qS) + 42 * allowance := by
  simp only [hashArgs, v1, v2, v3, Expression.argumentsDescription, Expression.descriptionBound, Expression.variableDescription]
  omega

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

theorem scalarArgs_denote (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS)) :
    (scalarArgs qS).denote (arithmetic F G₁ G₂ M M cost) env = (env.2.1, 0, env.1.2.1, ()) := rfl

theorem coinArgs_denote (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ScalarEnv qS)) :
    (coinArgs qS).denote (arithmetic F G₁ G₂ M M cost) env = (env.2.2.1, 0, env.2.1.2.2.1, ()) := rfl

theorem writeState_denote (qS : Nat) (signing : Bool) (env : Env (cryptoBase F G₁ G₂ M M) (BothEnv qS)) :
    (writeState qS signing).denote (arithmetic F G₁ G₂ M M cost) env =
      (env.2.2.1.1, env.2.1.2, env.1.2,
        if signing then env.2.2.2.1 :: env.2.2.1.2.2.2 else env.2.2.1.2.2.2) := by
  cases signing <;> rfl

theorem signArgs_denote (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (WrittenEnv qS)) :
    (signArgs qS).denote (arithmetic F G₁ G₂ M M cost) env =
      (env.2.2.1.1, env.2.2.2.1.1.2.1, env.2.1.1.val, ()) := rfl

theorem hashArgs_denote (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (WrittenEnv qS)) :
    (hashArgs qS).denote (arithmetic F G₁ G₂ M M cost) env =
      (env.2.2.1.1, env.2.2.2.1.1.1, env.2.2.2.1.1.2.2, env.2.1.1.val, ()) := rfl

include localLaws dataLaws primitiveBound sizes mono

theorem scalarArgs_cost (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ReadEnv qS))
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env (ReadEnv qS)) env ≤ width)
    (ht : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (scalarArgs qS)) env ≤
      zeroTime + 32 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
    dataLaws primitiveBound (scalarArgs qS) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [scalarArgs, v0, v1, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env, ReadEnv,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

theorem coinArgs_cost (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (ScalarEnv qS))
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty (boundedNat qS)) (0 : Fin (qS + 1)) ≤ width)
    (hi : Q.size (rep.env (ScalarEnv qS)) env ≤ width)
    (ht : (primitiveBound (CryptoOp.finZero qS)).time () ≤ zeroTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (coinArgs qS)) env ≤
      zeroTime + 32 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
    dataLaws primitiveBound (coinArgs qS) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [coinArgs, v1, v2, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env, ScalarEnv, ReadEnv, ScalarResult,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

include lists in
theorem writeState_cost (qS : Nat) (signing : Bool)
    (env : Env (cryptoBase F G₁ G₂ M M) (BothEnv qS))
    (width : Nat) (hh : header ≤ width) (hi : Q.size (rep.env (BothEnv qS)) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (writeState qS signing)) env ≤
      64 * overhead (32 * width) := by
  cases signing
  · change Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (.pair (.fst v2) (.pair (.snd v1) (.pair (.snd v0) (.snd (.snd (.snd v2))))))) env ≤ _
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
      dataLaws primitiveBound _ env).trans ?_
    have hprod := @sizes.prod_le
    have hfst := @sizes.fst_le
    have hsnd := @sizes.snd_le
    have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
    dsimp only [v0, v1, v2, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
      LanguageRepresentation.ty, LanguageRepresentation.env, BothEnv, CoinResult, ScalarEnv, ScalarResult, ReadEnv,
      Expr.denote, Var.get] at *
    grind only
  · change Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (.pair (.fst v2) (.pair (.snd v1) (.pair (.snd v0) (.cons v3 (.snd (.snd (.snd v2)))))))) env ≤ _
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
      dataLaws primitiveBound _ env).trans ?_
    have hprod := @sizes.prod_le
    have hfst := @sizes.fst_le
    have hsnd := @sizes.snd_le
    have hcons := @lists.cons_le
    have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
    dsimp only [v0, v1, v2, v3, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.consBound,
      LanguageRepresentation.ty, LanguageRepresentation.env, BothEnv, CoinResult, ScalarEnv, ScalarResult, ReadEnv,
      Expr.denote, Var.get] at *
    grind only

theorem signArgs_cost (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (WrittenEnv qS))
    (width conversionTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hn : ∀ n : Fin (qS + 1), Q.size rep.data.nat n.val ≤ width)
    (hi : Q.size (rep.env (WrittenEnv qS)) env ≤ width)
    (ht : ∀ n : Fin (qS + 1), (primitiveBound (CryptoOp.finVal qS)).time n ≤ conversionTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (signArgs qS)) env ≤
      conversionTime + 64 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
    dataLaws primitiveBound (signArgs qS) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [signArgs, v1, v2, v3, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env, WrittenEnv, BothEnv, CoinResult,
    ScalarEnv, ReadEnv, ScalarResult, Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

theorem hashArgs_cost (qS : Nat) (env : Env (cryptoBase F G₁ G₂ M M) (WrittenEnv qS))
    (width conversionTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hn : ∀ n : Fin (qS + 1), Q.size rep.data.nat n.val ≤ width)
    (hi : Q.size (rep.env (WrittenEnv qS)) env ≤ width)
    (ht : ∀ n : Fin (qS + 1), (primitiveBound (CryptoOp.finVal qS)).time n ≤ conversionTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (hashArgs qS)) env ≤
      conversionTime + 64 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive localLaws
    dataLaws primitiveBound (hashArgs qS) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [hashArgs, v1, v2, v3, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env, WrittenEnv, BothEnv, CoinResult,
    ScalarEnv, ReadEnv, ScalarResult, Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

end Signatures.Runtime.Coron.ReplyCompiler

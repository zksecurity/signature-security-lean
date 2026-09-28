import Signatures.Runtime.AGMInitialization
import Signatures.Runtime.AGMExecutionRefinement

/-! Complete good-branch target code: private full-domain initialization, store construction,
public-key/fixed-data source call, adaptive simulation, and extraction. The enclosing package
loads both the source's fixed data and the canonical key enumeration. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

abbrev dlogInputs : List (Ty CryptoAtom) := [point₁, point₁, point₂, point₂]

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v5 {a b c d e f Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: Γ) f :=
  .var (.there (.there (.there (.there (.there .here)))))
private def v6 {a b c d e f g Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there (.there .here))))))

variable {indexTy messageTy dataTy : Ty CryptoAtom} {randomBound : Nat}

def goodInitial : Expr CryptoOp (dlogInputs ++ [dataTy, .list indexTy])
    (oracleStore indexTy messageTy (goodConfig indexTy)) :=
  .pair (.pair v0 (.pair v1 .nil)) (.pair .nil .nil)

def goodBody (n : Nat) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound) [point₂, dataTy] (outputTy messageTy)) :
    Program CryptoOp (Machine.Effect (oracleStore indexTy messageTy (goodConfig indexTy)))
      (dlogInputs ++ [dataTy, .list indexTy]) scalar :=
  .bind (.call (sampleKeyed (oracleStore indexTy messageTy (goodConfig indexTy)) n) (.cons v5 .nil))
    (.bind (.query .write (.pair (.pair v1 (.pair v2 v0)) (.pair .nil .nil)))
      (.call (goodExecution eq weight source) (.cons v5 (.cons v6 (.cons v1 .nil)))))

def goodCode (n : Nat) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound) [point₂, dataTy] (outputTy messageTy)) :
    Machine.Code (dlogInputs ++ [dataTy, .list indexTy]) scalar where
  store := oracleStore indexTy messageTy (goodConfig indexTy)
  init := goodInitial
  body := goodBody n eq weight source

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

theorem goodCode_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (n : Nat) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound) [point₂, dataTy] (outputTy messageTy))
    (g X : G₁) (g₂ pk : G₂) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) :
    (goodCode n eq weight source).run cost sampling (g, X, g₂, pk, data, keys, ()) = (do
      let tab ← ((sampleKeyed (oracleStore indexTy messageTy (goodConfig indexTy)) n).run
        (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
        (keys, ())).run ((g, X, []), [], [])
      let z ← ((goodExecution eq weight source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
        (pk, data, tab.1.value, ())).run ((g, X, tab.1.value), [], [])
      pure ⟨z.1.value, tab.1.steps + z.1.steps + 59⟩) := by
  unfold goodCode Machine.Code.run goodBody
  generalize (sampleKeyed (oracleStore indexTy messageTy (goodConfig indexTy)) n) = draw
  generalize goodExecution eq weight source = execute
  dsimp [goodInitial, Program.run, Args.run, Expr.run, v0, v1, v2, v5, v6,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext tab
  congr 1
  funext z
  apply congrArg pure
  apply congrArg (Run.mk _)
  omega

def goodCodeBound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime n : Nat) (queries : Fin 3 → Nat) (gamma xi e w : Nat) : Nat :=
  sampleKeyedBound cost sampling n n +
    goodExecutionBound cost sampling randomBound localTime n queries gamma xi e w + 59

variable {I N : Type} {cost : PrimitiveCosts}
  {index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I}
  {message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N}
  {localTime gammaLength xiLength : Nat} {queries : Fin 3 → Nat}
  {adv : Model.LazyAGM.Adversary F I N G₁ G₂}

theorem SourceCertificate.goodCode_bound
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (e w : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (g X : G₁) (g₂ pk : G₂) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M)))
    (z : Run F) (hz : z ∈ support ((goodCode keys.length eq weight cert.code).run cost sampling
      (g, X, g₂, pk, cert.data, keys, ()))) :
    z.steps ≤ goodCodeBound cost sampling randomBound localTime keys.length queries gammaLength xiLength e w := by
  rw [goodCode_run] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨tab, ht, r, hr, rfl⟩ := hz
  have hs := sampleKeyed_bound cost sampling (oracleStore indexTy messageTy (goodConfig indexTy))
    keys.length keys ((g, X, []), [], []) tab ht
  have hb := cert.goodExecution_bound sampling eq weight e w heq hw g X pk tab.1.value r hr
  rw [hs.2.1] at hb
  exact Nat.add_le_add_right (Nat.add_le_add hs.2.2 hb.2.2) 59

theorem SourceCertificate.goodCode_erase [Fintype I] [DecidableEq I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (g X : G₁) (g₂ pk : G₂) :
    Run.value <$> (goodCode (Fintype.card I) eq weight cert.code).run cost sampling
      (g, X, g₂, pk, cert.data, canonicalKeys index.symm, ()) =
      Model.LazyAGM.goodReduction w adv g X g₂ pk := by
  let execute (table : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
    (fun z => z.1.value) <$>
      (((goodExecution eq weight cert.code).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (goodConfig indexTy)))
        (pk, cert.data, table, ())).run ((g, X, table), [], []))
  have ht := congrArg (Functor.map Prod.fst)
    (sampleKeyed_native cost sampling (oracleStore indexTy messageTy (goodConfig indexTy))
      index.symm ((g, X, []), [], []))
  simp only [Functor.map_map] at ht
  rw [goodCode_run]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  change (_ >>= fun tab : Run ((tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) ×
    (oracleStore indexTy messageTy (goodConfig indexTy)).Value (cryptoBase F G₁ G₂ K M) =>
      execute tab.1.value) = _
  rw [← bind_map_left (fun tab : Run ((tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) ×
    (oracleStore indexTy messageTy (goodConfig indexTy)).Value (cryptoBase F G₁ G₂ K M) => tab.1.value)
    _ execute, ht, bind_map_left]
  unfold Model.LazyAGM.goodReduction
  apply bind_congr
  intro rho
  simpa only [execute, goodResult, bind_pure_comp] using
    cert.goodExecution_erase sampling eq heq weight w hw rho g X pk

def dlogWithin (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (budget : Nat) (solver : AlgebraicGroupModel.DLog11Adversary F G₁ G₂) : Prop :=
  Machine.Within (F := F) (K := K) (M := M) cost sampling dlogInputs scalar budget
    (fun env => solver env.1 env.2.1 env.2.2.1 env.2.2.2.1)

noncomputable def SourceCertificate.goodPackage [Fintype I]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Machine.Package (cryptoBase F G₁ G₂ K M) dlogInputs scalar where
  dataTypes := [cert.dataTy, .list indexTy]
  data := (cert.data, canonicalKeys index.symm, ())
  code := goodCode (Fintype.card I) eq weight cert.code

noncomputable def SourceCertificate.goodBudget [Fintype I]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (e w : Nat) : Nat :=
  goodCodeBound cost sampling randomBound localTime (Fintype.card I) queries gammaLength xiLength e w +
    (Env.load (Γ := [cert.dataTy, .list indexTy]) (cert.data, canonicalKeys index.symm, ())).steps + 6

/-- Full implementation of the exact named good DLog solver in the general closed machine.
Only source and primitive budgets are premises; setup, loading, simulation, and extraction
costs are all derived from the compiled code. -/
theorem SourceCertificate.goodWithin [Fintype I] [DecidableEq I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heqValue : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hwValue : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (e cWeight : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight) :
    dlogWithin (F := F) (K := K) (M := M) cost sampling (cert.goodBudget sampling e cWeight)
      (Model.LazyAGM.goodReduction w adv) := by
  refine ⟨cert.goodPackage eq weight, ?_, ?_⟩
  · intro env
    rcases env with ⟨g, X, g₂, pk, ⟨⟩⟩
    rw [Machine.Package.run_eq]
    simp only [Functor.map_map]
    change Run.value <$> (goodCode (Fintype.card I) eq weight cert.code).run cost sampling
      (g, X, g₂, pk, cert.data, canonicalKeys index.symm, ()) = _
    exact cert.goodCode_erase sampling eq heqValue weight w hwValue g X g₂ pk
  · intro env r hr
    rcases env with ⟨g, X, g₂, pk, ⟨⟩⟩
    rw [Machine.Package.run_eq] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    have hb := cert.goodCode_bound sampling eq weight e cWeight heq hw
      g X g₂ pk (canonicalKeys index.symm) z (by
        simpa only [canonicalKeys_length, goodPackage, Env.append] using hz)
    simp only [canonicalKeys_length] at hb
    exact Nat.add_le_add_right (Nat.add_le_add_right hb _) 6

end Signatures.Runtime.AGM

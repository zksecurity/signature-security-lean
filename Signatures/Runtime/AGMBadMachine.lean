import Signatures.Runtime.AGMGoodMachine
import Signatures.Runtime.MaskedBases

/-! Complete bad-branch target code. Randomness is drawn in the native reduction's
order: kappa, the entire a table, then the entire b table. The source receives only
the computed public key kappa * g2 and its fixed data. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.AGM

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private def v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))
private def v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))
private def v4 {a b c d e Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: Γ) e :=
  .var (.there (.there (.there (.there .here))))
private def v6 {a b c d e f g Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: Γ) g :=
  .var (.there (.there (.there (.there (.there (.there .here))))))
private def v7 {a b c d e f g h Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: h :: Γ) h :=
  .var (.there (.there (.there (.there (.there (.there (.there .here)))))))
private def v9 {a b c d e f g h i j Γ} : Expr CryptoOp (a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: Γ) j :=
  .var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))

variable {indexTy messageTy dataTy : Ty CryptoAtom} {randomBound : Nat}

def badInitial : Expr CryptoOp (dlogInputs ++ [dataTy, .list indexTy])
    (oracleStore indexTy messageTy (badConfig indexTy)) :=
  .pair (.pair (.op .zero .unit) .nil) (.pair .nil .nil)

def badBody (n : Nat) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound) [point₂, dataTy] (outputTy messageTy)) :
    Program CryptoOp (Machine.Effect (oracleStore indexTy messageTy (badConfig indexTy)))
      (dlogInputs ++ [dataTy, .list indexTy]) scalar :=
  .bind (.query .scalar .unit)
    (.bind (.call (sampleKeyed (oracleStore indexTy messageTy (badConfig indexTy)) n) (.cons v6 .nil))
      (.bind (.call (sampleKeyed (oracleStore indexTy messageTy (badConfig indexTy)) n) (.cons v7 .nil))
        (.bind (.call (.ret (maskedBases eq)) (.cons v3 (.cons v4 (.cons v1 (.cons v0 .nil)))))
          (.bind (.query .write (.pair (.pair v3 v0) (.pair .nil .nil)))
            (.call (badExecution eq weight source)
              (.cons (.op .scale₂ (.pair v4 v7)) (.cons v9 (.cons v3 (.cons v2 .nil)))))))))

def badCode (n : Nat) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound) [point₂, dataTy] (outputTy messageTy)) :
    Machine.Code (dlogInputs ++ [dataTy, .list indexTy]) scalar where
  store := oracleStore indexTy messageTy (badConfig indexTy)
  init := badInitial
  body := badBody n eq weight source

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

theorem badCode_run (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (n : Nat) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar)
    (source : Program CryptoOp (Command indexTy messageTy randomBound) [point₂, dataTy] (outputTy messageTy))
    (g X : G₁) (g₂ X₂ : G₂) (data : dataTy.Value (cryptoBase F G₁ G₂ K M))
    (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M))) :
    (badCode n eq weight source).run cost sampling (g, X, g₂, X₂, data, keys, ()) = (do
      let kappa ← ($ᵗ F : ProbComp F)
      let a ← ((sampleKeyed (oracleStore indexTy messageTy (badConfig indexTy)) n).run
        (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
        (keys, ())).run ((0, []), [], [])
      let b ← ((sampleKeyed (oracleStore indexTy messageTy (badConfig indexTy)) n).run
        (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
        (keys, ())).run a.2
      let H := (maskedBases eq).run (arithmetic F G₁ G₂ K M cost) (g, X, a.1.value, b.1.value, ())
      let z ← ((badExecution eq weight source).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
        (kappa • g₂, data, a.1.value, b.1.value, ())).run ((kappa, H.value), [], [])
      pure ⟨z.1.value, a.1.steps + b.1.steps + H.steps + z.1.steps +
        sampling.scalar + cost.field + cost.scalar₂ + 111⟩) := by
  unfold badCode Machine.Code.run badBody
  generalize (sampleKeyed (oracleStore indexTy messageTy (badConfig indexTy)) n) = draw
  generalize maskedBases eq = bases
  generalize badExecution eq weight source = execute
  dsimp [badInitial, Program.run, Args.run, Expr.run, v0, v1, v2, v3, v4, v6, v7, v9,
    Var.get, Var.depth, StateT.run, StateT.bind, StateT.pure, Machine.effects, arithmetic, CryptoOp.price]
  simp only [bind_assoc, pure_bind, bind_map_left]
  congr 1
  funext kappa
  congr 1
  funext a
  congr 1
  funext b
  congr 1
  funext z
  apply congrArg pure
  apply congrArg (Run.mk _)
  omega

def badCodeBound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (randomBound localTime n : Nat) (queries : Fin 3 → Nat) (xi e w : Nat) : Nat :=
  2 * sampleKeyedBound cost sampling n n + maskedBasesBound cost n n e +
    badExecutionBound cost sampling randomBound localTime n n n queries xi e w +
    sampling.scalar + cost.field + cost.scalar₂ + 111

variable {I N : Type} {cost : PrimitiveCosts}
  {index : indexTy.Value (cryptoBase F G₁ G₂ K M) ≃ I}
  {message : messageTy.Value (cryptoBase F G₁ G₂ K M) ≃ N}
  {localTime gammaLength xiLength : Nat} {queries : Fin 3 → Nat}
  {adv : Model.LazyAGM.Adversary F I N G₁ G₂}

theorem SourceCertificate.badCode_bound
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (e w : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ w)
    (g X : G₁) (g₂ X₂ : G₂) (keys : List (indexTy.Value (cryptoBase F G₁ G₂ K M)))
    (z : Run F) (hz : z ∈ support ((badCode keys.length eq weight cert.code).run cost sampling
      (g, X, g₂, X₂, cert.data, keys, ()))) :
    z.steps ≤ badCodeBound cost sampling randomBound localTime keys.length queries xiLength e w := by
  rw [badCode_run] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨kappa, _, a, ha, b, hb, r, hr, rfl⟩ := hz
  have hsa := sampleKeyed_bound cost sampling (oracleStore indexTy messageTy (badConfig indexTy))
    keys.length keys ((0, []), [], []) a ha
  have hsb := sampleKeyed_bound cost sampling (oracleStore indexTy messageTy (badConfig indexTy))
    keys.length keys a.2 b hb
  have hm := maskedBases_steps_le cost eq e heq g X a.1.value b.1.value
  have hex := cert.badExecution_bound sampling eq weight e w heq hw kappa (kappa • g₂)
    ((maskedBases eq).run (arithmetic F G₁ G₂ K M cost) (g, X, a.1.value, b.1.value, ())).value
    a.1.value b.1.value r hr
  rw [maskedBases_length, hsa.2.1, hsb.2.1] at hex
  rw [hsa.2.1, hsb.2.1] at hm
  dsimp only [badCodeBound]
  have h := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsa.2.2 hsb.2.2) hm) hex.2.2
  omega

theorem SourceCertificate.badCode_erase [Fintype I] [DecidableEq I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heq : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (g X : G₁) (g₂ X₂ : G₂) :
    Run.value <$> (badCode (Fintype.card I) eq weight cert.code).run cost sampling
      (g, X, g₂, X₂, cert.data, canonicalKeys index.symm, ()) =
      Model.LazyAGM.badReduction w adv g X g₂ X₂ := by
  let execute (kappa : F) (a b : (tableTy indexTy).Value (cryptoBase F G₁ G₂ K M)) : ProbComp F :=
    (fun z => z.1.value) <$>
      (((badExecution eq weight cert.code).run (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
        (kappa • g₂, cert.data, a, b, ())).run
          ((kappa, ((maskedBases eq).run (arithmetic F G₁ G₂ K M cost) (g, X, a, b, ())).value), [], []))
  rw [badCode_run]
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  unfold Model.LazyAGM.badReduction
  apply bind_congr
  intro kappa
  rw [sampleKeyed_bind_native cost sampling (oracleStore indexTy messageTy (badConfig indexTy))
    index.symm ((0, []), [], []) (fun a state =>
      (((sampleKeyed (oracleStore indexTy messageTy (badConfig indexTy)) (Fintype.card I)).run
        (arithmetic F G₁ G₂ K M cost)
        (Machine.effects sampling (oracleStore indexTy messageTy (badConfig indexTy)))
        (canonicalKeys index.symm, ())).run state) >>= fun b => execute kappa a b.1.value)]
  apply bind_congr
  intro a
  rw [sampleKeyed_bind_native cost sampling (oracleStore indexTy messageTy (badConfig indexTy))
    index.symm ((0, []), [], [])
      (fun b _ => execute kappa (canonicalKeys (fun i => (index.symm i, a i))) b)]
  apply bind_congr
  intro b
  dsimp only [execute]
  rw [maskedBases_native cost eq heq index.symm index.symm.injective]
  simpa only [badResult, bind_pure_comp] using
    cert.badExecution_erase sampling eq heq weight w hw a b (fun i => a i • X + b i • g) kappa (kappa • g₂)

noncomputable def SourceCertificate.badPackage [Fintype I]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) :
    Machine.Package (cryptoBase F G₁ G₂ K M) dlogInputs scalar where
  dataTypes := [cert.dataTy, .list indexTy]
  data := (cert.data, canonicalKeys index.symm, ())
  code := badCode (Fintype.card I) eq weight cert.code

noncomputable def SourceCertificate.badBudget [Fintype I]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (e w : Nat) : Nat :=
  badCodeBound cost sampling randomBound localTime (Fintype.card I) queries xiLength e w +
    (Env.load (Γ := [cert.dataTy, .list indexTy]) (cert.data, canonicalKeys index.symm, ())).steps + 6

/-- The exact bad DLog solver is within the general closed-machine resource class.
The two table samplers, group construction, public key, and fixed-data load are charged;
only source and primitive contracts are assumptions. -/
theorem SourceCertificate.badWithin [Fintype I] [DecidableEq I]
    [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
    (cert : SourceCertificate cost index message randomBound localTime queries gammaLength xiLength adv)
    (sampling : Machine.SamplingCosts) (eq : Expr CryptoOp [indexTy, indexTy] .bool)
    (heqValue : ∀ x y, eq.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y))
    (weight : Expr CryptoOp [indexTy, messageTy] scalar) (w : I → N → F)
    (hwValue : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).value = w (index i) (message m))
    (e cWeight : Nat)
    (heq : ∀ x y, (eq.run (arithmetic F G₁ G₂ K M cost) (x, y, ())).steps ≤ e)
    (hw : ∀ i m, (weight.run (arithmetic F G₁ G₂ K M cost) (i, m, ())).steps ≤ cWeight) :
    dlogWithin (F := F) (K := K) (M := M) cost sampling (cert.badBudget sampling e cWeight)
      (Model.LazyAGM.badReduction w adv) := by
  refine ⟨cert.badPackage eq weight, ?_, ?_⟩
  · intro env
    rcases env with ⟨g, X, g₂, X₂, ⟨⟩⟩
    rw [Machine.Package.run_eq]
    simp only [Functor.map_map]
    change Run.value <$> (badCode (Fintype.card I) eq weight cert.code).run cost sampling
      (g, X, g₂, X₂, cert.data, canonicalKeys index.symm, ()) = _
    exact cert.badCode_erase sampling eq heqValue weight w hwValue g X g₂ X₂
  · intro env r hr
    rcases env with ⟨g, X, g₂, X₂, ⟨⟩⟩
    rw [Machine.Package.run_eq] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    have hb := cert.badCode_bound sampling eq weight e cWeight heq hw
      g X g₂ X₂ (canonicalKeys index.symm) z (by
        simpa only [canonicalKeys_length, badPackage, Env.append] using hz)
    simp only [canonicalKeys_length] at hb
    exact Nat.add_le_add_right (Nat.add_le_add_right hb _) 6

end Signatures.Runtime.AGM

import Proofs.Runtime.HeapBudget
import Proofs.Runtime.HeapData

/-! Closed packages load their encoded input and fixed data, build the combined
register frame, initialize storage and execute the compiled body. All online
work is charged. Abstract-to-bit encoding is the representation boundary, not
an uncharged operation performed by the runner. -/

namespace Signatures.Runtime.HeapMachine

open HeapBits SharedHeap OracleComp WeierstrassCurve

structure Package where
  data : List HeapExpression.Code
  code : Code

def Package.run (pack : Package) (input : List HeapExpression.Code) :
    OracleComp BitRejection.bitSpec (Run HeapExpression.Result × Bool) := do
  let loaded := HeapArguments.run input [] empty
  match loaded.value with
  | none => pure (⟨none, loaded.steps+1⟩, false)
  | some (frame, store) =>
    let fixed := HeapArguments.run pack.data [] store
    match fixed.value with
    | none => pure (⟨none, loaded.steps+fixed.steps+2⟩, false)
    | some (tail, next) =>
      let combined := HeapBits.append frame tail
      let out ← pack.code.run combined.value next
      pure (⟨out.1.value, loaded.steps+fixed.steps+combined.steps+out.1.steps+3⟩, out.2)

def packageFactor (w r k nodes registers : Nat) {Γ a} (code : Machine.Code Γ a) : Nat :=
  max (max (HeapData.envFactor w nodes registers) (budget w r k nodes code))
    (2*registers*(nodes+1)+4)

private theorem env_join {base : CryptoAtom → Type} {w : Nat}
    {leaf : (a : CryptoAtom) → List Bool → base a → Prop} {heap : List Node}
    {Γ Δ : List (Ty CryptoAtom)} {roots tail : List Address} {env : Env base Γ} {data : Env base Δ}
    (h : EnvRep w leaf heap roots env) (ht : EnvRep w leaf heap tail data) :
    EnvRep w leaf heap (roots ++ tail) (Env.append env data) := by
  induction h with
  | nil => exact ht
  | cons hx _ ih => exact .cons hx ih

private theorem bound_join {F G₁ G₂ K M : Type} {w : Nat} {Γ Δ : List (Ty CryptoAtom)}
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (data : Env (cryptoBase F G₁ G₂ K M) Δ)
    (he : NaturalRange.EnvBound w env) (hd : NaturalRange.EnvBound w data) :
    NaturalRange.EnvBound w (Env.append env data) := by
  induction Γ with
  | nil => exact hd
  | cons a Γ ih => exact ⟨he.1, ih env.2 he.2⟩

variable {r p₁ p₂ w : Nat} [Fact r.Prime] [Fact p₁.Prime] [Fact p₂.Prime]
  {W₁ : Affine (ZMod p₁)} {W₂ : Affine (ZMod p₂)} {K M : Type}
  (H₁ : AddSubgroup W₁.Point) (H₂ : AddSubgroup W₂.Point)
  (encodeK : K → BitVec w) (encodeM : M → BitVec w)

def compilePackage (k : Nat) {Γ a}
    (pack : Machine.Package (cryptoBase (ZMod r) H₁ H₂ K M) Γ a) : Package :=
  ⟨HeapData.encodeEnv H₁ H₂ encodeK encodeM pack.data, compile w r W₁ W₂ k pack.code⟩

variable [DecidableEq K] [DecidableEq M] [Module (ZMod r) H₁] [Module (ZMod r) H₂]
  [SampleableType (ZMod r)]

noncomputable def packageSemantics (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase (ZMod r) H₁ H₂ K M) Γ a)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ) :
    OracleComp BitRejection.bitSpec (Run (a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) × Bool) :=
  (fun out => (⟨out.1.value, out.1.steps+(Env.load pack.data).steps+Γ.length+2⟩, out.2)) <$>
    codeSemantics H₁ H₂ (w := w) k cost sampling pack.code (Env.append env pack.data)

theorem packageSemantics_support (k : Nat) (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase (ZMod r) H₁ H₂ K M) Γ a)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ)
    (out) (hout : out ∈ support (packageSemantics H₁ H₂ (w := w) k cost sampling pack env)) :
    out.1 ∈ support (pack.run cost sampling env) := by
  simp only [packageSemantics, support_map, Set.mem_image] at hout
  obtain ⟨source, hs, rfl⟩ := hout
  rw [Machine.Package.run_eq, support_map]
  exact Set.mem_image_of_mem _ (codeSemantics_support H₁ H₂ k cost sampling pack.code _ source hs)

/-- The caller supplies encoded input data, not an initialized heap or store.
The extra input-load term is explicit because the source machine's package
budget charges fixed-data loading but treats its input registers as supplied. -/
theorem compilePackage_costed
    (hr : r*r ≤ 2^w) (h₁ : p₁*p₁ ≤ 2^w) (h₂ : p₂*p₂ ≤ 2^w)
    (hr' : 2 < r) (h₁' : 2 < p₁) (h₂' : 2 < p₂)
    (hk : Function.Injective encodeK) (hm : Function.Injective encodeM)
    (cost : PrimitiveCosts) (k : Nat) (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n))
    {Γ a} (pack : Machine.Package (cryptoBase (ZMod r) H₁ H₂ K M) Γ a)
    (env : Env (cryptoBase (ZMod r) H₁ H₂ K M) Γ)
    (bits B : Nat) (he : NaturalRange.EnvBound bits env)
    (hd : NaturalRange.EnvBound bits pack.data) (hwidth : bits+B ≤ w)
    (hb : ∀ out ∈ support (pack.run cost sampling env), out.steps ≤ B) :
    let inputSize := (Env.load env).steps
    let factor := packageFactor w r k (inputSize+B) (Γ.length+pack.dataTypes.length) pack.code
    QueryTreeRel (fun actual source =>
      HeapExpression.ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) []
        (inputSize+source.1.steps) source.1.value actual.1 ∧
      actual.2 = source.2 ∧
      actual.1.steps ≤ (inputSize+source.1.steps+1)*factor ∧
      actual.1.steps ≤ (inputSize+B+1)*factor)
      ((compilePackage H₁ H₂ encodeK encodeM k pack).run (HeapData.encodeEnv H₁ H₂ encodeK encodeM env))
      (packageSemantics H₁ H₂ (w := w) k cost sampling pack env) := by
  let inputSize := (Env.load env).steps
  let dataSize := (Env.load pack.data).steps
  let codeBudget := B-dataSize-Γ.length-2
  let nodes := inputSize+B
  let registers := Γ.length+pack.dataTypes.length
  let factor := packageFactor w r k nodes registers pack.code
  have hfull : ∀ out ∈ support (pack.code.run cost sampling (Env.append env pack.data)),
      out.steps+dataSize+Γ.length+2 ≤ B := by
    intro out hout
    apply hb ⟨out.value, out.steps+dataSize+Γ.length+2⟩
    rw [Machine.Package.run_eq, support_map]
    exact Set.mem_image_of_mem _ hout
  obtain ⟨someOut, hsome⟩ := support_nonempty (pack.code.run cost sampling (Env.append env pack.data))
  have hdata : dataSize+codeBudget ≤ B := by
    have := hfull someOut hsome
    dsimp [codeBudget]
    omega
  have hcBudget : ∀ out ∈ support (pack.code.run cost sampling (Env.append env pack.data)),
      out.steps ≤ codeBudget := by
    intro out hout
    have := hfull out hout
    dsimp [codeBudget]
    omega
  have hinput := HeapData.encodeEnv_costed H₁ H₂ encodeK encodeM env [] empty empty_represents trivial
    (NaturalRange.env_mono (by omega) env he) nodes registers (by dsimp [nodes]; omega) (by dsimp [registers]; omega)
  obtain ⟨⟨first, roots, st₁, hv₁, hs₁, hw₁, he₁, hlen₁⟩, hcost₁⟩ := hinput
  simp only [List.nil_append] at hs₁ hw₁ he₁
  have hfixed := HeapData.encodeEnv_costed H₁ H₂ encodeK encodeM pack.data first st₁ hs₁ hw₁
    (NaturalRange.env_mono (by omega) pack.data hd) nodes registers
    (by change first.length ≤ inputSize at hlen₁; change first.length+dataSize ≤ nodes; dsimp [nodes]; omega)
    (by dsimp [registers]; omega)
  obtain ⟨⟨second, tail, st₂, hv₂, hs₂, hw₂, he₂, hlen₂⟩, hcost₂⟩ := hfixed
  have hnodes : (first ++ second).length+codeBudget ≤ nodes := by
    change first.length ≤ inputSize at hlen₁
    change second.length ≤ dataSize at hlen₂
    simp only [List.length_append]
    dsimp [nodes]
    omega
  have hjoined := env_join (he₁.append second) he₂
  have hrun := compile_costed H₁ H₂ encodeK encodeM hr h₁ h₂ hr' h₁' h₂' hk hm cost k sampling hsampling
    pack.code (first ++ second) (roots ++ tail) (Env.append env pack.data) st₂ hs₂ hw₂ hjoined
    bits codeBudget (bound_join env pack.data he hd) (by omega) hcBudget
  have hcodeFactor : budget w r k ((first ++ second).length+codeBudget) pack.code ≤ factor :=
    (budget_mono w r k hnodes pack.code).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hloadFactor : HeapData.envFactor w nodes registers ≤ factor :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hcost₁ := hcost₁.trans (Nat.mul_le_mul_left _ hloadFactor)
  have hcost₂ := hcost₂.trans (Nat.mul_le_mul_left _ hloadFactor)
  have hframe := frameBits_length roots nodes (fun addr h =>
    ((he₁.append second).addresses addr h).trans_le (by omega))
  have hlen : roots.length ≤ registers := by rw [he₁.length]; dsimp [registers]; omega
  have happend : (HeapBits.append (frameBits roots) (frameBits tail)).steps+3 ≤ factor := by
    rw [append_steps]
    have := Nat.mul_le_mul_right (nodes+1) hlen
    have hf : 2*registers*(nodes+1)+4 ≤ factor := le_max_right _ _
    simp only [Nat.mul_assoc] at hf
    omega
  have hfinal := hrun.with_support.map
    (fun out => (⟨out.1.value,
      (HeapArguments.run (HeapData.encodeEnv H₁ H₂ encodeK encodeM env) [] empty).steps+
      (HeapArguments.run (HeapData.encodeEnv H₁ H₂ encodeK encodeM pack.data) [] st₁).steps+
      (HeapBits.append (frameBits roots) (frameBits tail)).steps+out.1.steps+3⟩, out.2))
    (fun out => (⟨out.1.value, out.1.steps+dataSize+Γ.length+2⟩, out.2))
    (S := fun (actual : Run HeapExpression.Result × Bool)
      (source : Run (a.Value (cryptoBase (ZMod r) H₁ H₂ K M)) × Bool) =>
      HeapExpression.ResultSpec w (3*w+1) (atomRep H₁ H₂ encodeK encodeM) []
        (inputSize+source.1.steps) source.1.value actual.1 ∧ actual.2 = source.2 ∧
      actual.1.steps ≤ (inputSize+source.1.steps+1)*factor ∧ actual.1.steps ≤ (inputSize+B+1)*factor)
    (by
      intro actual source h
      have hsource := hfull source.1 (codeSemantics_support H₁ H₂ k cost sampling pack.code _ source h.2.1)
      have hc := h.2.2.2.2.1.trans (Nat.mul_le_mul_left _ hcodeFactor)
      have hb' : source.1.steps+dataSize+Γ.length+2 ≤ B := hsource
      have total :
          (HeapArguments.run (HeapData.encodeEnv H₁ H₂ encodeK encodeM env) [] empty).steps+
          (HeapArguments.run (HeapData.encodeEnv H₁ H₂ encodeK encodeM pack.data) [] st₁).steps+
          (HeapBits.append (frameBits roots) (frameBits tail)).steps+actual.1.steps+3 ≤
            (inputSize+(source.1.steps+dataSize+Γ.length+2)+1)*factor := by
        change _ ≤ inputSize*factor at hcost₁
        change _ ≤ dataSize*factor at hcost₂
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      refine ⟨?_, h.2.2.2.1, total, total.trans (Nat.mul_le_mul_right factor (by omega))⟩
      obtain ⟨more, root, last, ho, hs, hw, hx, hmore⟩ := h.2.2.1
      refine ⟨first ++ second ++ more, root, last, ho, ?_, ?_, ?_, ?_⟩
      · simpa using hs
      · simpa using hw
      · simpa using hx
      · change first.length ≤ inputSize at hlen₁
        change second.length ≤ dataSize at hlen₂
        simp only [List.length_append]
        omega)
  simp only [Package.run, compilePackage, hv₁, hv₂, append_value, packageSemantics, bind_pure_comp]
  convert hfinal using 1
  simp only [frameBits, List.flatMap_append]

end Signatures.Runtime.HeapMachine

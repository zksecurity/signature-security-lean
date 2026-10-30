import Signatures.SynchronizedPS.Game
import Signatures.Model.DLog11

/-! The three `(1,1)`-DLog solvers behind synchronized PS security. Each runs the attacker
through its grouped proof view against a simulated signer, then reads the challenge off the
forgery. With every hash exponent `ρ(t)` known, a forgery `σ*` on `(t*, m*)` has exponent
`const + x·lin + y·lin'`, and verification demands `(x + y·m*)·ρ(t*)`, so `x·D + y·D' = K`. The challenge is placed as `x` (solve when
`D ≠ 0`), as `y` (solve when `D' ≠ 0`), or in the hashes `H(t) = a(t)•Z₁ + b(t)•g₁` with both
keys known, where `D = D' = 0` becomes a linear equation in the hidden slopes `a`. -/

open OracleComp OracleSpec Model Model.LazyAGM

namespace SynchronizedPS.Reduction

variable {F Period G₁ G₂ : Type} [Field F] [DecidableEq F] [Fintype Period] [DecidableEq Period]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

abbrev Adversary (F Period G₁ G₂ : Type) [Field F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] :=
  DirectAGM.AdversaryWith F Period (Period × F) (Forgery F Period) G₁ G₂

/-- Run the attacker's proof view with fixed hash and signing tables; the transcripts record
the replies it saw, and its output explains the forged signature over `g₁` and those replies. -/
def run (adversary : Adversary F Period G₁ G₂) (g₁ : G₁) (publicKey : G₂ × G₂)
    (hash : Period → G₁) (sign : Period × F → G₁) :
    ProbComp (Output F (Forgery F Period) × Transcript Period (Period × F) G₁) :=
  (simulateQ (fixedImpl hash sign)
    ((DirectAGM.ProofView.adversaryWith g₁ (fun pk : G₂ × G₂ => [pk.1, pk.2]) adversary).main publicKey)).run ([], [])

section Exponents
variable (out : Output F (Forgery F Period)) (tr : Transcript Period (Period × F) G₁) (ρ : Period → F)

/-- The forgery's exponent is `const + x·lin + y·lin'` when the hash exponents are `ρ`. -/
def const : F := out.β + (tr.1.mapIdx fun n reply => tokenCoeff out.γ n * ρ reply.1).sum
def lin : F := (tr.2.mapIdx fun n reply => tokenCoeff out.ξ n * ρ reply.1.1).sum
def lin' : F := (tr.2.mapIdx fun n reply => tokenCoeff out.ξ n * (ρ reply.1.1 * reply.1.2)).sum
/-- Verification against `(x + y·m*)·ρ(t*)` leaves `x·D + y·D' = K`. -/
def D : F := ρ out.mstar.1 - lin out tr ρ
def D' : F := ρ out.mstar.1 * out.mstar.2 - lin' out tr ρ
def K : F := const out tr ρ
/-- The attacked period's coefficient in `D`: one minus the weight the forgery puts on the
signature of that period. It is zero only when the forgery reuses that signature with weight
one, and then `D'`'s coefficient `m* − m` is nonzero for a fresh message. -/
def reuse : F :=
  1 - (tr.2.mapIdx fun n reply => if reply.1.1 = out.mstar.1 then tokenCoeff out.ξ n else 0).sum

end Exponents

variable [SampleableType F]

/-- Challenge as the first key: `pk = (Z₂, y•g₂)`, signatures `ρ(t)•Z₁ + (ρ(t)·y·m)•g₁`,
answer `x = (K − y·D')/D`. -/
noncomputable def challengeInX (adversary : Adversary F Period G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g₁ Z₁ g₂ Z₂ => do
  let y ← ($ᵗ F : ProbComp F)
  let ρ ← ($ᵗ (Period → F) : ProbComp (Period → F))
  let (out, tr) ← run adversary g₁ (Z₂, y • g₂) (fun t => ρ t • g₁)
    (fun m => ρ m.1 • Z₁ + (ρ m.1 * (y * m.2)) • g₁)
  pure ((K out tr ρ - y * D' out tr ρ) / D out tr ρ)

/-- Challenge as the second key: `pk = (x•g₂, Z₂)`, signatures `(ρ(t)·x)•g₁ + (ρ(t)·m)•Z₁`,
answer `y = (K − x·D)/D'`. -/
noncomputable def challengeInY (adversary : Adversary F Period G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g₁ Z₁ g₂ Z₂ => do
  let x ← ($ᵗ F : ProbComp F)
  let ρ ← ($ᵗ (Period → F) : ProbComp (Period → F))
  let (out, tr) ← run adversary g₁ (x • g₂, Z₂) (fun t => ρ t • g₁)
    (fun m => (ρ m.1 * x) • g₁ + (ρ m.1 * m.2) • Z₁)
  pure ((K out tr ρ - x * D out tr ρ) / D' out tr ρ)

/-- Challenge in the hashes: both keys known, `H(t) = a(t)•Z₁ + b(t)•g₁`, honest signing.
When `D = D' = 0`, the coefficient vector of `D` (or of `D'` if the attacked period's entry
vanishes) is nonzero, so `D = 0` is a linear equation `D(a)·z + D(b) = 0` in the challenge. -/
noncomputable def challengeInHashes (adversary : Adversary F Period G₁ G₂) :
    AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g₁ Z₁ g₂ _ => do
  let x ← ($ᵗ F : ProbComp F)
  let y ← ($ᵗ F : ProbComp F)
  let a ← ($ᵗ (Period → F) : ProbComp (Period → F))
  let b ← ($ᵗ (Period → F) : ProbComp (Period → F))
  let hash := fun t => a t • Z₁ + b t • g₁
  let (out, tr) ← run adversary g₁ (x • g₂, y • g₂) hash (fun m => (x + y * m.2) • hash m.1)
  pure (if reuse out tr ≠ 0 then -D out tr b / D out tr a else -D' out tr b / D' out tr a)

end SynchronizedPS.Reduction

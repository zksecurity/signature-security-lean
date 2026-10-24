import Proofs.Runtime.BackendCacheRead
import Proofs.Runtime.BackendWeightedCache

/-! Native private reads for weighted evaluation. These reads change only the
private cache; they add no attacker-visible transcript entry. The fallback is
constructed by scalar-zero code even on a hit, and the bad branch uses two
independent scalar draws on a miss. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Read

open BackendProgram

abbrev cacheTy (index value : Ty CryptoAtom) : Ty CryptoAtom := .list (.pair index value)
abbrev inputTy (index value : Ty CryptoAtom) : Ty CryptoAtom := .pair index (cacheTy index value)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def zeroCode (input : Ty CryptoAtom) : Q.Realizer (rep.ty input) (rep.ty scalar) (fun _ => (0 : F)) :=
  (Q.compose (data.unit (rep.ty input)) (primitive .zero)).castFunction (by funext x; rfl)

def pairZeroCode (input : Ty CryptoAtom) :
    Q.Realizer (rep.ty input) (rep.ty (.pair scalar scalar)) (fun _ => ((0 : F), (0 : F))) :=
  QP.pair (zeroCode rep data cost primitive input) (zeroCode rep data cost primitive input)

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

def goodRead : Code Q unifSpec iface (rep.ty (inputTy index.ty scalar))
    (rep.ty (.pair scalar (cacheTy index.ty scalar))) :=
  CacheRead.code rep data (index.code rep data cost primitive)
    (zeroCode rep data cost primitive (inputTy index.ty scalar)) sampling.scalar

def badRead : Code Q unifSpec iface (rep.ty (inputTy index.ty (.pair scalar scalar)))
    (rep.ty (.pair (.pair scalar scalar) (cacheTy index.ty (.pair scalar scalar)))) :=
  CacheRead.code rep data (index.code rep data cost primitive)
    (pairZeroCode rep data cost primitive (inputTy index.ty (.pair scalar scalar)))
    (PrivateCache.pairSampler rep data sampling)

theorem goodRead_denote (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F)) :
    (goodRead rep data cost primitive sampling index).denote (k, cache) =
      ((BLS.LazyAGM.Reduction.privateListOracle (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F))
        (.inr k)).run cache :=
  CacheRead.uniform rep data (index.code rep data cost primitive)
    (zeroCode rep data cost primitive (inputTy index.ty scalar)) sampling.scalar
    (sampling.scalar_denote ()) k cache

theorem badRead_denote (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F))) :
    (badRead rep data cost primitive sampling index).denote (k, cache) =
      ((BLS.LazyAGM.Reduction.privateListOracle (M := index.ty.Value (cryptoBase F G₁ G₂ K M)) (R := F × F))
        (.inr k)).run cache :=
  CacheRead.uniform rep data (index.code rep data cost primitive)
    (pairZeroCode rep data cost primitive (inputTy index.ty (.pair scalar scalar)))
    (PrivateCache.pairSampler rep data sampling) (PrivateCache.pairSampler_denote rep data sampling ()) k cache

theorem goodRead_hit_run (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × F))
    (value : F) (hit : cache.lookup k = some value) :
    (goodRead rep data cost primitive sampling index).run control queryCost (k, cache) =
      (goodRead rep data cost primitive other index).run control queryCost (k, cache) :=
  CacheRead.hit_run rep data (index.code rep data cost primitive)
    (zeroCode rep data cost primitive (inputTy index.ty scalar)) sampling.scalar other.scalar
    control queryCost k cache value hit

theorem badRead_hit_run (other : MachineCompiler.SamplingImplementation Q iface rep)
    (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
    (k : index.ty.Value (cryptoBase F G₁ G₂ K M))
    (cache : List (index.ty.Value (cryptoBase F G₁ G₂ K M) × (F × F)))
    (value : F × F) (hit : cache.lookup k = some value) :
    (badRead rep data cost primitive sampling index).run control queryCost (k, cache) =
      (badRead rep data cost primitive other index).run control queryCost (k, cache) :=
  CacheRead.hit_run rep data (index.code rep data cost primitive)
    (pairZeroCode rep data cost primitive (inputTy index.ty (.pair scalar scalar)))
    (PrivateCache.pairSampler rep data sampling) (PrivateCache.pairSampler rep data other)
    control queryCost k cache value hit

end Signatures.Runtime.WeightedAGM.Read

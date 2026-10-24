import Proofs.Runtime.BackendLazyAGMCache
import Proofs.Runtime.LazyAGMReply

/-! Implemented private-cache reads for extraction. These reads update only
the private association list; no attacker-visible transcript token is added.
All argument routing is constructed from the shared backend's local code. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

def readArgs {value : Ty CryptoAtom} (fallback : Expr CryptoOp [message, cacheTy value] value) :
    Args CryptoOp [message, cacheTy value] [message, value, cacheTy value] :=
  .cons v0 (.cons fallback (.cons v1 .nil))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))

def readFrame {value : Ty CryptoAtom} :
    Q.Realizer (rep.ty (.pair message (cacheTy value))) (rep.env [message, cacheTy value])
      (fun p => (p.1, p.2, ())) :=
  QP.pair (QP.fst _ _) (QP.pair (QP.snd _ _) (data.unit _))

@[irreducible] def backendRead {value : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value) :
    Code Q unifSpec iface (rep.ty (.pair message (cacheTy value))) (rep.ty (cacheResultTy value)) :=
  .seq (.atomic (readFrame rep data))
    (.seq (.atomic (QP.pair
      (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive (readArgs fallback)) (data.unit _)))
      (.seq (SampledCache.code rep data (arithmetic F G₁ G₂ M M cost) primitive rep.data.unit sampler .messageEq)
        (.atomic (QP.fst _ _))))

theorem backendRead_denote {value : Ty CryptoAtom}
    [SampleableType (value.Value (cryptoBase F G₁ G₂ M M))]
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (hsample : sampler.denote () = ($ᵗ (value.Value (cryptoBase F G₁ G₂ M M)) : ProbComp _))
    (m : M) (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M))) :
    (backendRead rep data cost primitive sampler fallback).denote (m, cache) =
      ((BLS.LazyAGM.Reduction.privateListOracle (M := M)
        (R := value.Value (cryptoBase F G₁ G₂ M M))) (.inr m)).run cache := by
  rw [backendRead]
  simp only [Code.denote, pure_bind]
  change ((SampledCache.code rep data (arithmetic F G₁ G₂ M M cost) primitive rep.data.unit sampler .messageEq).denote
    ((m, fallback.denote (arithmetic F G₁ G₂ M M cost) (m, cache, ()), cache, ()), ()) >>= fun p => pure p.1) = _
  rw [SampledCache.uniform rep data (arithmetic F G₁ G₂ M M cost) primitive rep.data.unit
    CryptoOp.messageEq sampler hsample (fun _ _ => rfl)]
  simp only [bind_map_left, bind_pure]
  rfl

variable [SampleableType F]
  (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)

@[irreducible] def backendGoodRead :
    Code Q unifSpec iface (rep.ty (.pair message (cacheTy scalar))) (rep.ty (cacheResultTy scalar)) :=
  backendRead rep data cost primitive samplingCode.scalar (.op .zero .unit)

@[irreducible] def backendBadRead :
    Code Q unifSpec iface (rep.ty (.pair message (cacheTy (.pair scalar scalar))))
      (rep.ty (cacheResultTy (.pair scalar scalar))) :=
  backendRead rep data cost primitive (pairSampler rep data samplingCode) (.pair (.op .zero .unit) (.op .zero .unit))

theorem backendGoodRead_denote (m : M) (cache : List (M × F)) :
    (backendGoodRead rep data cost primitive samplingCode).denote (m, cache) =
      ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F)) (.inr m)).run cache := by
  rw [backendGoodRead]
  exact backendRead_denote rep data cost primitive samplingCode.scalar (.op .zero .unit)
    (samplingCode.scalar_denote ()) m cache

theorem backendBadRead_denote (m : M) (cache : List (M × (F × F))) :
    (backendBadRead rep data cost primitive samplingCode).denote (m, cache) =
      ((BLS.LazyAGM.Reduction.privateListOracle (M := M) (R := F × F)) (.inr m)).run cache := by
  rw [backendBadRead]
  exact backendRead_denote rep data cost primitive (pairSampler rep data samplingCode)
    (.pair (.op .zero .unit) (.op .zero .unit)) (pairSampler_denote rep data samplingCode ()) m cache

end Signatures.Runtime.LazyAGM

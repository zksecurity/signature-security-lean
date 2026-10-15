import Signatures.Runtime.BackendSchnorrROMCache
import Signatures.Runtime.BackendSchnorrROMDraws

/-! Executed common-store adapters for Schnorr's ordinary ROM pass. The
configuration, managed/live caches and raw tape travel through every call.
Signing uses private sampling; hashing and the final query use challenge draws.
The final query consults only the live cache. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeComponents

open BackendProgram RawTape

abbrev configTy : Ty CryptoAtom := .pair point₁ point₁
abbrev storeTy : Ty CryptoAtom := .pair cacheStore NativeUniform.stateTy
abbrev withStore (a : Ty CryptoAtom) : Ty CryptoAtom := .pair a storeTy
abbrev managedArgsTy : Ty CryptoAtom := .pair hashKey (.pair scalar (.pair hashCache (.pair hashCache .unit)))
abbrev liveArgsTy : Ty CryptoAtom := .pair hashKey (.pair scalar (.pair hashCache .unit))
abbrev signingArgsTy : Ty CryptoAtom := .pair message (.pair point₁ (.pair point₁ (.pair hashCache .unit)))
abbrev signatureTy : Ty CryptoAtom := .pair point₁ scalar
abbrev keepCacheTy : Ty CryptoAtom := .pair configTy hashCache
abbrev taped (a : Ty CryptoAtom) : Ty CryptoAtom := .pair a NativeUniform.stateTy

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here

def randomInput : Expr CryptoOp [withStore .nat] (.pair (taped .nat) cacheStore) :=
  .pair (.pair (.fst v0) (.snd (.snd v0))) (.fst (.snd v0))

def randomOutput : Expr CryptoOp [.pair (taped .nat) cacheStore] (withStore .nat) :=
  .pair (.fst (.fst v0)) (.pair (.snd v0) (.snd (.fst v0)))

def hashInput : Expr CryptoOp [withStore hashKey] (.pair (taped managedArgsTy) configTy) :=
  let caches := Expr.fst (.snd v0)
  .pair (.pair (.pair (.fst v0) (.pair (.op .zero .unit)
    (.pair (.fst (.snd caches)) (.pair (.snd (.snd caches)) .unit)))) (.snd (.snd v0))) (.fst caches)

def hashOutput : Expr CryptoOp [.pair (taped (.pair scalar (.pair hashCache hashCache))) configTy]
    (withStore scalar) :=
  let result := Expr.fst (.fst v0)
  .pair (.fst result) (.pair (.pair (.snd v0) (.snd result)) (.snd (.fst v0)))

def signingInput : Expr CryptoOp [withStore message] (.pair (taped signingArgsTy) keepCacheTy) :=
  let caches := Expr.fst (.snd v0)
  let config := Expr.fst caches
  .pair (.pair (.pair (.fst v0) (.pair (.fst config) (.pair (.snd config)
    (.pair (.fst (.snd caches)) .unit)))) (.snd (.snd v0)))
    (.pair config (.snd (.snd caches)))

def signingOutput : Expr CryptoOp [.pair (taped (.pair signatureTy hashCache)) keepCacheTy]
    (withStore signatureTy) :=
  let result := Expr.fst (.fst v0)
  let keep := Expr.snd v0
  .pair (.fst result) (.pair (.pair (.fst keep) (.pair (.snd result) (.snd keep))) (.snd (.fst v0)))

def finalInput : Expr CryptoOp [withStore hashKey] (.pair (taped liveArgsTy) keepCacheTy) :=
  let caches := Expr.fst (.snd v0)
  .pair (.pair (.pair (.fst v0) (.pair (.op .zero .unit) (.pair (.snd (.snd caches)) .unit)))
    (.snd (.snd v0))) (.pair (.fst caches) (.fst (.snd caches)))

def finalOutput : Expr CryptoOp [.pair (taped (.pair scalar hashCache)) keepCacheTy] (withStore scalar) :=
  let result := Expr.fst (.fst v0)
  let keep := Expr.snd v0
  .pair (.fst result) (.pair (.pair (.fst keep) (.pair (.snd keep) (.snd result))) (.snd (.fst v0)))

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def localCode {a b : Ty CryptoAtom} (e : Expr CryptoOp [a] b) :
    Q.Realizer (rep.ty a) (rep.ty b) (fun x => e.denote (arithmetic F G₁ G₂ K M cost) (x, ())) :=
  Q.compose (NativeUniform.frame rep data a)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive e)

def wrap {a b x y : Ty CryptoAtom} (keep : Ty CryptoAtom)
    (prepare : Expr CryptoOp [a] (.pair x keep)) (finish : Expr CryptoOp [.pair y keep] b)
    (core : Code Q unifSpec iface (rep.ty x) (rep.ty y)) : Code Q unifSpec iface (rep.ty a) (rep.ty b) :=
  .seq (.atomic (localCode rep data cost primitive prepare))
    (.seq (.first (rep.ty keep) core) (.atomic (localCode rep data cost primitive finish)))

def random (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface)) :
    Code Q unifSpec iface (rep.ty (withStore .nat)) (rep.ty (withStore .nat)) :=
  wrap rep data cost primitive cacheStore randomInput randomOutput (NativeUniform.code rep data cost primitive uniform)

def hash (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar)) :
    Code Q unifSpec iface (rep.ty (withStore hashKey)) (rep.ty (withStore scalar)) :=
  wrap rep data cost primitive configTy hashInput hashOutput
    (NativeCache.managed rep data cost primitive (rep.ty NativeUniform.stateTy)
      (NativeDraw.challenge rep data cost primitive sampler))

def finalHash (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar)) :
    Code Q unifSpec iface (rep.ty (withStore hashKey)) (rep.ty (withStore scalar)) :=
  wrap rep data cost primitive keepCacheTy finalInput finalOutput
    (NativeCache.live rep data cost primitive (rep.ty NativeUniform.stateTy)
      (NativeDraw.challenge rep data cost primitive sampler))

def signing [Q.IsDistributive] (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar)) :
    Code Q unifSpec iface (rep.ty (withStore message)) (rep.ty (withStore signatureTy)) :=
  wrap rep data cost primitive keepCacheTy signingInput signingOutput
    (NativeCache.signing rep data cost primitive (rep.ty NativeUniform.stateTy)
      (NativePrivate.code rep data cost primitive uniform ports sampler))

theorem random_denote (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (n : Nat) (saved : storeTy.Value (cryptoBase F G₁ G₂ K M)) :
    (random rep data cost primitive uniform).denote (n, saved) =
      (fun p => (p.1, saved.1, p.2)) <$>
        (NativeUniform.code rep data cost primitive uniform).denote (n, saved.2) := by
  simp only [random, wrap, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem hash_denote (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (k : M × G₁) (saved : storeTy.Value (cryptoBase F G₁ G₂ K M)) :
    (hash rep data cost primitive sampler).denote (k, saved) =
      (fun p => (p.1.1, (saved.1.1, p.1.2), p.2)) <$>
        (NativeCache.managed rep data cost primitive (rep.ty NativeUniform.stateTy)
          (NativeDraw.challenge rep data cost primitive sampler)).denote
          ((k, 0, saved.1.2.1, saved.1.2.2, ()), saved.2) := by
  simp only [hash, wrap, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem finalHash_denote (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (k : M × G₁) (saved : storeTy.Value (cryptoBase F G₁ G₂ K M)) :
    (finalHash rep data cost primitive sampler).denote (k, saved) =
      (fun p => (p.1.1, (saved.1.1, saved.1.2.1, p.1.2), p.2)) <$>
        (NativeCache.live rep data cost primitive (rep.ty NativeUniform.stateTy)
          (NativeDraw.challenge rep data cost primitive sampler)).denote
          ((k, 0, saved.1.2.2, ()), saved.2) := by
  simp only [finalHash, wrap, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem signing_denote [Q.IsDistributive]
    (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
    (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (msg : M) (saved : storeTy.Value (cryptoBase F G₁ G₂ K M)) :
    (signing rep data cost primitive uniform ports sampler).denote (msg, saved) =
      (fun p => (p.1.1, (saved.1.1, p.1.2, saved.1.2.2), p.2)) <$>
        (NativeCache.signing rep data cost primitive (rep.ty NativeUniform.stateTy)
          (NativePrivate.code rep data cost primitive uniform ports sampler)).denote
          ((msg, saved.1.1.1, saved.1.1.2, saved.1.2.1, ()), saved.2) := by
  simp only [signing, wrap, Code.denote, pure_bind, bind_pure_comp, Functor.map_map]
  rfl

theorem localCode_description {a b : Ty CryptoAtom} (e : Expr CryptoOp [a] b)
    (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    sizes.localSize (localCode rep data cost primitive e) ≤
      Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) e + 4 * allowance := by
  have hf : sizes.localSize (NativeUniform.frame rep data a) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have hc := laws.compose_bound hf
    (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
      (fun op => sizes.localSize (primitive op)) (fun _ => le_rfl) e)
  exact hc.trans (by omega)

theorem wrap_description {a b x y : Ty CryptoAtom} (keep : Ty CryptoAtom)
    (prepare : Expr CryptoOp [a] (.pair x keep)) (finish : Expr CryptoOp [.pair y keep] b)
    (core : Code Q unifSpec iface (rep.ty x) (rep.ty y))
    (sizes : DescriptionSize Q) (allowance : Nat) (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance) :
    (wrap rep data cost primitive keep prepare finish core).descriptionSize sizes ≤
      core.descriptionSize sizes +
        Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) prepare +
        Expression.descriptionBound allowance (fun op => sizes.localSize (primitive op)) finish + 8 * allowance + 5 := by
  have hp := localCode_description rep data cost primitive prepare sizes allowance laws dataLaws
  have hf := localCode_description rep data cost primitive finish sizes allowance laws dataLaws
  dsimp only [wrap, Code.descriptionSize]
  omega

end Signatures.Runtime.Schnorr.ListROM.NativeComponents

import Signatures.Runtime.SchnorrCache

/-! Closed-machine adapters for Schnorr's two-cache simulation. The final-query adapter
bypasses the managed cache, even when signing has programmed its target. -/

open OracleComp

namespace Signatures.Runtime.Schnorr

abbrev cacheStore : Ty CryptoAtom :=
  .pair (.pair point₁ point₁) (.pair hashCache hashCache)

private def v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private def v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)

def hashProgram {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar) :
    Program CryptoOp Cmd [hashKey] scalar :=
  .bind (.query read .unit)
    (.bind (.call (managedGet draw)
      (.cons v1 (.cons (.op .zero .unit)
        (.cons (.fst (.snd v0)) (.cons (.snd (.snd v0)) .nil)))))
      (.bind (.query write (.pair (.fst v1) (.snd v0)))
        (.ret (.fst v1))))

def finalHashProgram {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar) :
    Program CryptoOp Cmd [hashKey] scalar :=
  .bind (.query read .unit)
    (.bind (.call (cacheGetExpr hashEq draw)
      (.cons v1 (.cons (.op .zero .unit) (.cons (.snd (.snd v0)) .nil))))
      (.bind (.query write (.pair (.fst v1) (.pair (.fst (.snd v1)) (.snd v0))))
        (.ret (.fst v1))))

def signProgram {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar) :
    Program CryptoOp Cmd [message] (.pair point₁ scalar) :=
  .bind (.query read .unit)
    (.bind (.call (signCached draw)
      (.cons v1 (.cons (.fst (.fst v0))
        (.cons (.snd (.fst v0)) (.cons (.fst (.snd v0)) .nil)))))
      (.bind (.query write (.pair (.fst v1) (.pair (.snd v0) (.snd (.snd v1)))))
        (.ret (.fst v1))))

variable {F G₁ G₂ K M : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

omit [SampleableType F] in
theorem hashProgram_denote {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : SemanticsM (cryptoBase F G₁ G₂ K M) Cmd m)
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar)
    (k : M × G₁) :
    (hashProgram read write draw).denote (arithmetic F G₁ G₂ K M cost) H (k, ()) = (do
      let s ← H read ()
      let r ← (managedGet draw).denote (arithmetic F G₁ G₂ K M cost) H
        (k, 0, s.2.1, s.2.2, ())
      let _ ← H write (s.1, r.2)
      pure r.1) := by
  simp [hashProgram, Program.denote, Args.denote, Expr.denote, v0, v1, Var.get, arithmetic]

omit [SampleableType F] in
theorem finalHashProgram_denote {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : SemanticsM (cryptoBase F G₁ G₂ K M) Cmd m)
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar)
    (k : M × G₁) :
    (finalHashProgram read write draw).denote (arithmetic F G₁ G₂ K M cost) H (k, ()) = (do
      let s ← H read ()
      let r ← (cacheGetExpr hashEq draw).denote (arithmetic F G₁ G₂ K M cost) H
        (k, 0, s.2.2, ())
      let _ ← H write (s.1, s.2.1, r.2)
      pure r.1) := by
  simp [finalHashProgram, Program.denote, Args.denote, Expr.denote, v0, v1, Var.get, arithmetic]

omit [SampleableType F] in
theorem signProgram_denote {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : SemanticsM (cryptoBase F G₁ G₂ K M) Cmd m)
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar)
    (msg : M) :
    (signProgram read write draw).denote (arithmetic F G₁ G₂ K M cost) H (msg, ()) = (do
      let s ← H read ()
      let r ← (signCached draw).denote (arithmetic F G₁ G₂ K M cost) H
        (msg, s.1.1, s.1.2, s.2.1, ())
      let _ ← H write (s.1, r.2, s.2.2)
      pure r.1) := by
  simp [signProgram, Program.denote, Args.denote, Expr.denote, v0, v1, Var.get]

omit [SampleableType F] in
theorem hashProgram_run {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd m)
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar)
    (k : M × G₁) :
    (hashProgram read write draw).run (arithmetic F G₁ G₂ K M cost) H (k, ()) = (do
      let s ← H read ()
      let r ← (managedGet draw).run (arithmetic F G₁ G₂ K M cost) H
        (k, 0, s.value.2.1, s.value.2.2, ())
      let w ← H write (s.value.1, r.value.2)
      pure ⟨r.value.1, s.steps + r.steps + w.steps + cost.field + 33⟩) := by
  unfold hashProgram
  generalize managedGet draw = body
  simp only [Program.run, Args.run, Expr.run, v0, v1, Var.get, Var.depth,
    pure_bind, bind_assoc]
  congr 1
  funext s
  dsimp [arithmetic, CryptoOp.price]
  congr 1
  funext r
  congr 1
  funext w
  congr 1
  apply congrArg (Run.mk _)
  omega

omit [SampleableType F] in
theorem finalHashProgram_run {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd m)
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar)
    (k : M × G₁) :
    (finalHashProgram read write draw).run (arithmetic F G₁ G₂ K M cost) H (k, ()) = (do
      let s ← H read ()
      let r ← (cacheGetExpr hashEq draw).run (arithmetic F G₁ G₂ K M cost) H
        (k, 0, s.value.2.2, ())
      let w ← H write (s.value.1, s.value.2.1, r.value.2)
      pure ⟨r.value.1, s.steps + r.steps + w.steps + cost.field + 34⟩) := by
  unfold finalHashProgram
  generalize cacheGetExpr hashEq draw = body
  simp only [Program.run, Args.run, Expr.run, v0, v1, Var.get, Var.depth,
    pure_bind, bind_assoc]
  congr 1
  funext s
  dsimp [arithmetic, CryptoOp.price]
  congr 1
  funext r
  congr 1
  funext w
  congr 1
  apply congrArg (Run.mk _)
  omega

omit [SampleableType F] in
theorem signProgram_run {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (cost : PrimitiveCosts) (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd m)
    (read : Cmd .unit cacheStore) (write : Cmd cacheStore .unit) (draw : Cmd .unit scalar)
    (msg : M) :
    (signProgram read write draw).run (arithmetic F G₁ G₂ K M cost) H (msg, ()) = (do
      let s ← H read ()
      let r ← (signCached draw).run (arithmetic F G₁ G₂ K M cost) H
        (msg, s.value.1.1, s.value.1.2, s.value.2.1, ())
      let w ← H write (s.value.1, r.value.2, s.value.2.2)
      pure ⟨r.value.1, s.steps + r.steps + w.steps + 39⟩) := by
  unfold signProgram
  generalize signCached draw = body
  simp only [Program.run, Args.run, Expr.run, v0, v1, Var.get, Var.depth,
    pure_bind, bind_assoc]
  congr 1
  funext s
  congr 1
  funext r
  congr 1
  funext w
  congr 1
  apply congrArg (Run.mk _)
  omega

end Signatures.Runtime.Schnorr

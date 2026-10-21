import Signatures.Runtime.Caliper.SchnorrROMNonzeroSigningLayout

/-! Executed projections out of the signing frame `(R, a, (c, z), g, pk, msg,
managed)` and the final route into the cache-programming frame. Each is an
assembly copy whose time and stored code are charged by `ByteRoute`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning
open Caliper BoundedSource SchnorrROMTape ByteRoute
variable {w : Nat} {M F G : Type} (config : Signing.Enumerated.Configuration w M F G)

def gg (u : G × F × Signing.Input M F G) : G × G := (u.2.2.2.1, u.2.2.2.1)
def ag (u : G × F × Signing.Input M F G) : F × G := (u.2.1, u.2.2.2.1)
def za (u : G × F × Signing.Input M F G) : F × F := (u.2.2.1.2, u.2.1)
def rz (u : G × F × Signing.Input M F G) : G × F := (u.1, u.2.2.1.2)

/-- `(g, g)`: the arguments of the executed zero point `g - g`. -/
def projGG : Implementation .unit (frame config) config.handler.core.arithmetic.points gg :=
  route config _ _ gg (fun _ valid => ⟨valid.2.2.1.2.1, valid.2.2.1.2.1⟩)
    [.slice (pw config + sw config + sw config + sw config) (pw config),
     .slice (pw config + sw config + sw config + sw config) (pw config)]
    (by simp only [Valid]; rw [frame_words]; exact ⟨by omega, by omega, trivial⟩)
    (by simp only [words]; rfl)
    (by
      intro v
      let C := config.handler.core.point.representation.encoding.encode (commitmentOf v)
      let D := config.handler.core.scalar.representation.encoding.encode (nonceOf v)
      let E := config.handler.core.scalar.representation.encoding.encode (challengeOf v)
      let Z := config.handler.core.scalar.representation.encoding.encode (responseOf v)
      let Gg := config.handler.core.point.representation.encoding.encode (generatorOf v)
      let K := config.handler.core.point.representation.encoding.encode (publicKeyOf v)
      let Mm := config.handler.core.message.representation.encoding.encode (messageOf v)
      let T := config.handler.core.table.representation.encoding.encode (tableOf v)
      have hC : C.length = pw config := Encoding.encode_length _ _
      have hD : D.length = sw config := Encoding.encode_length _ _
      have hE : E.length = sw config := Encoding.encode_length _ _
      have hZ : Z.length = sw config := Encoding.encode_length _ _
      have hG : Gg.length = pw config := Encoding.encode_length _ _
      have piece := slice_block (C ++ D ++ E ++ Z) Gg (K ++ (Mm ++ T))
      simp only [List.length_append, hC, hD, hE, hZ, hG, List.append_assoc, ← Nat.add_assoc] at piece
      change bytes (C ++ (D ++ ((E ++ Z) ++ (Gg ++ (K ++ (Mm ++ T)))))) _ = Gg ++ Gg
      simp only [bytes, List.append_nil, List.append_assoc]
      rw [piece])

/-- `(a, g)`: the arguments of the repair commitment `a • g`. -/
def projAG : Implementation .unit (frame config) config.handler.core.arithmetic.scaleArgs ag :=
  route config _ _ ag (fun _ valid => ⟨valid.2.1, valid.2.2.1.2.1⟩)
    [.slice (pw config) (sw config),
     .slice (pw config + sw config + sw config + sw config) (pw config)]
    (by simp only [Valid]; rw [frame_words]; exact ⟨by omega, by omega, trivial⟩)
    (by simp only [words]; rfl)
    (by
      intro v
      let C := config.handler.core.point.representation.encoding.encode (commitmentOf v)
      let D := config.handler.core.scalar.representation.encoding.encode (nonceOf v)
      let E := config.handler.core.scalar.representation.encoding.encode (challengeOf v)
      let Z := config.handler.core.scalar.representation.encoding.encode (responseOf v)
      let Gg := config.handler.core.point.representation.encoding.encode (generatorOf v)
      let K := config.handler.core.point.representation.encoding.encode (publicKeyOf v)
      let Mm := config.handler.core.message.representation.encoding.encode (messageOf v)
      let T := config.handler.core.table.representation.encoding.encode (tableOf v)
      have hC : C.length = pw config := Encoding.encode_length _ _
      have hD : D.length = sw config := Encoding.encode_length _ _
      have hE : E.length = sw config := Encoding.encode_length _ _
      have hZ : Z.length = sw config := Encoding.encode_length _ _
      have hG : Gg.length = pw config := Encoding.encode_length _ _
      have nonce := slice_block C D (E ++ (Z ++ (Gg ++ (K ++ (Mm ++ T)))))
      have generator := slice_block (C ++ D ++ E ++ Z) Gg (K ++ (Mm ++ T))
      simp only [List.length_append, hC, hD, hE, hZ, hG, List.append_assoc, ← Nat.add_assoc] at nonce generator
      change bytes (C ++ (D ++ ((E ++ Z) ++ (Gg ++ (K ++ (Mm ++ T)))))) _ = D ++ Gg
      simp only [bytes, List.append_nil, List.append_assoc]
      rw [nonce, generator])

/-- `(z, a)`: the arguments of the repaired response `z + a`. -/
def projZA : Implementation .unit (frame config) config.handler.core.arithmetic.scalars za :=
  route config _ _ za (fun _ valid => ⟨valid.2.2.1.1.2, valid.2.1⟩)
    [.slice (pw config + sw config + sw config) (sw config), .slice (pw config) (sw config)]
    (by simp only [Valid]; rw [frame_words]; exact ⟨by omega, by omega, trivial⟩)
    (by simp only [words]; rfl)
    (by
      intro v
      let C := config.handler.core.point.representation.encoding.encode (commitmentOf v)
      let D := config.handler.core.scalar.representation.encoding.encode (nonceOf v)
      let E := config.handler.core.scalar.representation.encoding.encode (challengeOf v)
      let Z := config.handler.core.scalar.representation.encoding.encode (responseOf v)
      let Gg := config.handler.core.point.representation.encoding.encode (generatorOf v)
      let K := config.handler.core.point.representation.encoding.encode (publicKeyOf v)
      let Mm := config.handler.core.message.representation.encoding.encode (messageOf v)
      let T := config.handler.core.table.representation.encoding.encode (tableOf v)
      have hC : C.length = pw config := Encoding.encode_length _ _
      have hD : D.length = sw config := Encoding.encode_length _ _
      have hE : E.length = sw config := Encoding.encode_length _ _
      have hZ : Z.length = sw config := Encoding.encode_length _ _
      have nonce := slice_block C D (E ++ (Z ++ (Gg ++ (K ++ (Mm ++ T)))))
      have response := slice_block (C ++ D ++ E) Z (Gg ++ (K ++ (Mm ++ T)))
      simp only [List.length_append, hC, hD, hE, hZ, List.append_assoc, ← Nat.add_assoc] at nonce response
      change bytes (C ++ (D ++ ((E ++ Z) ++ (Gg ++ (K ++ (Mm ++ T)))))) _ = Z ++ D
      simp only [bytes, List.append_nil, List.append_assoc]
      rw [nonce, response])

/-- `(R, z)`: the unrepaired signature. -/
def projRZ : Implementation .unit (frame config) config.handler.core.reply rz :=
  route config _ _ rz (fun _ valid => ⟨valid.1, valid.2.2.1.1.2⟩)
    [.slice 0 (pw config), .slice (pw config + sw config + sw config) (sw config)]
    (by simp only [Valid]; rw [frame_words]; exact ⟨by omega, by omega, trivial⟩)
    (by simp only [words]; rfl)
    (by
      intro v
      let C := config.handler.core.point.representation.encoding.encode (commitmentOf v)
      let D := config.handler.core.scalar.representation.encoding.encode (nonceOf v)
      let E := config.handler.core.scalar.representation.encoding.encode (challengeOf v)
      let Z := config.handler.core.scalar.representation.encoding.encode (responseOf v)
      let Gg := config.handler.core.point.representation.encoding.encode (generatorOf v)
      let K := config.handler.core.point.representation.encoding.encode (publicKeyOf v)
      let Mm := config.handler.core.message.representation.encoding.encode (messageOf v)
      let T := config.handler.core.table.representation.encoding.encode (tableOf v)
      have hC : C.length = pw config := Encoding.encode_length _ _
      have hD : D.length = sw config := Encoding.encode_length _ _
      have hE : E.length = sw config := Encoding.encode_length _ _
      have hZ : Z.length = sw config := Encoding.encode_length _ _
      have commitment := slice_block [] C (D ++ (E ++ (Z ++ (Gg ++ (K ++ (Mm ++ T))))))
      have response := slice_block (C ++ D ++ E) Z (Gg ++ (K ++ (Mm ++ T)))
      simp only [List.length_nil, List.nil_append, List.length_append, hC, hD, hE, hZ, List.append_assoc,
        ← Nat.add_assoc] at commitment response
      change bytes (C ++ (D ++ ((E ++ Z) ++ (Gg ++ (K ++ (Mm ++ T)))))) _ = C ++ Z
      simp only [bytes, List.append_nil, List.append_assoc]
      rw [commitment, response])

section Assemble
variable [DecidableEq M] [DecidableEq G]

/-- Route the repaired reply and the frame into the cache-programming frame:
the key `(msg, R')`, the challenge `c`, the managed table, and the retained
signature `(R', z')` and configuration `(g, pk)`. -/
def assemble (r : (G × F) × G × F × Signing.Input M F G) : CacheLayout.Input (M × G) F × Signing.Saved F G :=
  (((r.2.2.2.2.2.2.1, r.1.1), r.2.2.2.1.1, r.2.2.2.2.2.2.2, ()), r.1, r.2.2.2.2.1, r.2.2.2.2.2.1)

def assembleParts : List (Part w) :=
  [.slice (pw config + sw config + pw config + sw config + sw config + sw config + pw config + pw config) (mw config),
   .slice 0 (pw config),
   .slice (pw config + sw config + pw config + sw config) (sw config),
   .slice (pw config + sw config + pw config + sw config + sw config + sw config + pw config + pw config + mw config) (tw config),
   .slice 0 (pw config),
   .slice (pw config) (sw config),
   .slice (pw config + sw config + pw config + sw config + sw config + sw config) (pw config + pw config)]

def routeWork : Implementation .unit (framed config) config.handler.core.work assemble :=
  route config _ _ assemble
    (fun _ valid => ⟨⟨⟨⟨valid.2.2.2.1.2.2.2.1, valid.1.1⟩, valid.2.2.2.1.1.1, valid.2.2.2.1.2.2.2.2, trivial⟩,
      fun _ => valid.2.2.2.2⟩, ⟨valid.1.1, valid.1.2⟩, valid.2.2.2.1.2.1, valid.2.2.2.1.2.2.1⟩)
    (assembleParts config)
    (by
      simp only [assembleParts, Valid]; rw [framed_words]
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩)
    (by
      simp only [assembleParts, words]; rw [work_words]; omega)
    (by
      intro r
      let u : (frame config).Value := ⟨r.val.2, r.property.2⟩
      let A := config.handler.core.point.representation.encoding.encode ⟨r.val.1.1, r.property.1.1⟩
      let B := config.handler.core.scalar.representation.encoding.encode ⟨r.val.1.2, r.property.1.2⟩
      let C := config.handler.core.point.representation.encoding.encode (commitmentOf u)
      let D := config.handler.core.scalar.representation.encoding.encode (nonceOf u)
      let E := config.handler.core.scalar.representation.encoding.encode (challengeOf u)
      let Z := config.handler.core.scalar.representation.encoding.encode (responseOf u)
      let Gg := config.handler.core.point.representation.encoding.encode (generatorOf u)
      let K := config.handler.core.point.representation.encoding.encode (publicKeyOf u)
      let Mm := config.handler.core.message.representation.encoding.encode (messageOf u)
      let T := config.handler.core.table.representation.encoding.encode (tableOf u)
      have hA : A.length = pw config := Encoding.encode_length _ _
      have hB : B.length = sw config := Encoding.encode_length _ _
      have hC : C.length = pw config := Encoding.encode_length _ _
      have hD : D.length = sw config := Encoding.encode_length _ _
      have hE : E.length = sw config := Encoding.encode_length _ _
      have hZ : Z.length = sw config := Encoding.encode_length _ _
      have hG : Gg.length = pw config := Encoding.encode_length _ _
      have hK : K.length = pw config := Encoding.encode_length _ _
      have hM : Mm.length = mw config := Encoding.encode_length _ _
      have hT : T.length = tw config := Encoding.encode_length _ _
      have message := slice_block (A ++ B ++ C ++ D ++ E ++ Z ++ Gg ++ K) Mm T
      have repaired := slice_block [] A (B ++ (C ++ (D ++ (E ++ (Z ++ (Gg ++ (K ++ (Mm ++ T))))))))
      have challenge := slice_block (A ++ B ++ C ++ D) E (Z ++ (Gg ++ (K ++ (Mm ++ T))))
      have table := slice_block (A ++ B ++ C ++ D ++ E ++ Z ++ Gg ++ K ++ Mm) T []
      have response := slice_block A B (C ++ (D ++ (E ++ (Z ++ (Gg ++ (K ++ (Mm ++ T)))))))
      have points := slice_block (A ++ B ++ C ++ D ++ E ++ Z) (Gg ++ K) (Mm ++ T)
      simp only [List.length_nil, List.nil_append, List.append_nil, List.length_append, hA, hB, hC, hD, hE, hZ, hG, hK, hM, hT,
        List.append_assoc, ← Nat.add_assoc] at message repaired challenge table response points
      change bytes ((A ++ B) ++ (C ++ (D ++ ((E ++ Z) ++ (Gg ++ (K ++ (Mm ++ T))))))) (assembleParts config) =
        ((Mm ++ A) ++ (E ++ (T ++ []))) ++ ((A ++ B) ++ (Gg ++ K))
      simp only [assembleParts, bytes, List.append_nil, List.append_assoc]
      rw [message, repaired, challenge, table, response]
      rw [points])

end Assemble
end Signatures.Runtime.CaliperBackend.SchnorrROM.NonzeroSigning

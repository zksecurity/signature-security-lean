import Proofs.Runtime.BackendLazyAGMSimulation
import Proofs.Runtime.BackendDataSize

/-! Encoded reachable-store bounds for native lazy AGM execution. The private
cache and the explicit reply logs are counted separately: a repeated signature
can grow the transcript even on a cache hit. Bounds use only stored entries and
encountered-message widths, never an enumeration of the message type.
-/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes lists

theorem store_encoded_size {value config : Ty CryptoAtom}
    (cfg : config.Value (cryptoBase F G₁ G₂ M M))
    (state : State M (value.Value (cryptoBase F G₁ G₂ M M)) G₁)
    (configWidth messageWidth valueWidth groupWidth cacheCap replyCap : Nat)
    (hc : Q.size (rep.ty config) cfg ≤ configWidth)
    (hm : state.Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth))
    (hv : ∀ r, Q.size (rep.ty value) r ≤ valueWidth)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : state.1.length ≤ cacheCap)
    (ht : state.2.1.length + state.2.2.length ≤ replyCap) :
    Q.size (rep.ty (storeTy value config)) (cfg, state) ≤
      configWidth + cacheCap * (messageWidth + valueWidth + 2 * header) +
        replyCap * (messageWidth + groupWidth + 2 * header) + 6 * header := by
  have hcache : Q.size (rep.ty (cacheTy value)) state.1 ≤
      cacheCap * (messageWidth + valueWidth + 2 * header) + header := by
    refine (lists.size_le_cap (rep.ty (.pair message value)) state.1
      (messageWidth + valueWidth + header) cacheCap (fun p hp => ?_) hk).trans ?_
    · have h := sizes.prod_le (rep.ty message) (rep.ty value) p
      have h1 := hm.1 p hp
      have h2 := hv p.2
      dsimp only [LanguageRepresentation.ty] at *
      omega
    · nlinarith
  have hlog (xs : List (M × G₁)) (hxs : ∀ p ∈ xs, Q.size (rep.ty message) p.1 ≤ messageWidth) :
      Q.size (rep.ty (.list (.pair message point₁))) xs ≤
        xs.length * (messageWidth + groupWidth + 2 * header) + header := by
    refine (lists.size_le_length (rep.ty (.pair message point₁)) xs
      (messageWidth + groupWidth + header) (fun p hp => ?_)).trans ?_
    · have h := sizes.prod_le (rep.ty message) (rep.ty point₁) p
      have h1 := hxs p hp
      have h2 := hg p.2
      dsimp only [LanguageRepresentation.ty] at *
      omega
    · nlinarith
  have hhash := hlog state.2.1 hm.2.1
  have hsign := hlog state.2.2 hm.2.2
  have htr := sizes.prod_le (rep.ty (.list (.pair message point₁)))
    (rep.ty (.list (.pair message point₁))) state.2
  have hstate := sizes.prod_le (rep.ty (cacheTy value)) (rep.ty transcriptTy) state
  have hstore := sizes.prod_le (rep.ty config) (rep.ty (.pair (cacheTy value) transcriptTy)) (cfg, state)
  have hcount := Nat.mul_le_mul_right (messageWidth + groupWidth + 2 * header) ht
  dsimp only [storeTy, transcriptTy, LanguageRepresentation.ty] at *
  nlinarith

theorem goodStore_encoded_size (g X : G₁) (state : State M F G₁)
    (messageWidth fieldWidth groupWidth cacheCap replyCap : Nat)
    (hm : state.Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth))
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ fieldWidth)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : state.1.length ≤ cacheCap) (ht : state.2.1.length + state.2.2.length ≤ replyCap) :
    Q.size (rep.ty (storeTy scalar goodConfigTy)) ((g, X), state) ≤
      2 * groupWidth + cacheCap * (messageWidth + fieldWidth + 2 * header) +
        replyCap * (messageWidth + groupWidth + 2 * header) + 7 * header := by
  have hcfg : Q.size (rep.ty goodConfigTy) (g, X) ≤ 2 * groupWidth + header := by
    have h := sizes.prod_le (rep.ty point₁) (rep.ty point₁) (g, X)
    have hg1 := hg g
    have hg2 := hg X
    change Q.size (rep.ty goodConfigTy) (g, X) ≤ _ at h
    dsimp at h
    omega
  have h := store_encoded_size rep sizes lists (value := scalar) (config := goodConfigTy)
    (g, X) state (2 * groupWidth + header)
    messageWidth fieldWidth groupWidth cacheCap replyCap hcfg hm hf hg hk ht
  omega

theorem badStore_encoded_size (g X : G₁) (kappa : F) (state : State M (F × F) G₁)
    (messageWidth fieldWidth groupWidth cacheCap replyCap : Nat)
    (hm : state.Messages (fun m => Q.size (rep.ty message) m ≤ messageWidth))
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ fieldWidth)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : state.1.length ≤ cacheCap) (ht : state.2.1.length + state.2.2.length ≤ replyCap) :
    Q.size (rep.ty (storeTy (.pair scalar scalar) badConfigTy)) ((kappa, g, X), state) ≤
      fieldWidth + 2 * groupWidth + cacheCap * (messageWidth + 2 * fieldWidth + 3 * header) +
        replyCap * (messageWidth + groupWidth + 2 * header) + 8 * header := by
  have hpair (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 2 * fieldWidth + header := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at h
    omega
  have hcfg : Q.size (rep.ty badConfigTy) (kappa, g, X) ≤ fieldWidth + 2 * groupWidth + 2 * header := by
    have hp : Q.size (rep.ty goodConfigTy) (g, X) ≤
        Q.size (rep.ty point₁) g + Q.size (rep.ty point₁) X + header :=
      sizes.prod_le (rep.ty point₁) (rep.ty point₁) (g, X)
    have hc : Q.size (rep.ty badConfigTy) (kappa, g, X) ≤
        Q.size (rep.ty scalar) kappa + Q.size (rep.ty goodConfigTy) (g, X) + header :=
      sizes.prod_le (rep.ty scalar) (rep.ty goodConfigTy) (kappa, g, X)
    have h1 := hg g
    have h2 := hg X
    have h3 := hf kappa
    omega
  have h := store_encoded_size rep sizes lists (value := .pair scalar scalar) (config := badConfigTy)
    (kappa, g, X) state
    (fieldWidth + 2 * groupWidth + 2 * header) messageWidth (2 * fieldWidth + header)
    groupWidth cacheCap replyCap hcfg hm hpair hg hk ht
  nlinarith

end Signatures.Runtime.LazyAGM

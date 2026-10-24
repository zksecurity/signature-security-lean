import Proofs.Runtime.WeightedExecution
import Proofs.Runtime.BackendDataSize

/-! Encoded reachable-store bounds for native weighted AGM execution. The private
cache and the explicit reply logs are counted separately: a repeated signature
can grow the transcript even on a cache hit. Bounds use only stored entries and
encountered-message widths, never an enumeration of the message type.
-/

open PFunctor

namespace Signatures.Runtime.WeightedAGM

open BackendProgram Reply

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

variable {indexTy messageTy : Ty CryptoAtom}

/-- Only encountered indices and messages have bounded encodings. -/
def State.Entries {ι M R G : Type} (key : ι → Prop) (message : M → Prop)
    (state : State ι M R G) : Prop :=
  (∀ p ∈ state.1, key p.1) ∧ (∀ p ∈ state.2.1, key p.1) ∧ ∀ p ∈ state.2.2, message p.1

include sizes lists

theorem store_encoded_size {value config : Ty CryptoAtom}
    (cfg : config.Value (cryptoBase F G₁ G₂ K M))
    (state : State (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) (value.Value (cryptoBase F G₁ G₂ K M)) G₁)
    (configWidth messageWidth valueWidth groupWidth cacheCap replyCap : Nat)
    (hc : Q.size (rep.ty config) cfg ≤ configWidth)
    (hm : State.Entries (fun k => Q.size (rep.ty indexTy) k ≤ messageWidth)
      (fun m => Q.size (rep.ty messageTy) m ≤ messageWidth) state)
    (hv : ∀ r, Q.size (rep.ty value) r ≤ valueWidth)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : state.1.length ≤ cacheCap)
    (ht : state.2.1.length + state.2.2.length ≤ replyCap) :
    Q.size (rep.ty (storeTy indexTy messageTy value config)) (cfg, state) ≤
      configWidth + cacheCap * (messageWidth + valueWidth + 2 * header) +
        replyCap * (messageWidth + groupWidth + 2 * header) + 6 * header := by
  have hcache : Q.size (rep.ty (cacheTy indexTy value)) state.1 ≤
      cacheCap * (messageWidth + valueWidth + 2 * header) + header := by
    refine (lists.size_le_cap (rep.ty (.pair indexTy value)) state.1
      (messageWidth + valueWidth + header) cacheCap (fun p hp => ?_) hk).trans ?_
    · have h := sizes.prod_le (rep.ty indexTy) (rep.ty value) p
      have h1 := hm.1 p hp
      have h2 := hv p.2
      dsimp only [LanguageRepresentation.ty] at *
      omega
    · nlinarith
  have hlog (ty : Ty CryptoAtom) (xs : List (ty.Value (cryptoBase F G₁ G₂ K M) × G₁)) (hxs : ∀ p ∈ xs, Q.size (rep.ty ty) p.1 ≤ messageWidth) :
      Q.size (rep.ty (.list (.pair ty point₁))) xs ≤
        xs.length * (messageWidth + groupWidth + 2 * header) + header := by
    refine (lists.size_le_length (rep.ty (.pair ty point₁)) xs
      (messageWidth + groupWidth + header) (fun p hp => ?_)).trans ?_
    · have h := sizes.prod_le (rep.ty ty) (rep.ty point₁) p
      have h1 := hxs p hp
      have h2 := hg p.2
      dsimp only [LanguageRepresentation.ty] at *
      omega
    · nlinarith
  have hhash := hlog indexTy state.2.1 hm.2.1
  have hsign := hlog messageTy state.2.2 hm.2.2
  have htr := sizes.prod_le (rep.ty (.list (.pair indexTy point₁)))
    (rep.ty (.list (.pair messageTy point₁))) state.2
  have hstate := sizes.prod_le (rep.ty (cacheTy indexTy value)) (rep.ty (transcriptTy indexTy messageTy)) state
  have hstore := sizes.prod_le (rep.ty config) (rep.ty (.pair (cacheTy indexTy value) (transcriptTy indexTy messageTy))) (cfg, state)
  have hcount := Nat.mul_le_mul_right (messageWidth + groupWidth + 2 * header) ht
  dsimp only [storeTy, transcriptTy, LanguageRepresentation.ty] at *
  nlinarith

theorem goodStore_encoded_size (g X : G₁) (state : State (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) F G₁)
    (messageWidth fieldWidth groupWidth cacheCap replyCap : Nat)
    (hm : State.Entries (fun k => Q.size (rep.ty indexTy) k ≤ messageWidth)
      (fun m => Q.size (rep.ty messageTy) m ≤ messageWidth) state)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ fieldWidth)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : state.1.length ≤ cacheCap) (ht : state.2.1.length + state.2.2.length ≤ replyCap) :
    Q.size (rep.ty (storeTy indexTy messageTy scalar LazyAGM.goodConfigTy)) ((g, X), state) ≤
      2 * groupWidth + cacheCap * (messageWidth + fieldWidth + 2 * header) +
        replyCap * (messageWidth + groupWidth + 2 * header) + 7 * header := by
  have hcfg : Q.size (rep.ty LazyAGM.goodConfigTy) (g, X) ≤ 2 * groupWidth + header := by
    have h := sizes.prod_le (rep.ty point₁) (rep.ty point₁) (g, X)
    have hg1 := hg g
    have hg2 := hg X
    change Q.size (rep.ty LazyAGM.goodConfigTy) (g, X) ≤ _ at h
    dsimp at h
    omega
  have h := store_encoded_size rep sizes lists (value := scalar) (config := LazyAGM.goodConfigTy)
    (g, X) state (2 * groupWidth + header)
    messageWidth fieldWidth groupWidth cacheCap replyCap hcfg hm hf hg hk ht
  omega

theorem badStore_encoded_size (g X : G₁) (kappa : F) (state : State (indexTy.Value (cryptoBase F G₁ G₂ K M)) (messageTy.Value (cryptoBase F G₁ G₂ K M)) (F × F) G₁)
    (messageWidth fieldWidth groupWidth cacheCap replyCap : Nat)
    (hm : State.Entries (fun k => Q.size (rep.ty indexTy) k ≤ messageWidth)
      (fun m => Q.size (rep.ty messageTy) m ≤ messageWidth) state)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ fieldWidth)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ groupWidth)
    (hk : state.1.length ≤ cacheCap) (ht : state.2.1.length + state.2.2.length ≤ replyCap) :
    Q.size (rep.ty (storeTy indexTy messageTy (.pair scalar scalar) LazyAGM.badConfigTy)) ((kappa, g, X), state) ≤
      fieldWidth + 2 * groupWidth + cacheCap * (messageWidth + 2 * fieldWidth + 3 * header) +
        replyCap * (messageWidth + groupWidth + 2 * header) + 8 * header := by
  have hpair (p : F × F) : Q.size (rep.ty (.pair scalar scalar)) p ≤ 2 * fieldWidth + header := by
    have h := sizes.prod_le (rep.ty scalar) (rep.ty scalar) p
    have h1 := hf p.1
    have h2 := hf p.2
    change Q.size (rep.ty (.pair scalar scalar)) p ≤ _ at h
    omega
  have hcfg : Q.size (rep.ty LazyAGM.badConfigTy) (kappa, g, X) ≤ fieldWidth + 2 * groupWidth + 2 * header := by
    have hp : Q.size (rep.ty LazyAGM.goodConfigTy) (g, X) ≤
        Q.size (rep.ty point₁) g + Q.size (rep.ty point₁) X + header :=
      sizes.prod_le (rep.ty point₁) (rep.ty point₁) (g, X)
    have hc : Q.size (rep.ty LazyAGM.badConfigTy) (kappa, g, X) ≤
        Q.size (rep.ty scalar) kappa + Q.size (rep.ty LazyAGM.goodConfigTy) (g, X) + header :=
      sizes.prod_le (rep.ty scalar) (rep.ty LazyAGM.goodConfigTy) (kappa, g, X)
    have h1 := hg g
    have h2 := hg X
    have h3 := hf kappa
    omega
  have h := store_encoded_size rep sizes lists (value := .pair scalar scalar) (config := LazyAGM.badConfigTy)
    (kappa, g, X) state
    (fieldWidth + 2 * groupWidth + 2 * header) messageWidth (2 * fieldWidth + header)
    groupWidth cacheCap replyCap hcfg hm hpair hg hk ht
  nlinarith

end Signatures.Runtime.WeightedAGM

import Signatures.Runtime.BackendSchnorrROMHandlerComponents
import Signatures.Runtime.BackendSchnorrROMManagedBudget
import Signatures.Runtime.BackendSchnorrROMSigningBudget

/-! Shared-store encoding invariants. Cache entries keep one fixed allowance
across adaptive calls. Both replay lists are charged at their reserved capacities. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeComponents

open BackendProgram RawTape

def frameWidth (width managedCap liveCap : Nat) : Nat :=
  (32 * (managedCap + liveCap) + 128) * width

universe v w

variable {C : StepClass.{0, v}} [C.HasProd]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M : Type}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))

def ConfigBound (width : Nat) (config : G₁ × G₁) : Prop :=
  Q.size (rep.ty point₁) config.1 ≤ width ∧ Q.size (rep.ty point₁) config.2 ≤ width

def CacheBound (width cap : Nat) (cache : List ((M × G₁) × F)) : Prop :=
  CacheCompiler.Entries (Q := Q) (key := hashKey) (val := scalar) rep (3 * width) cache ∧ cache.length ≤ cap

structure CachesBound (width managedCap liveCap : Nat)
    (caches : cacheStore.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  config : ConfigBound (Q := Q) rep width caches.1
  managed : CacheBound (Q := Q) rep width managedCap caches.2.1
  live : CacheBound (Q := Q) rep width liveCap caches.2.2

structure StoreBound (width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (saved : storeTy.Value (cryptoBase F G₁ G₂ K M)) : Prop where
  caches : CachesBound (Q := Q) rep width managedCap liveCap saved.1
  tape : NativeUniform.StateBound (Q := Q) rep tapeWidth savedCap remainingCap saved.2

def InputBound (a : Ty CryptoAtom) (valueWidth width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (input : (withStore a).Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  Q.size (rep.ty a) input.1 ≤ valueWidth ∧
    StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap input.2

def KeepBound (width cap : Nat) (saved : keepCacheTy.Value (cryptoBase F G₁ G₂ K M)) : Prop :=
  ConfigBound (Q := Q) rep width saved.1 ∧ CacheBound (Q := Q) rep width cap saved.2

theorem store_mono (width tapeWidth mc lc sc rc mc' lc' sc' rc' : Nat)
    (hm : mc ≤ mc') (hl : lc ≤ lc') (hs : sc ≤ sc') (hr : rc ≤ rc')
    (saved : storeTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : StoreBound (Q := Q) rep width tapeWidth mc lc sc rc saved) :
    StoreBound (Q := Q) rep width tapeWidth mc' lc' sc' rc' saved :=
  ⟨⟨bound.caches.config, ⟨bound.caches.managed.1, bound.caches.managed.2.trans hm⟩,
      ⟨bound.caches.live.1, bound.caches.live.2.trans hl⟩⟩,
    NativeUniform.tape_mono rep tapeWidth sc sc' saved.2.1 bound.tape.1 hs,
    NativeUniform.tape_mono rep tapeWidth rc rc' saved.2.2 bound.tape.2 hr⟩

variable [C.HasSum] [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)

include sizes

theorem config_size (width : Nat) (hh : header ≤ width) (config : G₁ × G₁)
    (bound : ConfigBound (Q := Q) rep width config) :
    Q.size (rep.ty configTy) config ≤ 3 * width := by
  have hp := sizes.prod_le (rep.ty point₁) (rep.ty point₁) config
  obtain ⟨hg, hk⟩ := bound
  change Q.size (rep.ty configTy) config ≤ _ at hp
  omega

include lists

theorem cache_size (width cap : Nat) (hh : header ≤ width) (cache : List ((M × G₁) × F))
    (bound : CacheBound (Q := Q) rep width cap cache) :
    Q.size (rep.ty hashCache) cache ≤ (12 * cap + 3) * width := by
  have h := CacheCompiler.list_size (key := hashKey) (val := scalar) rep sizes lists cache
    (3 * width) cap (by omega) bound.1 bound.2
  nlinarith

theorem keep_size (width cap : Nat) (hh : header ≤ width)
    (saved : keepCacheTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : KeepBound (Q := Q) rep width cap saved) :
    Q.size (rep.ty keepCacheTy) saved ≤ (12 * cap + 7) * width := by
  have hc := config_size rep sizes width hh saved.1 bound.1
  have hl := cache_size rep sizes lists width cap hh saved.2 bound.2
  have hp := sizes.prod_le (rep.ty configTy) (rep.ty hashCache) saved
  change Q.size (rep.ty keepCacheTy) saved ≤ _ at hp
  nlinarith

theorem caches_size (width managedCap liveCap : Nat) (hh : header ≤ width)
    (caches : cacheStore.Value (cryptoBase F G₁ G₂ K M))
    (bound : CachesBound (Q := Q) rep width managedCap liveCap caches) :
    Q.size (rep.ty cacheStore) caches ≤ (12 * (managedCap + liveCap) + 11) * width := by
  have hc := config_size rep sizes width hh caches.1 bound.config
  have hm := cache_size rep sizes lists width managedCap hh caches.2.1 bound.managed
  have hl := cache_size rep sizes lists width liveCap hh caches.2.2 bound.live
  have hp := @sizes.prod_le
  dsimp only [cacheStore, LanguageRepresentation.ty] at *
  grind only

theorem store_size (width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth)
    (hw : (6 * (savedCap + remainingCap) + 3) * tapeWidth ≤ width)
    (saved : storeTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap saved) :
    Q.size (rep.ty storeTy) saved ≤ (12 * (managedCap + liveCap) + 13) * width := by
  have hc := caches_size rep sizes lists width managedCap liveCap hh saved.1 bound.caches
  have htape := (NativeUniform.state_size rep sizes lists tapeWidth savedCap remainingCap ht saved.2 bound.tape).trans hw
  have hp := sizes.prod_le (rep.ty cacheStore) (rep.ty NativeUniform.stateTy) saved
  change Q.size (rep.ty storeTy) saved ≤ _ at hp
  nlinarith

theorem input_size (a : Ty CryptoAtom) (valueWidth width tapeWidth managedCap liveCap savedCap remainingCap : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hv : valueWidth ≤ 3 * width)
    (hw : (6 * (savedCap + remainingCap) + 3) * tapeWidth ≤ width)
    (input : (withStore a).Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep a valueWidth width tapeWidth managedCap liveCap savedCap remainingCap input) :
    Q.size (rep.ty (withStore a)) input ≤ (12 * (managedCap + liveCap) + 17) * width := by
  have hs := store_size rep sizes lists width tapeWidth managedCap liveCap savedCap remainingCap hh ht hw input.2 bound.2
  have ha := bound.1.trans hv
  have hp := sizes.prod_le (rep.ty a) (rep.ty storeTy) input
  change Q.size (rep.ty (withStore a)) input ≤ _ at hp
  nlinarith

end Signatures.Runtime.Schnorr.ListROM.NativeComponents

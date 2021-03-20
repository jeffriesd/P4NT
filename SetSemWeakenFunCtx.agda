
open import NestedTypeSyntax 
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open FVar
open _∋_ 

open import Categories.Category using (Category)
open import Categories.Functor using (Functor ; _∘F_)
open import NestedSetSemantics 
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Vec using (Vec ; _∷_ ;  []) 
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Data.Product hiding (curry) renaming (_×_ to _×'_)
open import Utils
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)

open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)

module SetSemWeakenFunCtx where 






open import SetEnvironments
open import SetCats
open import Categories.Category.Product using (Product ; _※_  ; πˡ ; πʳ ; _⁂_)

open import Level renaming (zero to lzero ; suc to lsuc)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)


-- taking set interpretation after weakening functorial context 
-- gives precisely the same functor 

mutual 
  SetSem-weakenFunCtx-Vec : ∀ {n} {Γ : TCCtx} → {Φ : FunCtx} → {Fs : Vec TypeExpr n}
                            → {k : ℕ} → (ψ : FVar k)
                            → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
                            → SetSemVec ⊢Fs
                              ≡ SetSemVec (foreach-preserves-weakening-FV {φ = ψ} Fs ⊢Fs)
  SetSem-weakenFunCtx-Vec {Fs = []} ψ ⊢Fs = ≡.refl 
  SetSem-weakenFunCtx-Vec {Fs = F ∷ Fs} ψ (⊢F , ⊢Fs) rewrite (SetSem-weakenFunCtx ψ ⊢F) | (SetSem-weakenFunCtx-Vec ψ ⊢Fs) = ≡.refl


  SetSem-weakenFunCtx : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
                      → {k : ℕ} → (ψ : FVar k)
                      → (⊢F : Γ ≀ Φ ⊢ F)
                      → SetSem ⊢F
                        ≡ SetSem (weakenFunCtx ψ F ⊢F)
  SetSem-weakenFunCtx ψ 𝟘-I = ≡.refl
  SetSem-weakenFunCtx ψ 𝟙-I = ≡.refl
  SetSem-weakenFunCtx ψ (AppT-I Γ∋φ Fs ⊢Fs) rewrite (SetSem-weakenFunCtx-Vec ψ ⊢Fs) = ≡.refl 
  SetSem-weakenFunCtx (ψ ^F k) (AppF-I {φ = φ ^F j} Φ∋φ Fs ⊢Fs) rewrite (SetSem-weakenFunCtx-Vec (ψ ^F k) ⊢Fs) with eqNat k j | ψ ≟ φ
  ... | yes ≡.refl | yes ≡.refl = ≡.refl
  ... | yes ≡.refl | no _       = ≡.refl
  ... | no _  | _               = ≡.refl

  SetSem-weakenFunCtx ψ (+-I ⊢F ⊢G) rewrite (SetSem-weakenFunCtx ψ ⊢F) | (SetSem-weakenFunCtx ψ ⊢G) = ≡.refl
  SetSem-weakenFunCtx ψ (×-I ⊢F ⊢G) rewrite (SetSem-weakenFunCtx ψ ⊢F) | (SetSem-weakenFunCtx ψ ⊢G) = ≡.refl
  SetSem-weakenFunCtx ψ (Nat-I ⊢F ⊢G) = ≡.refl
  SetSem-weakenFunCtx ψ (μ-I F ⊢F Gs ⊢Gs) rewrite (SetSem-weakenFunCtx-Vec ψ ⊢Gs) = ≡.refl 


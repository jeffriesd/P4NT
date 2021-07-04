module SetSem.TypeSem-Properties where 

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Syntax.NestedTypeSyntax 
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open FVar
open _∋_ 
open import SetCats
open import SetEnvironments.Core
open import SetSem.NestedSetSemantics
open import CatUtils 
open import Utils 
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; _∘ₕ_  to _∘h_ ; id to idnat)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) 
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.Category.Product using (Product ; _※_  ; πˡ ; πʳ)
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)





module VarSem-FV-properties {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {H : TypeExpr} (av : Id) (⊢H : Γ ≀ Φ ⊢ H) (pv : Id)  where 

  import Categories.NaturalTransformation.NaturalIsomorphism.Properties as NIP
  import Relation.Binary.HeterogeneousEquality as Het


  import Categories.Morphism as Mor 

  -- we are interested in isomorphisms in functor category 
  open Mor [Sets^ suc k ,Sets]
  open _≅_ -- import from/to 

  private 
    α : FVar 0 
    α = av ^F 0

    φ : FVar (suc k)
    φ = pv ^F (suc k)

  VarSem-FV-natural-equiv : ∀  {ρ ρ' : SetEnv} 
                      → (f : SetEnvMorph ρ ρ')
                      → [Sets^ suc k ,Sets] Categories.Category.[
                        Functor.F₁ (VarSem-FV φ) f
                       ≈ Functor.F₁ (VarSem-FV φ ∘F extendEnvFVar α ⊢H) f ]
  VarSem-FV-natural-equiv {ρ} {ρ'} f {Xs} {ρφXs} = ≡.refl

  -- use pointwise-iso 
  VarSem-FV-extend-iso : ∀ (ρ : SetEnv)
                    → Functor.F₀ (VarSem-FV φ) ρ ≅ Functor.F₀ (VarSem-FV φ ∘F extendEnvFVar α ⊢H) ρ 
  VarSem-FV-extend-iso ρ = record { from = idnat ; to = idnat ; iso = record { isoˡ = ≡.refl ; isoʳ = ≡.refl } }

  VarSem-FV-extend-≃ : VarSem-FV φ
                       ≃ VarSem-FV φ ∘F extendEnvFVar α ⊢H 
  VarSem-FV-extend-≃ = pointwise-iso VarSem-FV-extend-iso VarSem-FV-natural-equiv
    where open pointwise-iso {F = VarSem-FV φ} {G = VarSem-FV φ ∘F extendEnvFVar α ⊢H}



  module Mor0 = Mor [Sets^ 0 ,Sets]
  open Mor0._≅_ renaming (from to from0)

  VarSem-FV-extend-diffId-iso : ∀ (pv≢av : pv ≡.≢ av) X →
                             ([Sets^ 0 ,Sets] Mor.≅ Functor.F₀ (VarSem-FV (pv ^F 0)) X)
                             (Functor.F₀ (VarSem-FV (pv ^F 0) ∘F extendEnvFVar (av ^F 0) ⊢H) X)
  VarSem-FV-extend-diffId-iso pv≢av ρ with av ≟ pv 
  ... | yes ≡.refl = exFalso (pv≢av ≡.refl)
  ... | no p  = record { from = idnat ; to = idnat ; iso = record { isoˡ = ≡.refl ; isoʳ = ≡.refl } } 

  -- VarSem-FV-extend-diffId-natural : ∀  {ρ ρ' : SetEnv} 
  --                     → (pv ≡.≢ av)
  --                     → (f : SetEnvMorph ρ ρ')
  --                     → [Sets^ 0 ,Sets] Categories.Category.[
  --                       Functor.F₁ (VarSem-FV (pv ^F 0)) f
  --                     ≈ Functor.F₁ (VarSem-FV (pv ^F 0) ∘F extendEnvFVar α ⊢H) f ]
  -- VarSem-FV-extend-diffId-natural {ρ} {ρ'} pv≢av f = ? 

  VarSem-FV-extend-diffId-natural : ∀ (pv≢av : pv ≡.≢ av) {ρ ρ'}
                                    (f : SetEnvMorph ρ ρ') 
                                    → ([Sets^ 0 ,Sets] Category.≈
                                   ([Sets^ 0 ,Sets] Category.∘
                                    from0 (VarSem-FV-extend-diffId-iso pv≢av ρ'))
                                   (Functor.F₁ (VarSem-FV (pv ^F 0)) f))
                                  (([Sets^ 0 ,Sets] Category.∘
                                    Functor.F₁ (VarSem-FV (pv ^F 0) ∘F extendEnvFVar (av ^F 0) ⊢H)
                                    f)
                                   (from0 (VarSem-FV-extend-diffId-iso pv≢av ρ)))
  VarSem-FV-extend-diffId-natural pv≢av f with av ≟ pv 
  ... | yes ≡.refl = exFalso (pv≢av ≡.refl)
  ... | no p  = ≡.refl


  VarSem-FV-extend-diffId-≃ : (pv ≡.≢ av) → VarSem-FV (pv ^F 0)
                              ≃ VarSem-FV (pv ^F 0) ∘F extendEnvFVar α ⊢H 
  VarSem-FV-extend-diffId-≃ pv≢av = pointwise-iso (VarSem-FV-extend-diffId-iso pv≢av) (VarSem-FV-extend-diffId-natural pv≢av) 
    where open pointwise-iso {F = VarSem-FV (pv ^F 0)} {G = VarSem-FV (pv ^F 0) ∘F extendEnvFVar (av ^F 0) ⊢H}

  -- wts    

  -- SetSem ⊢H ≃ 
  -- (eval ∘F (VarSem-FV (α ^F 0) ※ const [])) 
  --   ∘F extendEnvFVar (α ^F 0) ⊢H 
  

  -- -- this doens't type-check because morphisms don't have the same type 
  -- VarSem-FV-subst-α-natural : ∀  {ρ ρ' : SetEnv} 
  --                     → (f : SetEnvMorph ρ ρ')
  --                     → Sets Categories.Category.[
  --                       Functor.F₁ (SetSem ⊢H) f
  --                      ≈ Functor.F₁ ((eval ∘F (VarSem-FV α ※ ConstF [])) ∘F extendEnvFVar α ⊢H) f ]
  -- VarSem-FV-subst-α-natural {ρ} {ρ'} f = ? 


  VarSem-FV-subst-α-equiv : ∀ (ρ : SetEnv) → Functor.F₀ (SetSem ⊢H ) ρ 
                      ≡ Functor.F₀ ((eval ∘F (VarSem-FV α ※ ConstF [])) ∘F extendEnvFVar α ⊢H) ρ 
  VarSem-FV-subst-α-equiv ρ =
  -- rewrite (extendfv-lem (SetEnv.fv ρ) α  (ConstF (Functor.F₀ (SetSem ⊢H) ρ))) = 
    let constH = ConstF (Functor.F₀ (SetSem ⊢H) ρ)
      
        constH-lem : (extendfv (SetEnv.fv ρ) α constH) α ≡ constH
        constH-lem = extendfv-lem (SetEnv.fv ρ) α constH
      in 
      begin
      --   Functor.F₀ (SetSem ⊢H) ρ
      -- ≡⟨ ≡.refl ⟩
        Functor.F₀ constH []
      ≡⟨ ≡.cong (λ F → Functor.F₀ F []) (≡.sym constH-lem) ⟩
        Functor.F₀ ((extendfv (SetEnv.fv ρ) α constH) α) []
      ∎

  module SetsM = Mor Sets

  equiv-iso : ∀ {A B : Set} → A ≡ B → A SetsM.≅ B
  equiv-iso ≡.refl = record { from = idf ; to = idf ; iso = record { isoˡ = ≡.refl ; isoʳ = ≡.refl } } 


  VarSem-FV-subst-α-iso : ∀ (ρ : SetEnv) → Functor.F₀ (SetSem ⊢H ) ρ 
                      SetsM.≅ Functor.F₀ ((eval ∘F (VarSem-FV α ※ ConstF [])) ∘F extendEnvFVar α ⊢H) ρ 
  VarSem-FV-subst-α-iso ρ = equiv-iso (VarSem-FV-subst-α-equiv ρ)


  VarSem-FV-subst-α-natural2 : ∀ {ρ ρ' : SetEnv}
                               (f : SetEnvCat Categories.Category.[ ρ , ρ' ]) →
                             (Sets Category.≈
                              (Sets Category.∘ SetsM._≅_.from (VarSem-FV-subst-α-iso ρ'))
                              (Functor.F₁ (SetSem ⊢H) f))
                             ((Sets Category.∘
                               Functor.F₁
                               ((eval ∘F (VarSem-FV (av ^F 0) ※ ConstF [])) ∘F
                                extendEnvFVar (av ^F 0) ⊢H)
                               f)
                              (SetsM._≅_.from (VarSem-FV-subst-α-iso ρ)))
  VarSem-FV-subst-α-natural2 {X} {Y} f {x} with eqNat zero zero | av ≟ av 
  ... | yes ≡.refl | yes ≡.refl = ≡.refl
  ... | yes ≡.refl | no av≢av  = exFalso (av≢av ≡.refl)
  ... | no z≢z     | _ = exFalso (z≢z ≡.refl)

  -- use pointwise-iso to define natural isomorphism 
  VarSem-FV-subst-α-≃ : SetSem ⊢H 
                      ≃ (eval ∘F (VarSem-FV α ※ ConstF [])) ∘F extendEnvFVar α ⊢H 
  VarSem-FV-subst-α-≃ = pointwise-iso VarSem-FV-subst-α-iso VarSem-FV-subst-α-natural2
    where open pointwise-iso {F = SetSem ⊢H} {G = (eval ∘F (VarSem-FV α ※ ConstF [])) ∘F extendEnvFVar α ⊢H}





module VarSem-TC-properties {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {H : TypeExpr} (α : FVar 0) (⊢H : Γ ≀ Φ ⊢ H) (φ : TCVar k)  where 

  import Categories.NaturalTransformation.NaturalIsomorphism.Properties as NIP
  import Relation.Binary.HeterogeneousEquality as Het


  import Categories.Morphism as Mor 

  -- we are interested in isomorphisms in functor category 
  open Mor [Sets^ k ,Sets]
  open _≅_ -- import from/to 

  VarSem-TC-natural-equiv : ∀  {ρ ρ' : SetEnv} 
                      → (f : SetEnvMorph ρ ρ')
                      → [Sets^ k ,Sets] Categories.Category.[
                        Functor.F₁ (VarSem-TC φ) f
                       ≈ Functor.F₁ (VarSem-TC φ ∘F extendEnvFVar α ⊢H) f ]
  VarSem-TC-natural-equiv {ρ} {ρ'} f {Xs} {ρφXs} = mkIdNatTr-eq (SetEnv.tc ρ φ) (SetEnv.tc ρ' φ) (eqTC-ext f φ) (eqTC-ext (Functor.F₁ (extendEnvFVar α ⊢H) f) φ)


  -- use pointwise-iso 
  VarSem-TC-extend-iso : ∀ (ρ : SetEnv)
                    → Functor.F₀ (VarSem-TC φ) ρ ≅ Functor.F₀ (VarSem-TC φ ∘F extendEnvFVar α ⊢H) ρ 
  VarSem-TC-extend-iso ρ = record { from =  idnat ; to = idnat ; iso = record { isoˡ = ≡.refl ; isoʳ = ≡.refl } }


  -- if we extend functorial part of environment, the extension doesn't affect VarSem-TC 
  VarSem-TC-extend-≃ : VarSem-TC φ
                       ≃ VarSem-TC φ ∘F extendEnvFVar α ⊢H 
  VarSem-TC-extend-≃ = pointwise-iso VarSem-TC-extend-iso VarSem-TC-natural-equiv 
    where open pointwise-iso {F = VarSem-TC φ} {G = VarSem-TC φ ∘F extendEnvFVar α ⊢H}


{-# OPTIONS --rewriting #-}
-- --confluence-check #-}
open import Agda.Builtin.Equality.Rewrite
open import Level 


open import Categories.Functor using (Functor ; _∘F_ ) 
open import Categories.Category 
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) 
open import Categories.NaturalTransformation using (NaturalTransformation ; ntHelper)
open import Categories.Morphism
open import Categories.Object.Terminal

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as ≡ 
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Vec using (Vec ; _∷_ )


module RTEnvironments.Properties {o l e o' l' e' : Level}
  (C : Category o' l' e') 
  (D : ℕ → Category o l e) 
  (Dt : (k : ℕ) → Category.Obj (D k))
  (Dtm : (k : ℕ) → {d : Category.Obj (D k)} → (D k) [ d , Dt k ])
  (toD0 : Functor C (D 0)) 
  where 
-- About this file: 
-- In this file we generalize the environment constructions 
-- to work for any categories D and C.
--
-- D is a family of categories indexed by natural numbers, while C is 
-- a category whose objects can be turned into objects of D 0 
--
-- For our purposes, we will use D = RTCat and C = Rels 
-- 
-- The objects of D k are used to interpret functor variables of arity k. 
-- Morphism of D are used to represent morphisms of environments. 
-- Dt and Dtm are used to define trivFVEnv. 



private module C = Category C 


open import RTEnvironments.Core D Dt Dtm 
open import RTEnvironments.EnvironmentExtension C D Dt Dtm toD0 
open import NestedTypeSyntax using (FVar)
import SetCats 

open SetCats.VecCat C
open SetCats.0Functors C


:fv=-unwind : ∀ {n k : ℕ} → (ρ : Env) → (φ : FVar k) → (φs : Vec (FVar k) n) 
              → (F : DObj k) → (Fs : Vec (DObj k) n) 
              → ρ [ φ ∷ φs :fvs= F ∷ Fs ] 
              ≡ (ρ [ φs :fvs= Fs ]) [ φ :fv= F ]
:fv=-unwind Env[ tc , fv ] φ Vec.[] F Vec.[] = ≡.refl
:fv=-unwind Env[ tc , fv ] φ (ψ ∷ ψs) F (G ∷ Gs) = ≡.refl 
-- doesn't pass confluence check, but maybe this is ok 
-- {-# REWRITE :fv=-unwind #-}


-- extending functorial αs does not alter the tc part of ρ 
extendEnv-ρ×As-tc-lem : ∀ {k} → (αs : Vec (FVar 0) k) (ρ : Env) (Xs : Vec C.Obj k)
                → (Functor.F₀ (extendEnv-ρ×As {k} αs) (ρ , Xs))
                  ≡TC ρ
extendEnv-ρ×As-tc-lem αs ρ Xs = ≡.sym (extendfv-vec-preserves-tc ρ αs (toRT0Vec Xs))


-- proof for a particular arity 
extendEnv-ρ×As-tc-lem-expl : ∀ {k j} → (αs : Vec (FVar 0) k) (ρ : Env) (Xs : Vec C.Obj k)
                → (Functor.F₀ (extendEnv-ρ×As {k} αs) (ρ , Xs))
                ≡TC-ext[ j ] ρ
extendEnv-ρ×As-tc-lem-expl αs ρ Xs = ≡.sym (extendfv-vec-preserves-tc-ext ρ αs (toRT0Vec Xs))


ForgetFVEnv-Extend-≃ : (Extend : Functor EnvCat EnvCat)
                    → (preserves-tc : ∀ ρ → Functor.F₀ Extend ρ ≡TC ρ)
                    → ForgetFVEnv ≃ ForgetFVEnv ∘F Extend 
ForgetFVEnv-Extend-≃ Extend preserves-tc =
            record { F⇒G = FtoG 
                   ; F⇐G = FfromG 
                   ; iso = λ ρ → iso ρ } 

         where to-η : ∀ ρ → EnvMorph (Functor.F₀ ForgetFVEnv ρ) (Functor.F₀ (ForgetFVEnv ∘F Extend) ρ)
               to-η ρ rewrite preserves-tc ρ = idEnv 
               to-commute : ∀ {ρ ρ' : Env} (f : EnvMorph ρ ρ') 
                            → (EnvCat Category.≈
                            (EnvCat Category.∘ to-η ρ') (Functor.F₁ ForgetFVEnv f))
                            ((EnvCat Category.∘ Functor.F₁ (ForgetFVEnv ∘F Extend) f)
                            (to-η ρ))
               to-commute {ρ} {ρ'} f {k} rewrite preserves-tc ρ | preserves-tc ρ' = Category.Equiv.refl (D k)

               from-η : ∀ ρ → EnvMorph (Functor.F₀ (ForgetFVEnv ∘F Extend) ρ) (Functor.F₀ ForgetFVEnv ρ) 
               from-η ρ rewrite preserves-tc ρ = idEnv 
               from-commute : ∀ {ρ ρ' : Env} (f : EnvMorph ρ ρ') 
                            → (EnvCat Category.≈
                            (EnvCat Category.∘ from-η ρ') (Functor.F₁ (ForgetFVEnv ∘F Extend) f))
                            ((EnvCat Category.∘ Functor.F₁ ForgetFVEnv f)
                            (from-η ρ))
               from-commute {ρ} {ρ'} f {k} rewrite preserves-tc ρ | preserves-tc ρ' = Category.Equiv.refl (D k)

               FtoG : NaturalTransformation ForgetFVEnv (ForgetFVEnv ∘F Extend)
               FtoG = ntHelper (record { η = to-η ; commute = to-commute })
               FfromG : NaturalTransformation (ForgetFVEnv ∘F Extend) ForgetFVEnv
               FfromG = ntHelper (record { η = from-η ; commute = from-commute })

               iso : ∀ (ρ : Env) → 
                    Iso EnvCat (NaturalTransformation.η FtoG ρ)
                    (NaturalTransformation.η FfromG ρ)
               iso ρ rewrite preserves-tc ρ = record { isoˡ =  λ {k} → Category.identityˡ (D k)  ; isoʳ = λ {k} → Category.identityʳ (D k)  } 


    {- -- not used anywhere 
    -- move this to Environment.Properties 
    SetSem-extendEnv-αs-eqtc : ∀ {k} → (ρ : Env) (αs : Vec (FVar 0) k) (Xs Ys : Vec C.Obj k) 
                    →   Functor.F₀ (extendEnv-αs αs ρ) Xs
                    ≡TC Functor.F₀ (extendEnv-αs αs ρ) Ys
    SetSem-extendEnv-αs-eqtc ρ αs Xs Ys = begin
            ((λ {k} → Env.tc (Functor.F₀ (extendEnv-αs αs ρ) Xs) {k}))
            ≡⟨ ≡.sym (extendfv-vec-preserves-tc ρ αs (toRT0Vec Xs)) ⟩
            (λ {k} → Env.tc ρ {k}) 
            ≡⟨ (extendfv-vec-preserves-tc ρ αs (toRT0Vec Ys)) ⟩
            (((λ {k} → Env.tc (Functor.F₀ (extendEnv-αs αs ρ) Ys) {k})))
            ∎ 

    -- special case of SetSem-eqTC-const 
    SetSem-const-extendEnv-αs : ∀ {k} {Γ} {F} → (⊢F : Γ ≀ ∅ ⊢ F) (ρ : Env) (αs : Vec (FVar 0) k) (Xs Ys : Vec C.Obj k) 
                    → Functor.F₀ (SetSem ⊢F) (Functor.F₀ (extendEnv-αs αs ρ) Xs)
                    ≡ Functor.F₀ (SetSem ⊢F) (Functor.F₀ (extendEnv-αs αs ρ) Ys)
    SetSem-const-extendEnv-αs ⊢F ρ αs Xs Ys = SetSem-eqTC-const ⊢F ((Functor.F₀ (extendEnv-αs αs ρ) Xs)) 
                                                            ((Functor.F₀ (extendEnv-αs αs ρ) Ys)) 
                                                            (SetSem-extendEnv-αs-eqtc ρ αs Xs Ys) 

    Δ-const-proof : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : Env) (αs : Vec (FVar 0) k) (Xs Ys : Vec C.Obj k) 
                    → Functor.F₀ (ContextInterp Δ) (Functor.F₀ (extendEnv-αs αs ρ) Xs)
                    ≡ Functor.F₀ (ContextInterp Δ) (Functor.F₀ (extendEnv-αs αs ρ) Ys)
    Δ-const-proof Δ∅ ρ αs Xs Ys = ≡.refl
    Δ-const-proof (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) ρ αs Xs Ys = ≡.cong₂ _×'_ (Δ-const-proof Δ ρ αs Xs Ys) (SetSem-const-extendEnv-αs ⊢F ρ αs Xs Ys)
    -}


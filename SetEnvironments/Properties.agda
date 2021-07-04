{-# OPTIONS --rewriting #-}
-- --confluence-check #-}
open import Agda.Builtin.Equality.Rewrite

module SetEnvironments.Properties where 

open import SetEnvironments.Core
open import SetEnvironments.EnvironmentExtension
open import Syntax.NestedTypeSyntax using (FVar)
open import SetCats using (to0Functors)

open import Categories.Functor using (Functor ; _∘F_ ) 
open import Categories.Category using (Category)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) 
open import Categories.NaturalTransformation using (NaturalTransformation ; ntHelper)
open import Categories.Morphism

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡ 
open import Data.Vec using (Vec ; _∷_ )
open import SetCats using (Sets ; Sets^)


:fv=-unwind : ∀ {n k : ℕ} → (ρ : SetEnv) → (φ : FVar k) → (φs : Vec (FVar k) n) 
              → (F : Functor (Sets^ k) Sets) → (Fs : Vec (Functor (Sets^ k ) (Sets )) n) 
              → ρ [ φ ∷ φs :fvs= F ∷ Fs ]Set 
              ≡ (ρ [ φs :fvs= Fs ]Set) [ φ :fv= F ]Set
:fv=-unwind SetEnv[ tc , fv ] φ Vec.[] F Vec.[] = refl
:fv=-unwind SetEnv[ tc , fv ] φ (ψ ∷ ψs) F (G ∷ Gs) = refl 
-- doesn't pass confluence check, but maybe this is ok 
-- {-# REWRITE :fv=-unwind #-}


-- extending functorial αs does not alter the tc part of ρ 
extendSetEnv-ρ×As-tc-lem : ∀ {k} → (αs : Vec (FVar 0) k) (ρ : SetEnv) (Xs : Vec Set k)
                → (Functor.F₀ (extendSetEnv-ρ×As {k} αs) (ρ , Xs))
                  ≡TC ρ
extendSetEnv-ρ×As-tc-lem αs ρ Xs = ≡.sym (extendfv-vec-preserves-tc ρ αs (to0Functors Xs))


-- proof for a particular arity 
extendSetEnv-ρ×As-tc-lem-expl : ∀ {k j} → (αs : Vec (FVar 0) k) (ρ : SetEnv) (Xs : Vec Set k)
                → (Functor.F₀ (extendSetEnv-ρ×As {k} αs) (ρ , Xs))
                ≡TC-ext[ j ] ρ
extendSetEnv-ρ×As-tc-lem-expl αs ρ Xs = sym (extendfv-vec-preserves-tc-ext ρ αs (to0Functors Xs))


ForgetFVSetEnv-Extend-≃ : (Extend : Functor SetEnvCat SetEnvCat)
                    → (preserves : ∀ ρ → Functor.F₀ Extend ρ ≡TC ρ)
                    → ForgetFVSetEnv ≃ ForgetFVSetEnv ∘F Extend 
ForgetFVSetEnv-Extend-≃ Extend preserves =
            record { F⇒G = FtoG 
                   ; F⇐G = FfromG 
                   ; iso = λ ρ → iso ρ } 

         where to-η : ∀ ρ → SetEnvMorph (Functor.F₀ ForgetFVSetEnv ρ) (Functor.F₀ (ForgetFVSetEnv ∘F Extend) ρ)
               to-η ρ rewrite preserves ρ = idSetEnv 
               to-commute : ∀ {ρ ρ' : SetEnv} (f : SetEnvMorph ρ ρ') 
                            → (SetEnvCat Category.≈
                            (SetEnvCat Category.∘ to-η ρ') (Functor.F₁ ForgetFVSetEnv f))
                            ((SetEnvCat Category.∘ Functor.F₁ (ForgetFVSetEnv ∘F Extend) f)
                            (to-η ρ))
               to-commute {ρ} {ρ'} f rewrite preserves ρ | preserves ρ' = refl 

               from-η : ∀ ρ → SetEnvMorph (Functor.F₀ (ForgetFVSetEnv ∘F Extend) ρ) (Functor.F₀ ForgetFVSetEnv ρ) 
               from-η ρ rewrite preserves ρ = idSetEnv 
               from-commute : ∀ {ρ ρ' : SetEnv} (f : SetEnvMorph ρ ρ') 
                            → (SetEnvCat Category.≈
                            (SetEnvCat Category.∘ from-η ρ') (Functor.F₁ (ForgetFVSetEnv ∘F Extend) f))
                            ((SetEnvCat Category.∘ Functor.F₁ ForgetFVSetEnv f)
                            (from-η ρ))
               from-commute {ρ} {ρ'} f rewrite preserves ρ | preserves ρ' = refl 

               FtoG : NaturalTransformation ForgetFVSetEnv (ForgetFVSetEnv ∘F Extend)
               FtoG = ntHelper (record { η = to-η ; commute = to-commute })
               FfromG : NaturalTransformation (ForgetFVSetEnv ∘F Extend) ForgetFVSetEnv
               FfromG = ntHelper (record { η = from-η ; commute = from-commute })

               iso : ∀ (ρ : SetEnv) → 
                    Iso SetEnvCat (NaturalTransformation.η FtoG ρ)
                    (NaturalTransformation.η FfromG ρ)
               iso ρ rewrite preserves ρ = record { isoˡ = refl ; isoʳ = refl }




    {- -- not used anywhere 
    -- move this to SetEnvironment.Properties 
    SetSem-extendSetEnv-αs-eqtc : ∀ {k} → (ρ : SetEnv) (αs : Vec (FVar 0) k) (Xs Ys : Vec Set k) 
                    →   Functor.F₀ (extendSetEnv-αs αs ρ) Xs
                    ≡TC Functor.F₀ (extendSetEnv-αs αs ρ) Ys
    SetSem-extendSetEnv-αs-eqtc ρ αs Xs Ys = begin
            ((λ {k} → SetEnv.tc (Functor.F₀ (extendSetEnv-αs αs ρ) Xs) {k}))
            ≡⟨ ≡.sym (extendfv-vec-preserves-tc ρ αs (to0Functors Xs)) ⟩
            (λ {k} → SetEnv.tc ρ {k}) 
            ≡⟨ (extendfv-vec-preserves-tc ρ αs (to0Functors Ys)) ⟩
            (((λ {k} → SetEnv.tc (Functor.F₀ (extendSetEnv-αs αs ρ) Ys) {k})))
            ∎ 

    -- special case of SetSem-eqTC-const 
    SetSem-const-extendSetEnv-αs : ∀ {k} {Γ} {F} → (⊢F : Γ ≀ ∅ ⊢ F) (ρ : SetEnv) (αs : Vec (FVar 0) k) (Xs Ys : Vec Set k) 
                    → Functor.F₀ (SetSem ⊢F) (Functor.F₀ (extendSetEnv-αs αs ρ) Xs)
                    ≡ Functor.F₀ (SetSem ⊢F) (Functor.F₀ (extendSetEnv-αs αs ρ) Ys)
    SetSem-const-extendSetEnv-αs ⊢F ρ αs Xs Ys = SetSem-eqTC-const ⊢F ((Functor.F₀ (extendSetEnv-αs αs ρ) Xs)) 
                                                            ((Functor.F₀ (extendSetEnv-αs αs ρ) Ys)) 
                                                            (SetSem-extendSetEnv-αs-eqtc ρ αs Xs Ys) 

    Δ-const-proof : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : SetEnv) (αs : Vec (FVar 0) k) (Xs Ys : Vec Set k) 
                    → Functor.F₀ (ContextInterp Δ) (Functor.F₀ (extendSetEnv-αs αs ρ) Xs)
                    ≡ Functor.F₀ (ContextInterp Δ) (Functor.F₀ (extendSetEnv-αs αs ρ) Ys)
    Δ-const-proof Δ∅ ρ αs Xs Ys = ≡.refl
    Δ-const-proof (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) ρ αs Xs Ys = ≡.cong₂ _×'_ (Δ-const-proof Δ ρ αs Xs Ys) (SetSem-const-extendSetEnv-αs ⊢F ρ αs Xs Ys)
    -}


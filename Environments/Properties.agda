{-# OPTIONS --rewriting #-}
-- --confluence-check #-}
open import Agda.Builtin.Equality.Rewrite
open import Level 


open import Categories.Functor using (Functor ; _∘F_ ) 
open import Categories.Category using (Category)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) 
open import Categories.NaturalTransformation using (NaturalTransformation ; ntHelper)
open import Categories.Morphism
open import Categories.Object.Terminal


module Environments.Properties {o l e : Level} (C : Category o l e) (C⊤ : Terminal C)  where 

private module C = Category C 

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡ 
open import Data.Vec using (Vec ; _∷_ )


open import Environments.Core C C⊤
open import Environments.EnvironmentExtension C C⊤ 
open import NestedTypeSyntax using (FVar)
import SetCats 

open SetCats.VecCat C 
open SetCats.0Functors C


:fv=-unwind : ∀ {n k : ℕ} → (ρ : GenEnv) → (φ : FVar k) → (φs : Vec (FVar k) n) 
              → (F : Functor (C^ k) C) → (Fs : Vec (Functor (C^ k ) (C )) n) 
              → ρ [ φ ∷ φs :fvs= F ∷ Fs ] 
              ≡ (ρ [ φs :fvs= Fs ]) [ φ :fv= F ]
:fv=-unwind Env[ tc , fv ] φ Vec.[] F Vec.[] = refl
:fv=-unwind Env[ tc , fv ] φ (ψ ∷ ψs) F (G ∷ Gs) = refl 
-- doesn't pass confluence check, but maybe this is ok 
{-# REWRITE :fv=-unwind #-}


-- extending functorial αs does not alter the tc part of ρ 
extendGenEnv-ρ×As-tc-lem : ∀ {k} → (αs : Vec (FVar 0) k) (ρ : GenEnv) (Xs : Vec C.Obj k)
                → (Functor.F₀ (extendGenEnv-ρ×As {k} αs) (ρ , Xs))
                  ≡TC ρ
extendGenEnv-ρ×As-tc-lem αs ρ Xs = ≡.sym (extendfv-vec-preserves-tc ρ αs (to0FunctorsGen Xs))


-- proof for a particular arity 
extendGenEnv-ρ×As-tc-lem-expl : ∀ {k j} → (αs : Vec (FVar 0) k) (ρ : GenEnv) (Xs : Vec C.Obj k)
                → (Functor.F₀ (extendGenEnv-ρ×As {k} αs) (ρ , Xs))
                ≡TC-ext[ j ] ρ
extendGenEnv-ρ×As-tc-lem-expl αs ρ Xs = sym (extendfv-vec-preserves-tc-ext ρ αs (to0FunctorsGen Xs))


ForgetFVEnv-Extend-≃ : (Extend : Functor GenEnvCat GenEnvCat)
                    → (preserves : ∀ ρ → Functor.F₀ Extend ρ ≡TC ρ)
                    → ForgetFVEnv ≃ ForgetFVEnv ∘F Extend 
ForgetFVEnv-Extend-≃ Extend preserves =
            record { F⇒G = FtoG 
                   ; F⇐G = FfromG 
                   ; iso = λ ρ → iso ρ } 

         where to-η : ∀ ρ → GenEnvMorph (Functor.F₀ ForgetFVEnv ρ) (Functor.F₀ (ForgetFVEnv ∘F Extend) ρ)
               to-η ρ rewrite preserves ρ = idGenEnv 
               to-commute : ∀ {ρ ρ' : GenEnv} (f : GenEnvMorph ρ ρ') 
                            → (GenEnvCat Category.≈
                            (GenEnvCat Category.∘ to-η ρ') (Functor.F₁ ForgetFVEnv f))
                            ((GenEnvCat Category.∘ Functor.F₁ (ForgetFVEnv ∘F Extend) f)
                            (to-η ρ))
               to-commute {ρ} {ρ'} f rewrite preserves ρ | preserves ρ' = C.Equiv.refl

               from-η : ∀ ρ → GenEnvMorph (Functor.F₀ (ForgetFVEnv ∘F Extend) ρ) (Functor.F₀ ForgetFVEnv ρ) 
               from-η ρ rewrite preserves ρ = idGenEnv 
               from-commute : ∀ {ρ ρ' : GenEnv} (f : GenEnvMorph ρ ρ') 
                            → (GenEnvCat Category.≈
                            (GenEnvCat Category.∘ from-η ρ') (Functor.F₁ (ForgetFVEnv ∘F Extend) f))
                            ((GenEnvCat Category.∘ Functor.F₁ ForgetFVEnv f)
                            (from-η ρ))
               from-commute {ρ} {ρ'} f rewrite preserves ρ | preserves ρ' = C.Equiv.refl

               FtoG : NaturalTransformation ForgetFVEnv (ForgetFVEnv ∘F Extend)
               FtoG = ntHelper (record { η = to-η ; commute = to-commute })
               FfromG : NaturalTransformation (ForgetFVEnv ∘F Extend) ForgetFVEnv
               FfromG = ntHelper (record { η = from-η ; commute = from-commute })

               iso : ∀ (ρ : GenEnv) → 
                    Iso GenEnvCat (NaturalTransformation.η FtoG ρ)
                    (NaturalTransformation.η FfromG ρ)
               iso ρ rewrite preserves ρ = record { isoˡ = C.identity² ;  isoʳ = C.identity²  } 


    {- -- not used anywhere 
    -- move this to GenEnvironment.Properties 
    SetSem-extendGenEnv-αs-eqtc : ∀ {k} → (ρ : GenEnv) (αs : Vec (FVar 0) k) (Xs Ys : Vec C.Obj k) 
                    →   Functor.F₀ (extendGenEnv-αs αs ρ) Xs
                    ≡TC Functor.F₀ (extendGenEnv-αs αs ρ) Ys
    SetSem-extendGenEnv-αs-eqtc ρ αs Xs Ys = begin
            ((λ {k} → GenEnv.tc (Functor.F₀ (extendGenEnv-αs αs ρ) Xs) {k}))
            ≡⟨ ≡.sym (extendfv-vec-preserves-tc ρ αs (to0FunctorsGen Xs)) ⟩
            (λ {k} → GenEnv.tc ρ {k}) 
            ≡⟨ (extendfv-vec-preserves-tc ρ αs (to0FunctorsGen Ys)) ⟩
            (((λ {k} → GenEnv.tc (Functor.F₀ (extendGenEnv-αs αs ρ) Ys) {k})))
            ∎ 

    -- special case of SetSem-eqTC-const 
    SetSem-const-extendGenEnv-αs : ∀ {k} {Γ} {F} → (⊢F : Γ ≀ ∅ ⊢ F) (ρ : GenEnv) (αs : Vec (FVar 0) k) (Xs Ys : Vec C.Obj k) 
                    → Functor.F₀ (SetSem ⊢F) (Functor.F₀ (extendGenEnv-αs αs ρ) Xs)
                    ≡ Functor.F₀ (SetSem ⊢F) (Functor.F₀ (extendGenEnv-αs αs ρ) Ys)
    SetSem-const-extendGenEnv-αs ⊢F ρ αs Xs Ys = SetSem-eqTC-const ⊢F ((Functor.F₀ (extendGenEnv-αs αs ρ) Xs)) 
                                                            ((Functor.F₀ (extendGenEnv-αs αs ρ) Ys)) 
                                                            (SetSem-extendGenEnv-αs-eqtc ρ αs Xs Ys) 

    Δ-const-proof : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : GenEnv) (αs : Vec (FVar 0) k) (Xs Ys : Vec C.Obj k) 
                    → Functor.F₀ (ContextInterp Δ) (Functor.F₀ (extendGenEnv-αs αs ρ) Xs)
                    ≡ Functor.F₀ (ContextInterp Δ) (Functor.F₀ (extendGenEnv-αs αs ρ) Ys)
    Δ-const-proof Δ∅ ρ αs Xs Ys = ≡.refl
    Δ-const-proof (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) ρ αs Xs Ys = ≡.cong₂ _×'_ (Δ-const-proof Δ ρ αs Xs Ys) (SetSem-const-extendGenEnv-αs ⊢F ρ αs Xs Ys)
    -}


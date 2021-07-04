


module RelEnvironments.Properties where

-- open import RelCats using (Rels ; RelTerminal)
-- 
-- open import Environments.Properties (Rels) (RelTerminal) public 


open import RelEnvironments.Core
open import SetEnvironments.Core

open import Categories.Functor
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function renaming (_∘_ to _∘'_) 
open import Relation.Nullary using (Dec; yes; no; ¬_)



open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Syntax.NestedTypeSyntax 
open import RelSem.RelCats 
open RelObj
open import Data.Product renaming (_×_ to _×'_) 
open import SetCats
open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Category.Product
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
import Categories.NaturalTransformation as NT 
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_ ; niHelper)
import Categories.NaturalTransformation.NaturalIsomorphism as NI 

open import RelEnvironments.EnvironmentExtension
open import SetEnvironments.EnvironmentExtension




-- this module provides a natural isomorphism showing that
-- a functor F distribues over extendEnv2 in some sense 
module _ (F : ∀ {j} → Functor (RTCat j) [Sets^ j ,Sets]) where 

  abstract 
  
    genlem-η : ∀ {k} (φ : FVar k) (ρ : RelEnv) (Rt : RTObj k)
            → SetEnvMorph (Functor.F₀ (EnvFunc-RT F ∘F extendRelEnv2 φ) (ρ , Rt))
                            (Functor.F₀ (extendSetEnv2 φ ∘F (EnvFunc-RT F ⁂ F)) (ρ , Rt))
    genlem-η φ@(p ^F k) ρ Rt = SetEnvM[ ≡.refl , fvm ] 
        where fvm : ∀ {j : ℕ} → (ψ : FVar j)
                    → NaturalTransformation
                    (SetEnv.fv (Functor.F₀ (EnvFunc-RT F) (ρ [ φ :fv= Rt ]Rel)) ψ)
                    (SetEnv.fv (Functor.F₀ (EnvFunc-RT F) ρ [ φ :fv= Functor.F₀ F Rt ]Set) ψ)
              fvm (p' ^F j) with eqNat k j | p ≟ p'
              ... | yes ≡.refl | yes ≡.refl = idnat 
              ... | yes ≡.refl | no _ = idnat 
              ... | no _  | _  = idnat 


    genlem-η' : ∀ {k} (φ : FVar k) (ρ : RelEnv) (Rt : RTObj k) 
            → SetEnvMorph ((Functor.F₀ (EnvFunc-RT F) ρ) [ φ :fv= Functor.F₀ F Rt ]Set)
                        (Functor.F₀ (EnvFunc-RT F) (ρ [ φ :fv= Rt ]Rel))
    genlem-η' φ@(p ^F k) ρ Rt = SetEnvM[ ≡.refl , fvm ]  
        where fvm : ∀ {j : ℕ} → (ψ : FVar j)
                    → NaturalTransformation
                        (SetEnv.fv (Functor.F₀ (EnvFunc-RT F) ρ [ φ :fv= Functor.F₀ F Rt ]Set) ψ)
                        (SetEnv.fv (Functor.F₀ (EnvFunc-RT F) (ρ [ φ :fv= Rt ]Rel)) ψ)
              fvm (p' ^F j) with eqNat k j | p ≟ p'
              ... | yes ≡.refl | yes ≡.refl = idnat 
              ... | yes ≡.refl | no _ = idnat 
              ... | no _  | _  = idnat 


    genlem-commute : ∀ {k} (φ : FVar k) {ρ ρ' : RelEnv}
                → (f : RelEnvMorph ρ ρ') {Rt St : RTObj k}
                → (m : RTMorph Rt St)
                → SetEnvCat [
                    genlem-η φ ρ' St  
                    ∘SetEnv Functor.F₁ ((EnvFunc-RT F) ∘F extendRelEnv2 φ) (f , m)
                    ≈ 
                    Functor.F₁ (extendSetEnv2 φ ∘F ((EnvFunc-RT F) ⁂ F)) (f , m)
                    ∘SetEnv genlem-η φ ρ Rt 
                ] 
    genlem-commute φ@(p ^F k) f@(RelEnvM[ ≡.refl  , fv ]) m {j} {ψ@(s ^F j)} with eqNat k j | p ≟ s
    ... | yes ≡.refl | yes ≡.refl = Functor.F-resp-≈ F (Category.identityˡ (RTCat j) {f = m})
    ... | yes ≡.refl | no _ = Functor.F-resp-≈ F (Category.identityˡ (RTCat j) {f = fv ψ}) 
    ... | no _  | _  =  Functor.F-resp-≈ F (Category.identityˡ (RTCat j) {f = fv ψ}) 


    genlem-isoˡ : ∀ {k} (φ : FVar k) (ρ : RelEnv) (Rt : RTObj k)
            → SetEnvCat [
                genlem-η' φ ρ Rt ∘SetEnv genlem-η φ ρ Rt
                ≈ idSetEnv ] 
    genlem-isoˡ φ@(p ^F k) ρ Rt {j} {ψ@(s ^F j)} with eqNat k j | p ≟ s
    ... | yes ≡.refl | yes ≡.refl = ≡.refl
    ... | yes ≡.refl | no _ = ≡.refl
    ... | no _  | _  = ≡.refl


    genlem-isoʳ : ∀ {k} (φ : FVar k) (ρ : RelEnv) (Rt : RTObj k)
            → SetEnvCat [
                genlem-η φ ρ Rt ∘SetEnv genlem-η' φ ρ Rt
                ≈ idSetEnv ] 
    genlem-isoʳ φ@(p ^F k) ρ Rt {j} {ψ@(s ^F j)} with eqNat k j | p ≟ s
    ... | yes ≡.refl | yes ≡.refl = ≡.refl
    ... | yes ≡.refl | no _ = ≡.refl
    ... | no _  | _  = ≡.refl

    genlem : ∀ {k : ℕ} (φ : FVar k) 
            → EnvFunc-RT F ∘F extendRelEnv2 φ
            ≃ extendSetEnv2 φ ∘F (EnvFunc-RT F ⁂ F)
    genlem φ = niHelper (record { η = λ { (ρ , Rt) → genlem-η φ ρ Rt  }
                            ; η⁻¹ = λ { (ρ , Rt) → genlem-η' φ ρ Rt } 
                            ; commute = λ { (f , d) → genlem-commute φ f d  } 
                            ; iso = λ { (ρ , Rt) → record { isoˡ = genlem-isoˡ φ ρ Rt ; isoʳ = genlem-isoʳ φ ρ Rt } } }) 


    -- -- how can we generalize this to any environment extension functor? 
    -- genlem2 : (E : Functor C RelEnvCat) (E' : Functor C SetEnvCat)
    --         → EnvFunc-RT F ∘F E
    --         ≃ E' ∘F EnvFunc-RT F 



    -- we can also prove that any functor F distributes over
    -- apply ApplyRelEnv/ApplySetEnv 
    ApplyFV-EnvFunc-≃ : ∀ {k : ℕ} (φ : FVar k) 
            → F ∘F (ApplyRelEnv-FV φ)
            ≃ (ApplySetEnv-FV φ) ∘F EnvFunc-RT F 
    ApplyFV-EnvFunc-≃ φ =
      niHelper (record { η = λ ρ → idnat 
                       ; η⁻¹ = λ ρ → idnat 
                       ; commute = λ { RelEnvM[ ≡.refl , fvm ] → ≡.refl } 
                       ; iso = λ ρ → record { isoˡ = ≡.refl ; isoʳ = ≡.refl } })
  





{-
π₁Env-ρ×As-η : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv) (Rs : Vec RelObj k) 
               -- → SetEnvMorph (Functor.F₀ (π₁Env ∘F extendRelEnv-ρ×As αs) (ρ , Rs))
               --               (Functor.F₀ (extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k)) (ρ , Rs))
               → SetEnvMorph (Functor.F₀ π₁Env (ρ [ αs :fvs= vmap ConstRT Rs ]Rel ))
                             ((Functor.F₀ π₁Env ρ) [ αs :fvs= vmap ConstF (vecfst Rs) ]Set)
π₁Env-ρ×As-η [] ρ [] = idSetEnv
π₁Env-ρ×As-η (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) = SetEnvM[ ≡.refl , fvm ]  
    where
          -- rec = π₁Env-ρ×As-η αs ρ Rs 
          fvm : {j : ℕ } (φ : FVar j) → [Sets^ j ,Sets] [
                    SetEnv.fv (Functor.F₀ π₁Env (ρ [ α ∷ αs :fvs= ConstRT R ∷ vmap ConstRT Rs ]Rel)) φ
                  -- , SetEnv.fv (Functor.₀ (extendSetEnv-ρ×As (α ∷ αs)) (Functor.₀ (EnvFunc-RT F ⁂ Func^ Rels Sets G (suc k)) (ρ , R ∷ Rs))) φ
                  -- , SetEnv.fv (Functor.₀ (extendSetEnv-ρ×As (α ∷ αs)) ((Functor.F₀ π₁Env ρ) [ α ∷ αs  )) φ
                  , SetEnv.fv ((Functor.F₀ π₁Env ρ) [ α ∷ αs :fvs= vmap ConstF (vecfst (R ∷ Rs)) ]Set) φ 
                    ]

          fvm φ@(p ^F j) with eqNat z j | a ≟ p
          ... | yes ≡.refl | yes ≡.refl = idnat
          ... | yes ≡.refl | no _ = SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ Rs) φ
          ... | no _  | _  = SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ Rs) φ



π₁Env-ρ×As-η' : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv) (Rs : Vec RelObj k) 
               -- → SetEnvMorph (Functor.F₀ (π₁Env ∘F extendRelEnv-ρ×As αs) (ρ , Rs))
               --               (Functor.F₀ (extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k)) (ρ , Rs))
               → SetEnvMorph ((Functor.F₀ π₁Env ρ) [ αs :fvs= vmap ConstF (vecfst Rs) ]Set)
                             (Functor.F₀ π₁Env (ρ [ αs :fvs= vmap ConstRT Rs ]Rel ))
π₁Env-ρ×As-η' [] ρ [] = idSetEnv
π₁Env-ρ×As-η' (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) = SetEnvM[ ≡.refl , fvm ]  
    where -- rec = π₁Env-ρ×As-η' αs ρ Rs 
          fvm : {j : ℕ } (φ : FVar j) → [Sets^ j ,Sets] [
                    SetEnv.fv ((Functor.F₀ π₁Env ρ) [ α ∷ αs :fvs= vmap ConstF (vecfst (R ∷ Rs)) ]Set) φ 
                  , SetEnv.fv (Functor.F₀ π₁Env (ρ [ α ∷ αs :fvs= ConstRT R ∷ vmap ConstRT Rs ]Rel)) φ
                    ]

          fvm φ@(p ^F j) with eqNat z j | a ≟ p
          ... | yes ≡.refl | yes ≡.refl = idnat
          -- otherwise make recursive call  to π₁Env-ρ×As-η' 
          ... | yes ≡.refl | no _ = SetEnvMorph.fv (π₁Env-ρ×As-η' αs ρ Rs) φ
          ... | no _  | _  = SetEnvMorph.fv (π₁Env-ρ×As-η' αs ρ Rs)  φ





π₁RT-π₁Env : ∀ {k : ℕ} (φ : FVar k) {ρ ρ' : RelEnv} (f : RelEnvMorph ρ ρ')
        → [Sets^ k ,Sets] [ Functor.F₁ π₁RT (RelEnvMorph.fv f φ)
                ≈  SetEnvMorph.fv (Functor.F₁ π₁Env f) φ ]
π₁RT-π₁Env φ RelEnvM[ ≡.refl , _ ] = ≡.refl 


π₁RT-π₁Env-commute : ∀ {k : ℕ} (φ : FVar k) {ρ ρ' : RelEnv} (f : RelEnvMorph ρ ρ')
        → [Sets^ k ,Sets] [ Functor.F₁ π₁RT (RelEnvMorph.fv f φ)
                ≈  SetEnvMorph.fv (Functor.F₁ π₁Env f) φ ]
π₁RT-π₁Env-commute φ = (NaturalTransformation.commute (NI.NaturalIsomorphism.F⇒G (ApplyFV-EnvFunc-≃ π₁RT φ)))




-- define π₁Env-ρ×As-commute etc. 
-- further below we generalize this so we don't need a copy for π₁ and for π₂ 

Nat-refl⟩∘⟨_ : ∀ {k : ℕ} {F G H : Functor (Sets^ k) Sets} {η : NaturalTransformation G H} {δ δ' : NaturalTransformation F G} 
       → [Sets^ k ,Sets] [ δ ≈ δ' ]
       → [Sets^ k ,Sets] [ η ∘v δ ≈ η ∘v δ' ] 
Nat-refl⟩∘⟨_ {η = η} {δ} {δ'} δ≈δ' {Xs} {x} = ≡.cong (NaturalTransformation.η η Xs) δ≈δ'

π₁Env-ρ×As-commute : ∀ {k} (αs : Vec (FVar 0) k) {ρ ρ' : RelEnv} (f : RelEnvMorph ρ ρ')
                     → {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ] ) 
                     →
                     SetEnvCat [
                        π₁Env-ρ×As-η αs ρ' Ss
                        ∘SetEnv (Functor.F₁ (π₁Env ∘F extendRelEnv-ρ×As αs) (f , ms))
                      ≈ 
                        (Functor.F₁ (extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k)) (f , ms))
                        ∘SetEnv π₁Env-ρ×As-η αs ρ Rs 
                     ] 
π₁Env-ρ×As-commute [] f@(RelEnvM[ ≡.refl , fvm ]) {[]} {[]} ms = ≡.refl
π₁Env-ρ×As-commute {k = suc k} (α@(a ^F z) ∷ αs) {ρ} {ρ'} f@(RelEnvM[ ≡.refl , fvm ]) {R ∷ Rs} {S ∷ Ss} (m , ms) {j} {φ@(p ^F j)} {X} {x} with eqNat z j | a ≟ p 
... | yes ≡.refl | yes ≡.refl = ≡.refl
-- theres no way this definition is right -vvvvv
... | yes ≡.refl | no _ = lem
  where module Setsj = Category [Sets^ j ,Sets]
        open Setsj.HomReasoning

        help : ∀ η → [Sets^ j ,Sets] [ 
                 η ∘v Functor.F₁ π₁RT (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
              ≈  η ∘v SetEnvMorph.fv (Functor.F₁ π₁Env (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) φ
                        ]
        -- should be able to use refl⟩∘⟨_ from HomReasoning for this, but for some reason it won't compute the implicit arguments 
        help η {Xs} {x} = ≡.cong (NaturalTransformation.η η Xs) (π₁RT-π₁Env-commute φ (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) 
        
        lem : [Sets^ j ,Sets] [
            SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v RTMorph.d1 (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
            ≈ SetEnvMorph.fv (Functor.F₁ (extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k)) (f , ms)) φ ∘v SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ Rs) φ ]
        lem = begin
                        SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v RTMorph.d1 (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
                        --  ≈⟨ ≡.refl ⟩
                        -- SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v Functor.F₁ π₁RT (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
                         ≈⟨ help (SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ) ⟩ 
                        -- SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v SetEnvMorph.fv (Functor.F₁ π₁Env (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) φ
                        --  ≈⟨ ≡.refl ⟩
                        -- SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss ∘SetEnv (Functor.F₁ π₁Env (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)))) φ
                        --  ≈⟨ ≡.refl ⟩
                        SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss ∘SetEnv (Functor.F₁ (π₁Env ∘F extendRelEnv-ρ×As αs) (f , ms))) φ
                         ≈⟨ π₁Env-ρ×As-commute αs f ms ⟩ 
                        SetEnvMorph.fv ((Functor.F₁ (extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k)) (f , ms)) ∘SetEnv π₁Env-ρ×As-η αs ρ Rs) φ
                         ∎     


... | no _  | _  =  lem
  where module Setsj = Category [Sets^ j ,Sets]
        open Setsj.HomReasoning

        help : ∀ η → [Sets^ j ,Sets] [ 
                 η ∘v Functor.F₁ π₁RT (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
              ≈  η ∘v SetEnvMorph.fv (Functor.F₁ π₁Env (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) φ
                        ]
        -- should be able to use refl⟩∘⟨_ from HomReasoning for this, but for some reason it won't compute the implicit arguments 
        help η {Xs} {x} = ≡.cong (NaturalTransformation.η η Xs) (π₁RT-π₁Env-commute φ (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) 
        
        lem : [Sets^ j ,Sets] [
            SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v RTMorph.d1 (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
            ≈ SetEnvMorph.fv (Functor.F₁ (extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k)) (f , ms)) φ ∘v SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ Rs) φ ]
        lem = begin
                        SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v RTMorph.d1 (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
                        --  ≈⟨ ≡.refl ⟩
                        -- SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v Functor.F₁ π₁RT (RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)) φ)
                         ≈⟨ help (SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ) ⟩ 
                        -- SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss) φ ∘v SetEnvMorph.fv (Functor.F₁ π₁Env (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) φ
                        --  ≈⟨ ≡.refl ⟩
                        -- SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss ∘SetEnv (Functor.F₁ π₁Env (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)))) φ
                        --  ≈⟨ ≡.refl ⟩
                        SetEnvMorph.fv (π₁Env-ρ×As-η αs ρ' Ss ∘SetEnv (Functor.F₁ (π₁Env ∘F extendRelEnv-ρ×As αs) (f , ms))) φ
                         ≈⟨ π₁Env-ρ×As-commute αs f ms ⟩ 
                        SetEnvMorph.fv ((Functor.F₁ (extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k)) (f , ms)) ∘SetEnv π₁Env-ρ×As-η αs ρ Rs) φ
                         ∎     


π₁Env-ρ×As-isoˡ : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv)
                  → (Rs : Category.Obj (R^ k))
                  → SetEnvCat [ 
                    (π₁Env-ρ×As-η' αs ρ Rs) ∘SetEnv (π₁Env-ρ×As-η αs ρ Rs)
                    ≈ idSetEnv ] 
π₁Env-ρ×As-isoˡ [] ρ [] = ≡.refl
π₁Env-ρ×As-isoˡ (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) {j} {φ@(p ^F j)} with eqNat z j | a ≟ p
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | yes ≡.refl | no _ = π₁Env-ρ×As-isoˡ αs ρ Rs
... | no _  | _  = π₁Env-ρ×As-isoˡ αs ρ Rs



π₁Env-ρ×As-isoʳ : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv)
                  → (Rs : Category.Obj (R^ k))
                  → SetEnvCat [ 
                    (π₁Env-ρ×As-η αs ρ Rs) ∘SetEnv (π₁Env-ρ×As-η' αs ρ Rs)
                    ≈ idSetEnv ] 
π₁Env-ρ×As-isoʳ [] ρ [] = ≡.refl
π₁Env-ρ×As-isoʳ (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) {j} {φ@(p ^F j)} with eqNat z j | a ≟ p
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | yes ≡.refl | no _ = π₁Env-ρ×As-isoʳ αs ρ Rs
... | no _  | _  = π₁Env-ρ×As-isoʳ  αs ρ Rs


π₁Env-extendSetEnv-ρ×As-≃ : ∀ {k : ℕ} (αs : Vec (FVar 0) k) 
      → π₁Env ∘F extendRelEnv-ρ×As αs 
      ≃ extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k) 
π₁Env-extendSetEnv-ρ×As-≃ αs =
    niHelper (record { η = λ { (ρ , Rs) → π₁Env-ρ×As-η αs ρ Rs }
                     ; η⁻¹ =  λ { (ρ , Rs) → π₁Env-ρ×As-η' αs ρ Rs }
                     ; commute = λ { (f , ms) → π₁Env-ρ×As-commute αs f ms  } 
                     ; iso = λ { (ρ , Rs) → record { isoˡ = π₁Env-ρ×As-isoˡ αs ρ Rs ; isoʳ = π₁Env-ρ×As-isoʳ αs ρ Rs } } }) 
-}



-- [ ] - TODO - find a better way to do this... maybe the answer is to just do the π₁ and π₂ cases
-- individually to make the proofs simpler / faster 
module _ (F : ∀ {j} → Functor (RTCat j) [Sets^ j ,Sets])
         (G : Functor Rels Sets)
         -- (Const-≃ : ∀ (R : RelObj) → (Functor.F₀ F (ConstRT R)) ≃ (ConstF (Functor.F₀ G R)))
         (Const-≃ : (F {0} ∘F Rels⇒RT0 ) ≃ Sets→0Functors ∘F G )
         where 
    open VecFunc

    abstract 

        FConstRT⇒ConstGR : ∀ (R : RelObj) → NaturalTransformation (Functor.F₀ F (ConstRT R)) (ConstF (Functor.F₀ G R))
        FConstRT⇒ConstGR R = NaturalTransformation.η (NI.NaturalIsomorphism.F⇒G Const-≃) R 

        FConstRT⇐ConstGR : ∀ (R : RelObj) → NaturalTransformation (ConstF (Functor.F₀ G R)) (Functor.F₀ F (ConstRT R))
        FConstRT⇐ConstGR R = NaturalTransformation.η (NI.NaturalIsomorphism.F⇐G Const-≃) R  


        Const-commute : ∀ {R S : RelObj} (m : RelMorph R S)
                        → [Sets^ 0 ,Sets] [
                                (FConstRT⇒ConstGR S) ∘v (Functor.F₁ (F ∘F Rels⇒RT0) m)
                                ≈ 
                                Functor.F₁ (Sets→0Functors ∘F G) m ∘v (FConstRT⇒ConstGR R) ] 
        Const-commute m = NaturalTransformation.commute (NI.NaturalIsomorphism.F⇒G Const-≃) m 


        FEnv-ρ×As-η : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv) (Rs : Vec RelObj k) 
                    → SetEnvCat [
                    Functor.F₀ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (ρ , Rs) 
                    , Functor.F₀ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) (ρ , Rs)
                    ]
        FEnv-ρ×As-η [] ρ [] = idSetEnv 
        FEnv-ρ×As-η {k = suc k} (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) = SetEnvM[ ≡.refl , fvm  ] 
            where fvm : ∀ {j} (φ : FVar j) → [Sets^ j ,Sets] [
                            SetEnv.fv (Functor.F₀ (EnvFunc-RT F ∘F extendRelEnv-ρ×As ((a ^F 0) ∷ αs)) (ρ , R ∷ Rs)) φ
                            , SetEnv.fv (Functor.F₀ (extendSetEnv-ρ×As ((a ^F 0) ∷ αs) ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G (suc k))) (ρ , R ∷ Rs)) φ
                            ]

                  fvm φ@(p ^F j) with eqNat z j | a ≟ p
                  ... | yes ≡.refl | yes ≡.refl = FConstRT⇒ConstGR R 
                  ... | yes ≡.refl | no _ = SetEnvMorph.fv (FEnv-ρ×As-η αs ρ Rs) φ
                  ... | no _  | _  =  SetEnvMorph.fv (FEnv-ρ×As-η αs ρ Rs) φ


        FEnv-ρ×As-η' : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv) (Rs : Vec RelObj k) 
                    → SetEnvCat [
                    Functor.F₀ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) (ρ , Rs)
                    , Functor.F₀ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (ρ , Rs) 
                    ]
        FEnv-ρ×As-η' [] ρ [] = idSetEnv 
        FEnv-ρ×As-η' {k = suc k} (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) = SetEnvM[ ≡.refl , fvm  ] 
            where fvm : ∀ {j} (φ : FVar j) → [Sets^ j ,Sets] [
                            SetEnv.fv (Functor.F₀ (extendSetEnv-ρ×As ((a ^F 0) ∷ αs) ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G (suc k))) (ρ , R ∷ Rs)) φ
                            , SetEnv.fv (Functor.F₀ (EnvFunc-RT F ∘F extendRelEnv-ρ×As ((a ^F 0) ∷ αs)) (ρ , R ∷ Rs)) φ
                            ]

                  fvm φ@(p ^F j) with eqNat z j | a ≟ p
                  ... | yes ≡.refl | yes ≡.refl = FConstRT⇐ConstGR R 
                  ... | yes ≡.refl | no _ = SetEnvMorph.fv (FEnv-ρ×As-η' αs ρ Rs) φ
                  ... | no _  | _  =  SetEnvMorph.fv (FEnv-ρ×As-η' αs ρ Rs) φ



                            -- (SetEnvCat Category.≈
                            -- (SetEnvCat Category.∘ (λ { (ρ , Rs) → FEnv-ρ×As-η αs ρ Rs }) Y)
                            -- (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) f))
                            -- ((SetEnvCat Category.∘
                            -- Functor.F₁ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) f)
                            -- ((λ { (ρ , Rs) → FEnv-ρ×As-η αs ρ Rs }) X))


                -- Goal: Functor.F₁ F (RelEnvMorph.fv m' φ) Setsj.≈
                --     SetEnvMorph.fv (EnvFunc-RT-map F m') φ 

        F-resp-fv : ∀ {k} (φ : FVar k) {ρ ρ' : RelEnv} (m : RelEnvMorph ρ ρ')
            → [Sets^ k ,Sets] [ Functor.F₁ F (RelEnvMorph.fv m φ) ≈ SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F) m) φ ]
        F-resp-fv φ RelEnvM[ ≡.refl , fvm ] = ≡.refl

        FEnv-ρ×As-commute : ∀ {k} (αs : Vec (FVar 0) k) {ρ ρ' : RelEnv} (f : RelEnvMorph ρ ρ')
                            → {Rs Ss : Vec RelObj k} (ms : (Rels^ k) [ Rs , Ss ]) 
                            → SetEnvCat [
                            FEnv-ρ×As-η αs ρ' Ss
                            ∘SetEnv  (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms))
                            ≈
                            Functor.F₁ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) (f , ms)
                            ∘SetEnv FEnv-ρ×As-η αs ρ Rs 
                            ]
        FEnv-ρ×As-commute [] f {[]} {[]} _ = ≡.refl 
        FEnv-ρ×As-commute {suc k} (α@(a ^F z) ∷ αs) {ρ} {ρ'} f@(RelEnvM[ ≡.refl , fvm ]) {R ∷ Rs} {S ∷ Ss} (m , ms) {j} {φ@(p ^F j)} {Xs} {x} with eqNat z j | a ≟ p | Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms)  | ≡.inspect (Functor.F₁ (extendRelEnv-ρ×As αs)) (f , ms)
        ... | yes ≡.refl | yes ≡.refl | _ | _ = Const-commute m 
        ... | yes ≡.refl | no _ | m'@(RelEnvM[ e' ,  fvmm' ])  | ≡.[ ≡.refl ] = goal
              where rec : SetEnvCat [ FEnv-ρ×As-η αs ρ' Ss ∘SetEnv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms))
                                            ≈ Functor.F₁ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) (f , ms) ∘SetEnv FEnv-ρ×As-η αs ρ Rs ] 
                    rec = FEnv-ρ×As-commute αs f ms 

                    ff = RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))

                    fvmm'' = RTM[ idnat ∘v RTMorph.d1 (fvmm' φ) , idnat ∘v RTMorph.d2 (fvmm' φ) , RTMorph.d-preserves (fvmm' φ) ]

                    lhs' = Functor.F₁ F fvmm'' 

                    RTM-≈ : (RTCat j) [ fvmm' φ ≈ fvmm'' ] 
                    RTM-≈ = ≡.refl , ≡.refl 

                    lhs = SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ ∘v lhs' 
                    rhs = SetEnvMorph.fv (Functor.F₁ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) (f , ms) ∘SetEnv FEnv-ρ×As-η αs ρ Rs) φ

                    module SEC = Category SetEnvCat 

                    module Setsj = Category [Sets^ j ,Sets]
                    open Setsj.HomReasoning

                    subsubgoal : [Sets^ j ,Sets] [ Functor.F₁ F fvmm'' ≈ SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ ]
                    subsubgoal =  begin (Functor.F₁ F fvmm'')
                                        ≈⟨  Functor.F-resp-≈ F RTM-≈ ⟩
                                        Functor.F₁ F (fvmm' φ)
                                        ≈⟨ F-resp-fv φ m' ⟩
                                        SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F) m') φ  
                                        ≈⟨ ≡.refl ⟩ -- this line comes from proof given by inspect 
                                        SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F) (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) φ  
                                        ≈⟨ ≡.refl ⟩
                                        SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ  ∎   

                    subgoal : [Sets^ j ,Sets] [ lhs ≈ SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ ∘v  SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ ]
                    subgoal {Xs} {x} =  ≡.cong (NaturalTransformation.η (SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ) Xs) subsubgoal  

                    goal : [Sets^ j ,Sets] [ lhs ≈ rhs ] 
                    goal = begin lhs
                                ≈⟨ subgoal ⟩
                                SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ ∘v  SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ
                                ≈⟨ rec ⟩
                                rhs  ∎ 

        -- we must match on fvmm' or else goal doesn't typecheck.
        -- same exact case as case directly above... 
        ... | no _  | _  | m'@(RelEnvM[ e' , fvmm' ]) | ≡.[ ≡.refl ] = goal
          where rec : SetEnvCat [ FEnv-ρ×As-η αs ρ' Ss ∘SetEnv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms))
                                        ≈ Functor.F₁ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) (f , ms) ∘SetEnv FEnv-ρ×As-η αs ρ Rs ] 
                rec = FEnv-ρ×As-commute αs f ms 

                ff = RelEnvMorph.fv (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))

                fvmm'' = RTM[ idnat ∘v RTMorph.d1 (fvmm' φ) , idnat ∘v RTMorph.d2 (fvmm' φ) , RTMorph.d-preserves (fvmm' φ) ]

                lhs' = Functor.F₁ F fvmm'' 

                RTM-≈ : (RTCat j) [ fvmm' φ ≈ fvmm'' ] 
                RTM-≈ = ≡.refl , ≡.refl 

                lhs = SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ ∘v lhs' 
                rhs = SetEnvMorph.fv (Functor.F₁ (extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ Func^ Rels Sets G k)) (f , ms) ∘SetEnv FEnv-ρ×As-η αs ρ Rs) φ

                module SEC = Category SetEnvCat 

                module Setsj = Category [Sets^ j ,Sets]
                open Setsj.HomReasoning

                subsubgoal : [Sets^ j ,Sets] [ Functor.F₁ F fvmm'' ≈ SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ ]
                subsubgoal =  begin (Functor.F₁ F fvmm'')
                                    ≈⟨  Functor.F-resp-≈ F RTM-≈ ⟩
                                    Functor.F₁ F (fvmm' φ)
                                    ≈⟨ F-resp-fv φ m' ⟩
                                    SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F) m') φ  
                                    ≈⟨ ≡.refl ⟩ -- this line comes from proof given by inspect 
                                    SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F) (Functor.F₁ (extendRelEnv-ρ×As αs) (f , ms))) φ  
                                    ≈⟨ ≡.refl ⟩
                                    SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ  ∎   

                subgoal : [Sets^ j ,Sets] [ lhs ≈ SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ ∘v  SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ ]
                subgoal {Xs} {x} =  ≡.cong (NaturalTransformation.η (SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ) Xs) subsubgoal  

                goal : [Sets^ j ,Sets] [ lhs ≈ rhs ] 
                goal = begin lhs
                            ≈⟨ subgoal ⟩
                            SetEnvMorph.fv (FEnv-ρ×As-η αs ρ' Ss) φ ∘v  SetEnvMorph.fv (Functor.F₁ (EnvFunc-RT F ∘F extendRelEnv-ρ×As αs) (f , ms)) φ
                            ≈⟨ rec ⟩
                            rhs ∎ 




        open import Categories.Morphism
        FEnv-ρ×As-isoˡ : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv) (Rs : Vec RelObj k)
                        → SetEnvCat [ 
                            FEnv-ρ×As-η' αs ρ Rs ∘SetEnv FEnv-ρ×As-η αs ρ Rs 
                            ≈ idSetEnv ] 
        FEnv-ρ×As-isoˡ [] ρ [] = ≡.refl 
        FEnv-ρ×As-isoˡ (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) {j} {φ@(p ^F j)} with eqNat z j | a ≟ p
        ... | yes ≡.refl | yes ≡.refl = Iso.isoˡ (NI.NaturalIsomorphism.iso Const-≃ R)
        ... | yes ≡.refl | no _ = FEnv-ρ×As-isoˡ αs ρ Rs 
        ... | no _       | _    = FEnv-ρ×As-isoˡ αs ρ Rs   

        FEnv-ρ×As-isoʳ : ∀ {k} (αs : Vec (FVar 0) k) (ρ : RelEnv) (Rs : Vec RelObj k)
                        → SetEnvCat [ 
                            FEnv-ρ×As-η αs ρ Rs ∘SetEnv FEnv-ρ×As-η' αs ρ Rs 
                            ≈ idSetEnv ] 
        FEnv-ρ×As-isoʳ [] ρ [] = ≡.refl 
        FEnv-ρ×As-isoʳ (α@(a ^F z) ∷ αs) ρ (R ∷ Rs) {j} {φ@(p ^F j)} with eqNat z j | a ≟ p
        ... | yes ≡.refl | yes ≡.refl = Iso.isoʳ (NI.NaturalIsomorphism.iso Const-≃ R) 
        ... | yes ≡.refl | no _ = FEnv-ρ×As-isoʳ αs ρ Rs 
        ... | no _       | _    = FEnv-ρ×As-isoʳ αs ρ Rs   


        FEnv-extendEnv-ρ×As-≃ : ∀ {k : ℕ} (αs : Vec (FVar 0) k) 
            → EnvFunc-RT F ∘F extendRelEnv-ρ×As αs 
            ≃ extendSetEnv-ρ×As αs ∘F (EnvFunc-RT F ⁂ (Func^ Rels Sets G k))
        FEnv-extendEnv-ρ×As-≃ αs =
            niHelper (record { η = λ { (ρ , Rs) → FEnv-ρ×As-η αs ρ Rs  }
                            ; η⁻¹ = λ { (ρ , Rs) → FEnv-ρ×As-η' αs ρ Rs } 
                            ; commute = λ { {ρ , Rs} {ρ' , Ss} (f , ms) →  FEnv-ρ×As-commute αs f ms } 
                            ; iso = λ { (ρ , Rs) → record { isoˡ = FEnv-ρ×As-isoˡ αs ρ Rs
                                                            ; isoʳ = FEnv-ρ×As-isoʳ αs ρ Rs } } }) 





-- even after making these definitions abstract, 
-- their application in other files is still type-checking slowly 
abstract 

    π₁RT-π₁Rels-≃ : π₁RT ∘F Rels⇒RT0 ≃ Sets→0Functors ∘F π₁Rels 
    π₁RT-π₁Rels-≃ = niHelper (record { η = λ R → idnat ; η⁻¹ = λ R → idnat ; commute = λ f → ≡.refl ; iso = λ R → record { isoˡ = ≡.refl ; isoʳ = ≡.refl } })


    π₁Env-extendSetEnv-ρ×As-≃ : ∀ {k : ℕ} (αs : Vec (FVar 0) k) 
        → π₁Env ∘F extendRelEnv-ρ×As αs 
        ≃ extendSetEnv-ρ×As αs ∘F (π₁Env ⁂ π₁Vec k) 
    π₁Env-extendSetEnv-ρ×As-≃ αs = FEnv-extendEnv-ρ×As-≃ π₁RT π₁Rels π₁RT-π₁Rels-≃ αs 


    π₂RT-π₂Rels-≃ : π₂RT ∘F Rels⇒RT0 ≃ Sets→0Functors ∘F π₂Rels 
    π₂RT-π₂Rels-≃ =
        niHelper (record { η = λ R → idnat ; η⁻¹ = λ R → idnat ; commute = λ f → ≡.refl ; iso = λ R → record { isoˡ = ≡.refl ; isoʳ = ≡.refl } })



    π₂Env-extendSetEnv-ρ×As-≃ : ∀ {k : ℕ} (αs : Vec (FVar 0) k) 
        → π₂Env ∘F extendRelEnv-ρ×As αs 
        ≃ extendSetEnv-ρ×As αs ∘F (π₂Env ⁂ π₂Vec k) 
    π₂Env-extendSetEnv-ρ×As-≃ αs = FEnv-extendEnv-ρ×As-≃ π₂RT π₂Rels π₂RT-π₂Rels-≃ αs 


    -- proofs about φ extension 

    -- why does this one (and same for π₂) take so long to typecheck? 
    π₁Env-extendSetEnv2-≃ : ∀ {k : ℕ} (φ : FVar k) 
        → π₁Env ∘F extendRelEnv2 φ
        ≃ extendSetEnv2 φ ∘F (π₁Env ⁂ π₁RT) 
    π₁Env-extendSetEnv2-≃ = genlem π₁RT 

    π₂Env-extendSetEnv2-≃ : ∀ {k : ℕ} (φ : FVar k) 
        → π₂Env ∘F extendRelEnv2 φ
        ≃ extendSetEnv2 φ ∘F (π₂Env ⁂ π₂RT) 
    π₂Env-extendSetEnv2-≃ = genlem π₂RT





{-
TEnvFibred : ∀ {k : ℕ} (αs : Vec (FVar 0) k) (φ : FVar k)
             → (ρ : RelEnv) (Rt : RTObj k) (Rs : Vec RelObj k)
             → Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs))
             ≡ Functor.F₀ (extendTSetEnv φ αs) ((Functor.F₀ π₁Env ρ , RTObj.F1 Rt) , (vecfst Rs))
TEnvFibred αs φ ρ Rt Rs =
  let p : Functor.F₀ π₁Env ρ ≡ SetEnv[ (λ x → RTObj.F1 (RelEnv.tc ρ x)) , (λ x → RTObj.F1 (RelEnv.fv ρ x)) ]
      p = ≡.refl

      lhs-tc = (λ {j} (ψ : TCVar j) → RTObj.F1 (RelEnv.tc ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel) ψ))
      lhs-fv = (λ {j} (ψ : FVar  j) → RTObj.F1 (RelEnv.fv ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel) ψ))
      -- rhs-tc = (λ {j} (ψ : TCVar j) → 
      -- rhs = ((Functor.F₀ π₁Env ρ) [ φ :fv= RTObj.F1 Rt ]Set) [ αs :fvs= to0Functors (vecfst Rs) ]Set
      rhs = ((Functor.F₀ π₁Env ρ) [ φ :fv= RTObj.F1 Rt ]Set) [ αs :fvs= to0Functors (vecfst Rs) ]Set

--       rhs-tc = (λ {k} → SetEnv.tc rhs {k})
      rhs-tc = (λ {j} (ψ : TCVar j) → SetEnv.tc (((Functor.F₀ π₁Env ρ) [ φ :fv= RTObj.F1 Rt ]Set) [ αs :fvs= to0Functors (vecfst Rs) ]Set) ψ)
      rhs-fv = (λ {j} (ψ : FVar  j) → SetEnv.fv (((Functor.F₀ π₁Env ρ) [ φ :fv= RTObj.F1 Rt ]Set) [ αs :fvs= to0Functors (vecfst Rs) ]Set) ψ)


      tc-goal : (λ {j} → lhs-tc {j}) ≡ rhs-tc
      tc-goal = {!!} 

      fv-goal : (λ {j} → lhs-fv {j}) ≡ rhs-fv
      fv-goal = {!!} 

      tc-goal-ext : ∀ {j} (ψ : TCVar j)
                    → RTObj.F1 (RelEnv.tc ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel) ψ)
                    ≡ SetEnv.tc (((Functor.F₀ π₁Env ρ) [ φ :fv= RTObj.F1 Rt ]Set) [ αs :fvs= to0Functors (vecfst Rs) ]Set) ψ
      tc-goal-ext ψ = {!   (extendTSetEnv φ αs ∘F ((π₁Env ⁂ π₁RT) ⁂ π₁Vec k))   !} 

      goal : SetEnv[ lhs-tc , lhs-fv ] ≡ rhs 
      goal = ≡.cong₂ SetEnv[_,_] tc-goal fv-goal    

    in goal   




TEnvfvm1 : ∀ {k} (αs : Vec (FVar 0) k) (φ : FVar k) ρ
             (Rt : RTObj k) (Rs : Vec RelObj k) {j} (ψ : FVar j) →
           [Sets^ j ,Sets] [
           SetEnv.fv
           (Functor.F₀ (π₁Env ∘F extendTRelEnv φ αs) ((ρ , Rt) , Rs)) ψ
           ,
           SetEnv.fv
           (Functor.F₀ (extendTSetEnv φ αs ∘F ((π₁Env ⁂ π₁RT) ⁂ π₁Vec k))
            ((ρ , Rt) , Rs)) ψ
           ]
TEnvfvm1 αs φ ρ Rt Rs {j} ψ = {!!}


TEnv1-comp : ∀ {k} (αs : Vec (FVar 0) k) (φ : FVar k) (ρ : RelEnv)
               (Rt : RTObj k) (Rs : Vec RelObj k)
               → SetEnvCat [
                Functor.F₀ (π₁Env ∘F extendTRelEnv φ αs) ((ρ , Rt) , Rs)
              , Functor.F₀ (extendTSetEnv φ αs ∘F ((π₁Env ⁂ π₁RT) ⁂ π₁Vec k)) ((ρ , Rt) , Rs) ]
TEnv1-comp αs φ ρ Rt Rs = SetEnvM[ {!!} , {!TEnvfvm1 αs φ ρ Rt Rs!} ]  


TEnv1 : ∀ {k : ℕ} (αs : Vec (FVar 0) k) (φ : FVar k)
        → (ρ : RelEnv) (Rt : RTObj k) (Rs : Vec RelObj k)
        → NaturalTransformation (π₁Env ∘F extendTRelEnv φ αs) (extendTSetEnv φ αs ∘F ((π₁Env ⁂ π₁RT) ⁂ (π₁Vec k)))
TEnv1 αs φ ρ Rt Rs = record { η = {!TEnv1-comp αs φ ρ Rt Rs !} ; commute = {!!} ; sym-commute = {!!} } 


{-
{!
    let p : Functor.F₀ π₁Env ρ ≡ ? -- SetEnv[ (λ x → RTObj.F1 (RelEnv.tc ρ x)) , (λ x → RTObj.F1 (RelEnv.fv ρ x)) ]
        p = ? 
    in ? 

!} 
-}


{-
      ([Sets^_,Sets] RTEnvironments.Core.[
       SetFunctors-Terminal :fvs=

       ([Sets^_,Sets] RTEnvironments.Core.[ SetFunctors-Terminal
         :fv= RelEnv[ (λ x → RTObj.F1 (RelEnv.tc ρ x)) , (λ x → RTObj.F1 (RelEnv.fv ρ x)) ]])

       φ (RTObj.F1 Rt)
       ])
      αs (vmap ConstF (vmap fst Rs))
      -}

{-
Goal: RelEnv[
      (λ x → RTObj.F1 (RelEnv.tc ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel) x))
      ,
      (λ x → RTObj.F1 (RelEnv.fv ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel) x))]
      ≡
      ((λ k₁ →
          Categories.Category.Construction.Functors.Functors
          (VecCat.Cat^ (Setsl Agda.Primitive.lzero) k₁)
          (Setsl Agda.Primitive.lzero))
       RTEnvironments.Core.[ SetFunctors-Terminal :fvs=
       ((λ k₁ →
           Categories.Category.Construction.Functors.Functors
           (VecCat.Cat^ (Setsl Agda.Primitive.lzero) k₁)
           (Setsl Agda.Primitive.lzero))
        RTEnvironments.Core.[ SetFunctors-Terminal :fv=
        RelEnv[ (λ x → RTObj.F1 (RelEnv.tc ρ x)) ,
        (λ x → RTObj.F1 (RelEnv.fv ρ x)) ]
        ])
       φ (RTObj.F1 Rt)
       ])
      αs (vmap ConstF (vmap fst Rs))

-}

-}

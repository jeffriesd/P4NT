open import Syntax.NestedTypeSyntax
open _≀_⊢_ -- import names of data constructors
open TypeExpr
open FVar
open _∋_

-- open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (if_then_else_; true; false)
open import Categories.Category
open import Categories.Category.Product using (Product ; _※_  ; πˡ ; πʳ)
open import Categories.Functor using (Functor ; _∘F_) renaming (id to idF)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; _∘ₕ_  to _∘h_ ; id to idnat)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
-- open import Categories.Morphism.Reasoning Rels as MR

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
-- open import Data.Unit using (⊤)
-- open import Data.Empty
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≡_)
-- open ≡.≡-Reasoning
open import Data.Sum hiding ([_,_])
-- open import Data.Sum.Properties using (inj₂-injective)

open import SetCats
open import RelSem.RelCats
open RelObj
open RelMorph

open import Data.Product renaming (_×_ to _×'_)
-- open import Utils
open import RelEnvironments.Core as RE
open import SetEnvironments.Core
open import SetEnvironments.EnvironmentExtension
open import RelEnvironments.EnvironmentExtension
-- open import HFixFunctorLib
open import CatUtils
-- open import SetSem.NestedSetSemantics
-- open import RelSem.RelTypeSemantics using (RelSem ; RelSemVec ; MuRelSem ; module NormalTRel)
-- open NormalT renaming (TRel to TSet)

open import TypeSemantics.TypeSemantics

-- open NormalTRel

open import Categories.Category.Product

open import Utils

module RelSem.Fibred where

-- ideas --
-- functors are of type : Functor (RTCat k) (Functors (Rels^ k) Sets)
-- can we define natural transformations for the uncurried functors?


open ≡.≡-Reasoning
h1-eq : ∀ {k} {Γ} {H} {φ : FVar k} {αs : Vec (FVar 0) k} → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H)
     → (ρ : RelEnv)
     → ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
     → Functor.F₀ (Functor.F₀ (postcomp-F (π₁Vec k) ∘F Functor.₀ (TSet ⊢H ∘F π₁Env) ρ ∘F π₁RT) Rt) Rs
     ≡ Functor.F₀ (Functor.F₀ (precomp-F π₁Rels ∘F Functor.₀ (TRel ⊢H) ρ) Rt) Rs
h1-eq {k} {φ = φ} {αs} ⊢H ρ Rt Rs = 
  begin
    Functor.F₀ (SetSem ⊢H)
      ((Functor.F₀ π₁Env ρ [ φ :fv= RTObj.F1 Rt ]Set) [ αs :fvs= vmap ConstF (vecfst Rs) ]Set) 
    ≡⟨ SetSem-ext-eq-envs (((Functor.F₀ π₁Env ρ [ φ :fv= RTObj.F1 Rt ]Set) [ αs :fvs= vmap ConstF (vecfst Rs) ]Set))
                          ((Functor.F₀ π₁Env ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel)))
                          ⊢H {!!} {!!} ⟩
    Functor.F₀ (SetSem ⊢H)
      (Functor.F₀ π₁Env ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel))
    ≡⟨ SetSem-over-1 ⊢H  ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel) ⟩
      fst
      (Functor.F₀ (RelSem ⊢H)
       ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= vmap ConstRT Rs ]Rel))
     ∎  

open import HetEquality.Core



open import HetEquality.Core
open import HetEquality.HetFunctors RelEnvCat -- using
import HetEquality.HetFunctors SetEnvCat as HetSetFunctors -- using
--   -- (module HetNatResp ; module HetFuncRespVec ; module HetNaturality-equal-maps ; module VecHetEquality)
open VecHetEquality

{-
postulate
    SetSemVec-over-eq-map  : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} → (⊢Fs : foreach (Γ ≀ Φ ⊢_) Fs)
                    → ∀ {ρ ρ' : RelEnv}
                    → (f : RelEnvMorph ρ ρ')
                    → pointwise-het-≈ (Functor.F₁ (SetSemVec ⊢Fs ∘F π₁Env) f) (Functor.F₁ (π₁Vec k ∘F RelSemVec ⊢Fs) f)
    SetSem-over-eq-map  : ∀ {Γ} {Φ} {F} → (⊢F : Γ ≀ Φ ⊢ F)
                    → ∀ {ρ ρ' : RelEnv}
                    → (f : RelEnvMorph ρ ρ')
                    → (Functor.F₁ (SetSem ⊢F) (Functor.F₁ π₁Env f))
                    het-≈ (mfst (Functor.F₁ (RelSem ⊢F) f))

-}



open VecCat (Sets) renaming (componentwise-Vec-≈ to _Vec-≈_)
open VecCat (Rels) renaming (idVec to idVecRels)

-- STOPPED HERE

SetSemVec-ext-eq-morph : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} (⊢Fs : foreach (Γ ≀ Φ ⊢_) Fs)
                    → (ρ ρ' : SetEnv) (f g : SetEnvMorph ρ ρ')
                    → (∀ {j} (φ : FVar j) → (SetEnvMorph.fv f φ) ≡ SetEnvMorph.fv g φ)
                    → (Functor.F₁ (SetSemVec ⊢Fs) f)
                    Vec-≈
                        (Functor.F₁ (SetSemVec ⊢Fs) g)
SetSemVec-ext-eq-morph ⊢Fs ρ ρ' f g p = Functor.F-resp-≈ (SetSemVec ⊢Fs)  (λ {k} {φ} {Xs} {x} →  ≡.subst (λ h → NaturalTransformation.η h Xs x ≡ NaturalTransformation.η (SetEnvMorph.fv g φ) Xs x) (≡.sym (p φ)) ≡.refl)

SetSem-ext-eq-morph : ∀ {Γ} {Φ} {F} (⊢F : Γ ≀ Φ ⊢ F)
                    → (ρ ρ' : SetEnv) (f g : SetEnvMorph ρ ρ')
                    → (∀ {j} (φ : FVar j) → (SetEnvMorph.fv f φ) ≡ SetEnvMorph.fv g φ)
                    → Functor.F₁ (SetSem ⊢F) f
                    ≡-ext
                        Functor.F₁ (SetSem ⊢F) g
SetSem-ext-eq-morph ⊢F ρ ρ' f g p = Functor.F-resp-≈ (SetSem ⊢F) (λ {k} {φ} {Xs} {x} →  ≡.subst (λ h → NaturalTransformation.η h Xs x ≡ NaturalTransformation.η (SetEnvMorph.fv g φ) Xs x) (≡.sym (p φ)) ≡.refl) 






import Relation.Binary.HeterogeneousEquality as Het 
open Het.≅-Reasoning renaming (begin_ to begin≅_ ; _∎ to _≅∎)


{-
Goal: Functor.F₁ (SetSem ⊢H)
      (RTEnvironments.EnvironmentExtension.extendfv-morph-vec αs
       (vmap ConstF (vmap fst Rs)) (vmap ConstF (vmap fst Rs))
       (SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.[ φ :fv= RTObj.F1 Rt ])
       (SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.[ φ :fv= RTObj.F1 St ])
       (RTEnvironments.EnvironmentExtension.extendmorph-η
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        φ (RTMorph.d1 m)
        RTEnvironments.Core.∘Env
        RTEnvironments.EnvironmentExtension.extendmorph-idF φ (RTObj.F1 Rt)
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.idEnv)
       (RTEnvironments.EnvironmentExtension.toRT0Vec-map
        (idVec (vmap fst Rs))))
      x
      ≅
      mfst
      (Functor.F₁ (RelSem ⊢H)
       (RelEnvironments.EnvironmentExtension.extendfv-morph-vec αs
        (vmap ConstRT Rs) (vmap ConstRT Rs) (ρ [ φ :fv= Rt ]Rel)
        (ρ [ φ :fv= St ]Rel)
        (RelEnvironments.EnvironmentExtension.extendmorph-η ρ φ m ∘RelEnv
         RelEnvironments.EnvironmentExtension.extendmorph-idF φ Rt ρ ρ
         idRelEnv)
        (RelEnvironments.EnvironmentExtension.toRT0Vec-map
         (VecCat.idVec Rels Rs))))
      y
-}

h1-eq-morph-nat : ∀ {k} {Γ} {H} {φ : FVar k} {αs : Vec (FVar 0) k} → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H)
     → (ρ : RelEnv)
     → ∀ (Rt St : RTObj k) (Rs : Vec RelObj k) (m : RTMorph Rt St) 
     → NaturalTransformation.η (Functor.F₁ (postcomp-F (π₁Vec k) ∘F Functor.₀ (TSet ⊢H ∘F π₁Env) ρ ∘F π₁RT) m) Rs
     het-≈ NaturalTransformation.η (Functor.F₁ (precomp-F π₁Rels ∘F Functor.₀ (TRel ⊢H) ρ) m) Rs
h1-eq-morph-nat {φ = φ} {αs} ⊢H ρ Rt St Rs m {x} {y} p = 
  let p1 : Functor.F₁ (SetSem ⊢H) (Functor.F₁ (extendTSetEnv φ αs) ((idSetEnv {Functor.F₀ π₁Env ρ}, (RTMorph.d1 m)) , (idVec (vecfst Rs))) )
           het-≈ 
           Functor.F₁ (SetSem ⊢H) (Functor.F₁ π₁Env ( (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , m) , idVecRels Rs))))
      p1 = {!!} 
      p2 : Functor.F₁ (SetSem ⊢H) (Functor.F₁ π₁Env ( (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , m) , idVecRels Rs))))
           het-≈ 
           mfst (Functor.F₁ (RelSem ⊢H) (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , m) , idVecRels Rs)))
           
      p2 = SetSem-over-eq-map ⊢H (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , m) , idVecRels Rs))  
   in het-≈-trans p1 p2 (SetSem-ext-eq-envs
                           (Functor.F₀ (extendTSetEnv φ αs)
                            ((Functor.F₀ π₁Env ρ , RTObj.F1 Rt) , vecfst Rs))
                           (Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs)))
                           ⊢H {!!} {!!}) p   

-- Goal: RTEnvironments.Core.EnvMorph
--       ((SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
--         (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
--         RTEnvironments.Core.[ φ :fv= RTObj.F1 Rt ])
--        RTEnvironments.Core.[ αs :fvs= vmap ConstF (vmap fst m) ])
-- 
--       ((SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
--         (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
--         RTEnvironments.Core.[ φ :fv= RTObj.F1 St ])
--        RTEnvironments.Core.[ αs :fvs= vmap ConstF (vmap fst m) ])



h1-eq-morph : ∀ {k} {Γ} {H} {φ : FVar k} {αs : Vec (FVar 0) k} → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H)
     → (ρ : RelEnv)
     → ∀ (Rt : RTObj k) (Rs Ss : Vec RelObj k) (ms : (Rels^ k) [ Rs , Ss ])
     → Functor.F₁ (Functor.F₀ (postcomp-F (π₁Vec k) ∘F Functor.₀ (TSet ⊢H ∘F π₁Env) ρ ∘F π₁RT) Rt) ms
     het-≈ Functor.F₁ (Functor.F₀ (precomp-F π₁Rels ∘F Functor.₀ (TRel ⊢H) ρ) Rt) ms
h1-eq-morph {k} {φ = φ} {αs} ⊢H ρ Rt Rs Ss ms p = {!!}

{- WORK IN PROGRESS
  let

      step' : Functor.F₁ (SetSem ⊢H) (Functor.F₁ (extendTSetEnv φ αs) ((idSetEnv {Functor.F₀ (π₁Env) ρ} , idnat {F = RTObj.F1 Rt}) , vecmfst ms))
            het-≈
              Functor.F₁ (SetSem ⊢H) (Functor.F₁ π₁Env (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , idRTMorph Rt) , ms)))
      step' = {!!}

      step : Functor.F₁ (SetSem ⊢H) (Functor.F₁ π₁Env (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , idRTMorph Rt) , ms)))
            het-≈
            mfst
            (Functor.F₁ (RelSem ⊢H) (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , idRTMorph Rt) , ms)))
      step = {!!}

      goal : Functor.F₁ (SetSem ⊢H) (Functor.F₁ (extendTSetEnv φ αs) ((idSetEnv {Functor.F₀ (π₁Env) ρ} , idnat {F = RTObj.F1 Rt}) , vecmfst ms))
           het-≈
            mfst
            (Functor.F₁ (RelSem ⊢H) (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv {ρ} , idRTMorph Rt) , ms)))
      goal = het-≈-trans step' step (SetSem-ext-eq-envs
                                        ( (Functor.F₀ (extendTSetEnv φ αs) (((Functor.F₀ π₁Env ρ) , (RTObj.F1 Rt)) , (vecfst Rs))))
                                        ( (Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs))))
                                        ⊢H {!!} {!!})


-- need to prove environments are extensionally equal
-- -- trying to prove this in RelEnvironments.EnvironmentExtension
-- Goal: Functor.F₀ (extendTSetEnv φ αs)
--       ((Functor.F₀ π₁Env ρ , RTObj.F1 Rt) , vecfst Rs)
--       SetEnvironments.Core.≡TC
--       Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs))
-- Goal: Functor.F₀ (extendTSetEnv φ αs)
--       ((Functor.F₀ π₁Env ρ , RTObj.F1 Rt) , vecfst Rs)
--       ≡FV-extSetEnv
--       Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs))
-- ————————————————————————————————————————————————————————————

    in goal p


-}



{-
Goal: Functor.F₀ (SetSem ⊢H)
      (Functor.F₀ (extendTSetEnv φ αs) (F₀ π₁Env ρ , vmap fst Rs))
      ≡
      Functor.F₀ (SetSem ⊢H)
      (Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs)))
       -}



{-

h1-eq-morph ⊢H ρ Rt Rs Ss ms p = {!!}
with extendTEnv2 abstract

Goal:
Functor.F₁ (SetSem ⊢H)
      (Functor.F₁ (extendTSetEnv2 φ αs)
       ((idSetEnv , idnat) ,
        vecfst ms))
      x
      ≅
      mfst
      (Functor.F₁ (RelSem ⊢H)
       (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv , idRTMorph Rt) , ms)))
      y


--
mfst (Functor.F₁ (RelSem ⊢H) ) y
≈
Functor.F₁ (SetSem ⊢F)
  (Functor.F₁ π₁Env (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv , idRTMorph Rt) , ms))) y
≈
Functor.F₁ (SetSem ⊢F)
  (Functor.F₁ π₁Env (Functor.F₁ (extendTRelEnv φ αs) ((idRelEnv , idRTMorph Rt) , ms))) y
-}



{-
goal has the form

Functor.F₁ (SetSem ⊢H) f
het-≈
mfst (Functor.F₁ (RelSem ⊢H) f')

maybe start by proving something about that?


Goal: Functor.F₁ (SetSem ⊢H)
      (RTEnvironments.EnvironmentExtension.extendfv-morph-vec αs
       (vmap ConstF (vmap fst Rs)) (vmap ConstF (vmap fst Ss))
       (SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.[ φ :fv= RTObj.F1 Rt ])
       (SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.[ φ :fv= RTObj.F1 Rt ])
       (RTEnvironments.EnvironmentExtension.extendmorph-η
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        φ idnat
        RTEnvironments.Core.∘Env
        RTEnvironments.EnvironmentExtension.extendmorph-idF φ (RTObj.F1 Rt)
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.idEnv)
       (RTEnvironments.EnvironmentExtension.toRT0Vec-map
        (VecFunc.Func^-map Rels Sets π₁Rels ms)))
      x
      ≅
      mfst
      (Functor.F₁ (RelSem ⊢H)
       (RelEnvironments.EnvironmentExtension.extendfv-morph-vec αs
        (vmap ConstRT Rs) (vmap ConstRT Ss) (ρ [ φ :fv= Rt ]Rel)
        (ρ [ φ :fv= Rt ]Rel)
        (RelEnvironments.EnvironmentExtension.extendmorph-η ρ φ
         (idRTMorph Rt)
         ∘RelEnv
         RelEnvironments.EnvironmentExtension.extendmorph-idF φ Rt ρ ρ
         idRelEnv)
        (RelEnvironments.EnvironmentExtension.toRT0Vec-map ms)))
      y
Goal: Functor.F₁ (SetSem ⊢H)
      (RTEnvironments.EnvironmentExtension.extendfv-morph-vec αs
       (vmap ConstF (vmap fst Rs)) (vmap ConstF (vmap fst Ss))
       (SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.[ φ :fv= RTObj.F1 Rt ])
       (SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.[ φ :fv= RTObj.F1 Rt ])
       (RTEnvironments.EnvironmentExtension.extendmorph-η
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        φ idnat
        RTEnvironments.Core.∘Env
        RTEnvironments.EnvironmentExtension.extendmorph-idF φ (RTObj.F1 Rt)
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        SetEnv[ (λ x₁ → RTObj.F1 (SetEnv.tc ρ x₁)) ,
        (λ x₁ → RTObj.F1 (SetEnv.fv ρ x₁)) ]
        RTEnvironments.Core.idEnv)
       (RTEnvironments.EnvironmentExtension.toRT0Vec-map
        (VecFunc.Func^-map Rels Sets π₁Rels ms)))
      x
      ≅
      mfst
      (Functor.F₁ (RelSem ⊢H)
       (RelEnvironments.EnvironmentExtension.extendfv-morph-vec αs
        (vmap ConstRT Rs) (vmap ConstRT Ss) (ρ [ φ :fv= Rt ]Rel)
        (ρ [ φ :fv= Rt ]Rel)
        (RelEnvironments.EnvironmentExtension.extendmorph-η ρ φ
         (idRTMorph Rt)
         ∘RelEnv
         RelEnvironments.EnvironmentExtension.extendmorph-idF φ Rt ρ ρ
         idRelEnv)
        (RelEnvironments.EnvironmentExtension.toRT0Vec-map ms)))
      y
      -}



-- need the following to define TEnvRT
h1 : ∀ {k} {Γ} {H} {φ : FVar k} {αs : Vec (FVar 0) k} → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H)
     → (ρ : RelEnv)
     -- functors are of type : Functor (RTCat k) (Functors (Rels^ k) Sets)
     → NaturalTransformation (postcomp-F (π₁Vec k) ∘F Functor.₀ (TSet ⊢H ∘F π₁Env) ρ ∘F π₁RT)
                                (precomp-F π₁Rels ∘F Functor.₀ (TRel ⊢H) ρ)
h1 {k} ⊢H ρ = HF.HRTFunctors.nat (Rels^ k) (postcomp-F (π₁Vec k) ∘F Functor.₀ (TSet ⊢H ∘F π₁Env) ρ ∘F π₁RT) (precomp-F π₁Rels ∘F Functor.₀ (TRel ⊢H) ρ) ( h1-eq ⊢H ρ) (h1-eq-morph-nat ⊢H ρ) (h1-eq-morph ⊢H ρ)   
  where open import HetEquality.HetFunctors (RTCat k) as HF

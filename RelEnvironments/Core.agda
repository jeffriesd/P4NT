-------------------------------------------------------
-- Relation Environments
-------------------------------------------------------


module RelEnvironments.Core where

open import RelSem.RelCats-Set 

{-
open import Environments.Core (Rels) (RelTerminal)
  renaming (Env to RelEnv
          ; EnvCat to RelEnvCat
          ; EnvTC to RelEnvTC 
          ; EnvFV to RelEnvFV
          ; Env[_,_] to RelEnv[_,_]) public
-}


-- define functions from SetEnvs to RelEnvs
open import SetCats using (Sets ; SetTerminal ; [Sets^_,Sets] ; SetFunctors-Terminal)


open import SetEnvironments.Core

open import Categories.Functor using (Functor)
open import Categories.Category

open import RTEnvironments.Core (RTCat) (RT-Terminal)
  renaming (Env to RelEnv
          ; idEnv to idRelEnv 
          ; EnvCat to RelEnvCat
          ; EnvMorph to RelEnvMorph 
          ; EnvTC to RelEnvTC 
          ; EnvFV to RelEnvFV
          ; Env[_,_] to RelEnv[_,_]
          ; EnvM[_,_] to RelEnvM[_,_]
          ; _∘Env_ to _∘RelEnv_ 
          ; _[_:fv=_] to  _[_:fv=_]Rel
          ; _[_:fvs=_] to  _[_:fvs=_]Rel
          ; ApplyEnv-FV to ApplyRelEnv-FV 
          ; ApplyEnv-TC to ApplyRelEnv-TC 
          ) public


  -- (D : ℕ → Category o l e) 
  -- (Dt : (k : ℕ) → Category.Obj (D k))
  -- (Dtm : (k : ℕ) → {d : Category.Obj (D k)} → (D k) [ d , Dt k ])

import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality using (_≡_)


open import SetCats using ([Sets^_,Sets])
open import Agda.Builtin.Nat renaming (Nat to ℕ) 
open import Function renaming (_∘_ to _∘'_) 


-- extend a functor from RT -> [Sets^ k ,Sets] to a functor on environment categories 
module _ (F : ∀ {k} → Functor (RTCat k) [Sets^ k ,Sets]) where 

    EnvFunc-RTObj : RelEnv → SetEnv
    EnvFunc-RTObj ρ = SetEnv[ (Functor.F₀ F) ∘' (RelEnv.tc ρ) , (Functor.F₀ F) ∘' (RelEnv.fv ρ) ]  

    EnvFunc-RT-map : ∀ {ρ ρ' : RelEnv} → RelEnvMorph ρ ρ' → SetEnvMorph (EnvFunc-RTObj ρ) (EnvFunc-RTObj ρ') 
    EnvFunc-RT-map {RelEnv[ tc , fv ]} {RelEnv[ .tc , fv' ]} RelEnvM[  ≡.refl , fvm ] = SetEnvM[ ≡.refl , Functor.F₁ F ∘' fvm ] 

    -- need to pattern match on eqTC proofs of equality since EnvFunc-RT-map is defined by
    -- matching on these proofs 
    EnvFunc-RT-homomorphism : ∀ {X Y Z : RelEnv} (f : RelEnvMorph X Y) (g : RelEnvMorph Y Z)
                           → SetEnvCat [
                                EnvFunc-RT-map (RelEnvCat Categories.Category.[ g ∘ f ])
                                ≈ SetEnvCat [ EnvFunc-RT-map g ∘ EnvFunc-RT-map f ]
                            ]
    EnvFunc-RT-homomorphism RelEnvM[ ≡.refl , fv ] RelEnvM[ ≡.refl , fv' ] = Functor.homomorphism F 

    EnvFunc-RT-resp : ∀ {X Y : RelEnv} → (f g : RelEnvMorph X Y)
                   → (f≈g : RelEnvCat [ f ≈ g ])
                   → SetEnvCat [ EnvFunc-RT-map f ≈ EnvFunc-RT-map g ]
    EnvFunc-RT-resp RelEnvM[ ≡.refl , fv ] RelEnvM[ ≡.refl , fv' ] f≈g = Functor.F-resp-≈ F f≈g  


    EnvFunc-RT : Functor RelEnvCat SetEnvCat 
    EnvFunc-RT = record
                { F₀ = EnvFunc-RTObj 
                ; F₁ = EnvFunc-RT-map 
                ; identity =  Functor.identity F 
                ; homomorphism = λ {X} {Y} {Z} {f} {g} → EnvFunc-RT-homomorphism f g 
                ; F-resp-≈ = λ {X} {Y} {f} {g} f≈g → EnvFunc-RT-resp f g f≈g  
                } 

π₁Env : Functor RelEnvCat SetEnvCat 
π₁Env = EnvFunc-RT π₁RT 

π₂Env : Functor RelEnvCat SetEnvCat 
π₂Env = EnvFunc-RT π₂RT 

-- extend a functor from [Sets^ k ,Sets] -> RT k to a functor on environment categories 
module _ (F : ∀ {k} → Functor [Sets^ k ,Sets] (RTCat k)) where 
  
    EnvFunc-SetsObj : SetEnv → RelEnv
    EnvFunc-SetsObj ρ = RelEnv[ Functor.F₀ F ∘' SetEnv.tc ρ ,  Functor.F₀ F ∘' SetEnv.fv ρ  ]   

    EnvFunc-Sets-map : ∀ {ρ ρ' : SetEnv}
                       → SetEnvMorph ρ ρ' 
                       → RelEnvMorph (EnvFunc-SetsObj ρ) (EnvFunc-SetsObj ρ')
    EnvFunc-Sets-map SetEnvM[ ≡.refl , fvm ] = RelEnvM[ ≡.refl , Functor.F₁ F ∘' fvm ]  

    EnvFunc-Sets-homomorphism : ∀ {X Y Z : SetEnv} 
                                → (f : SetEnvCat [ X , Y ]) (g : SetEnvCat [ Y , Z ])
                                → RelEnvCat [
                                    EnvFunc-Sets-map (SetEnvCat [ g ∘ f ])
                                    ≈ RelEnvCat [ EnvFunc-Sets-map g ∘ EnvFunc-Sets-map f ]
                                ]
    EnvFunc-Sets-homomorphism SetEnvM[ ≡.refl , fv ] SetEnvM[ ≡.refl , fv' ] = Functor.homomorphism F  


    EnvFunc-Sets-resp : ∀ {X Y : SetEnv}
                        → (f g : SetEnvMorph X Y)
                        → (f≈g : SetEnvCat [ f ≈ g ])
                        → RelEnvCat [ EnvFunc-Sets-map f ≈ EnvFunc-Sets-map g ]
    EnvFunc-Sets-resp SetEnvM[ ≡.refl , fv ] SetEnvM[ ≡.refl , fv' ] f≈g = Functor.F-resp-≈ F f≈g 


    EnvFunc-Sets : Functor SetEnvCat RelEnvCat 
    EnvFunc-Sets = record
                { F₀ = EnvFunc-SetsObj
                ; F₁ = EnvFunc-Sets-map 
                ; identity = Functor.identity F 
                ; homomorphism = λ {X} {Y} {Z} {f} {g} → EnvFunc-Sets-homomorphism f g 
                ; F-resp-≈ = λ {X} {Y} {f} {g} f≈g → EnvFunc-Sets-resp f g f≈g 
                } 

EqEnv : Functor SetEnvCat RelEnvCat
EqEnv = EnvFunc-Sets idRTFunctor




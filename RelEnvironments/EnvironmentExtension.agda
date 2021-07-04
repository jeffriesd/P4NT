
module RelEnvironments.EnvironmentExtension where

open import RelSem.RelCats using (Rels ; RTCat ; RT-Terminal ; Rels⇒RT0)

-- open import Environments.EnvironmentExtension (Rels) (RelTerminal) public 

open import Level renaming (zero to lzero ; suc to lsuc)

open import RTEnvironments.EnvironmentExtension
    {lsuc lzero} {lsuc lzero} {lsuc lzero}
    {lsuc lzero} {lsuc lzero} {lzero}
    {Rels} {RTCat} {RT-Terminal} {Rels⇒RT0}
  renaming ( -- extendTEnv2 to extendTRelEnvEnv
           -- ;
           extendEnv2 to extendRelEnv2 
           ; extendEnv-ρ×As to extendRelEnv-ρ×As
           ; extendEnv-αs to extendRelEnv-αs 
           ; extendEnv-α to extendRelEnv-α
           )
           public 


--   (toD0 : Functor R (D 0)) 



open import Syntax.NestedTypeSyntax 
open import Data.Vec using (Vec)
open import Categories.Functor using (Functor)
open import Categories.Category.Product using (Product)
open import RelEnvironments.Core using (RelEnvCat)
open import RelSem.RelCats using (RTCat ; Rels^)


module extendT where
  -- abstract 
    extendTRelEnv : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                → Functor (Product (Product RelEnvCat (RTCat k)) (Rels^ k)) RelEnvCat
    extendTRelEnv = extendTEnv2  


{-
    open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
    open import SetEnvironments.Core renaming (_≡TC_ to _≡TC'_)
    open import RelEnvironments.Core 
    open import RelSem.RelCats 
    open import Categories.Category
    open import SetEnvironments.EnvironmentExtension using (extendTSetEnv ; extendSetEnv-αs)
    open import Data.Product
    import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
    open import Relation.Binary.PropositionalEquality using (_≡_)
    open FVar ; open Vec
    open import Data.Nat using (ℕ)
    open ℕ
    open import SetCats using (to0Functors)

    Goal1 : ∀ {k} {φ : FVar k} {αs : Vec (FVar 0) k} 
            → (ρ : RelEnv)
            → ∀ (Rt : RTObj k) (Rs : Vec RelObj k) 
            → Functor.F₀ (extendTSetEnv φ αs)
                        ((Functor.F₀ π₁Env ρ , RTObj.F1 Rt) , vecfst Rs)
            ≡TC'
              Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs))

    Goal1 {αs = Vec.[]} ρ Rt Vec.[] = ≡.refl
    Goal1 {αs = α Vec.∷ αs} ρ Rt (R Vec.∷ Rs) = ≡.refl


    env-over1 : ∀ {k} (φ : FVar k)
                → (ρ : RelEnv)
                → (Rt : RTObj k)
                → ((Functor.F₀ π₁Env ρ) [ φ :fv= RTObj.F1 Rt ]Set)
                ≡FV-extSetEnv
                (Functor.F₀ π₁Env (ρ [ φ :fv= Rt ]Rel))
    env-over1 (φ ^F k) ρ Rt (ψ ^F j) with eqNat k j | φ ≟ ψ
    ... | yes ≡.refl | yes ≡.refl  = ≡.refl 
    ... | yes ≡.refl | no _ = ≡.refl
    ... | no _       | _    = ≡.refl

    env-over : ∀ {k} {αs : Vec (FVar 0) k} 
                → (ρ : RelEnv)
                → (Rs : Vec RelObj k) 
                → (Functor.F₀ (extendSetEnv-αs αs (Functor.F₀ π₁Env ρ)) ((vecfst Rs)))
                ≡FV-extSetEnv
                (Functor.F₀ π₁Env (Functor.F₀ (extendRelEnv-αs αs ρ) Rs))
    env-over {αs = []} ρ [] ψ = ≡.refl
    env-over {αs = α ^F k ∷ αs} ρ (R ∷ Rs) (ψ ^F j) with eqNat k j | α ≟ ψ
    ... | yes ≡.refl | yes ≡.refl  = ≡.refl 
    ... | yes ≡.refl | no _ = env-over {αs = αs} ρ Rs (ψ ^F j) 
    ... | no _       | _    = env-over {αs = αs} ρ Rs (ψ ^F j)  


    Goal2 : ∀ {k} {φ : FVar k} {αs : Vec (FVar 0) k} 
            → (ρ : RelEnv)
            → ∀ (Rt : RTObj k) (Rs : Vec RelObj k) 
            → Functor.F₀ (extendTSetEnv φ αs) ((Functor.F₀ π₁Env ρ , RTObj.F1 Rt) , vecfst Rs)
                    ≡FV-extSetEnv
                    (Functor.F₀ π₁Env (Functor.F₀ (extendTRelEnv φ αs) ((ρ , Rt) , Rs)))
    -- Goal2 {φ = φ ^F k} {αs = αs} ρ Rt Rs (ψ ^F j) with eqNat k j | φ ≟ ψ
    -- ... | yes ≡.refl | yes ≡.refl = {!!}
    -- ... | yes ≡.refl | no _ = {!!}
    -- ... | no _       | _    = {!!}

    Goal2 {φ = φ ^F .0} {αs = []} ρ Rt [] (ψ ^F j) with eqNat 0 j | φ ≟ ψ
    ... | yes ≡.refl | yes ≡.refl = ≡.refl 
    ... | yes ≡.refl | no _ = ≡.refl 
    ... | no _       | _    = ≡.refl 
    Goal2 {φ = φ ^F k} {αs = α ^F n ∷ αs} ρ Rt (R ∷ Rs) (ψ ^F j) with eqNat n j | α ≟ ψ
    ... | yes ≡.refl | yes ≡.refl = ≡.refl
    ... | yes ≡.refl | no _ = env-over {!!} (R ∷ Rs) (α ^F n) 
    ... | no _       | _    = {!!}

    Goal2 {φ = φ} {αs = αs} ρ Rt Rs (ψ ^F j) = {!   !} 

{-
∀ φ → 

   RTObj.F1
   (SetEnv.fv
    ((ρ [ φ :fv= Rt ]Rel) [ αs :fvs= Data.Vec.map ConstRT Rs ]Rel) φ))
≡
(SetEnv[ (λ x → RTObj.F1 (SetEnv.tc ρ x)) ,
 (λ x → RTObj.F1 (SetEnv.fv ρ x)) ]
 [ φ :fv= RTObj.F1 Rt ])
[ αs :fvs= map const (vecfst Rs)]
-}

-}

open extendT public 



-- {-# OPTIONS --rewriting #-}
-- open import Agda.Builtin.Equality.Rewrite


open import Syntax.NestedTypeSyntax 
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open FVar
open _∋_ 

-- open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (if_then_else_; true; false)
open import Categories.Category using (Category)
open import Categories.Category.Product using (Product ; _※_  ; πˡ ; πʳ)
open import Categories.Functor using (Functor ; _∘F_) renaming (id to idF)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; _∘ₕ_  to _∘h_ ; id to idnat)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) 

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Unit using (⊤)
open import Data.Empty 
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning
open import Data.Product hiding (curry) renaming (_×_ to _×'_)
open import Data.Sum
open import Data.Sum.Properties using (inj₂-injective)

open import SetCats
  using
  (Sets ; [Sets^_,Sets] ; Sets^ ; [[_,_]] ; ConstF ; Sets^cons ; SetSum ; SetProd)

open import RelSem.RelCats using (RelObj ; preservesRelObj)

open import Utils using (foreach)
-- open import CatUtils 
open import SetEnvironments.Core
  using
  (SetEnvCat ; SetEnv ; SetEnvMorph ; NatEnv ; _∘SetEnv_
  ; ForgetFVSetEnv ; ApplySetEnv-FV ; ApplySetEnv-TC )
open import SetEnvironments.EnvironmentExtension -- using (extendTSetEnv ; extendSetEnv-αs ; extendSetEnv-ρ×As)
open import HFixFunctorLib 

module SetSem.NestedSetSemantics where






-------------------------------------------------------
-- SetSem functor -- 
-------------------------------------------------------

SetSem : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
            → Γ ≀ Φ ⊢ F
            → Functor SetEnvCat Sets

----------
-- TENV -- 
----------



module NormalT where 

--   abstract 

    TSetProd : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
              {φ : FVar k} {αs : Vec (FVar 0) k}
            → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
            → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) Sets


    TEnv : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
              {φ : FVar k} {αs : Vec (FVar 0) k}
            → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
            → Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])

    -------------------------------------------------------
    -- TENV definitions 
    -------------------------------------------------------

    -- TSetProd : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
    --           {φ : FVar k} {αs : Vec (FVar 0) k}
    --         → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
    --         → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) Sets
    TSetProd {k} {Γ} {H} {φ} {αs} ⊢H = SetSem {Γ} {(∅ ,++ αs) ,, φ} ⊢H ∘F extendTSetEnv φ αs


    -- TEnv : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
    --           {φ : FVar k} {αs : Vec (FVar 0) k}
    --         → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
    --         → Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])


    TEnv {k} {Γ} {H} {φ} {αs} ⊢H = curry.F₀ (curry.F₀ (TSetProd ⊢H))




module AbT where 

    -- module T = NormalT


    -- abstract version of TEnv for faster type-checking 
    abstract 
      TEnv : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
                {φ : FVar k} {αs : Vec (FVar 0) k}
              → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
              → Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
  
      -- TEnv {k} {Γ} {H} {φ} {αs} ⊢H = curry.F₀ (curry.F₀ (TSetProd ⊢H))
      TEnv = NormalT.TEnv
      -- TEnv = T.TEnv
      

      TEnv≡absTEnv : (λ {k} {Γ} {H} {φ} {αs} → NormalT.TEnv {k} {Γ} {H} {φ} {αs}) ≡ (λ {k} {Γ} {H} {φ} {αs} → TEnv {k} {Γ} {H} {φ} {αs})
      TEnv≡absTEnv = ≡.refl

      TEnv≡absTEnv' : ∀ {k : ℕ} {Γ} {H} {φ : FVar k} {αs : Vec (FVar 0) k} (⊢H : Γ ≀ (∅ ,++ αs) ,, φ ⊢ H)
                      → NormalT.TEnv ⊢H ≡ TEnv ⊢H
      TEnv≡absTEnv' ⊢H = ≡.refl

    -- this type-checks but is it useful? 
    Tsubst : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr} {φ : FVar k} {αs : Vec (FVar 0) k}
            → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H)
            → ∀ {a} (P : Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]]) → Set a)
            → P (NormalT.TEnv ⊢H)
            → P (TEnv ⊢H)
    Tsubst ⊢H P pt = ≡.subst P (TEnv≡absTEnv' ⊢H) pt 



open AbT
-- open NormalT




-----------------------------------------------------
-- Nat Types
-----------------------------------------------------



-- take a functor interpreting some type and 
-- compose with an environment extension functor 
-- 
-- λ ⟦Fs⟧ → ⟦Fs⟧ ρ [ αs := _ ] 
-- 
-- this is an instance of functor precomposition, so 
-- we can turn this into a higher order functor 
extendSetSem-αs : ∀ {k} → (αs : Vec (FVar 0) k) 
    → (ρ : SetEnv)
    → Functor SetEnvCat Sets
    → Functor (Sets^ k) Sets
extendSetSem-αs αs ρ ⟦F⟧ = 
  let ρ[-] = extendSetEnv-αs αs ρ
    in ⟦F⟧ ∘F ρ[-] 



{-# NO_UNIVERSE_CHECK #-}
{-# NO_POSITIVITY_CHECK #-}
record NatType3 {k : ℕ} (αs : Vec (FVar 0) k) (ρ : SetEnv) (⟦F⟧ ⟦G⟧ : Functor SetEnvCat Sets) : Set where
  constructor NatT3[_]
  eta-equality

  field
    nat : NaturalTransformation (extendSetSem-αs αs ρ ⟦F⟧) (extendSetSem-αs αs ρ ⟦G⟧)

{-
    preserves-relations :
      -- ∀ Rs . (nat As , nat Bs) should be a
      -- morphism of relations from
      --
      -- ⟦F⟧ : RelEnv → Rels
      -- want to apply ⟦F⟧ on rel env
      -- (EqEnv ρ) [ αs := Rs ]
      -- (⟦F⟧ ∘F extendRelEnv-αs αs (EqEnv ρ)) Rs
      -- = extendRelSem-αs αs (EqEnv ρ) ⟦F⟧
      -- 
      -- Functor.F₀ ⟦F⟧ (Functor.F₀ (extendRelEnv-αs αs (Functor.F₀ EqEnv ρ)) Rs)
      -- to
      -- Functor.F₀ ⟦G⟧ (Functor.F₀ (extendRelEnv-αs αs (Functor.F₀ EqEnv ρ)) Rs)
      -- 
      -- 
      ∀ (Rs : Vec RelObj k) 
      → preservesRelObj
          (Functor.F₀ (extendRelSem-αs αs (Functor.F₀ EqEnv ρ) ⟦F⟧) Rs)
          (Functor.F₀ (extendRelSem-αs αs (Functor.F₀ Eqenv ρ) ⟦G⟧) Rs)
          ? ? 
          
-}





NatTypeSem3-map : ∀ {k} (αs : Vec (FVar 0) k) (⟦F⟧ ⟦G⟧ : Functor SetEnvCat Sets) 
                  → {ρ ρ' : SetEnv}
                  → SetEnvMorph ρ ρ'
                  → NatType3 αs (NatEnv ρ) ⟦F⟧ ⟦G⟧ 
                  → NatType3 αs (NatEnv ρ') ⟦F⟧ ⟦G⟧ 
NatTypeSem3-map αs ⟦F⟧ ⟦G⟧ record { eqTC = ≡.refl ; fv = fv } = idf
-- rewrite (NatEnv-eq f) = idf



NatTypeSem3-homomorphism : ∀ {k} (αs : Vec (FVar 0) k)
                            → (⟦F⟧ ⟦G⟧ : Functor SetEnvCat Sets)
                            → {ρ1 ρ2 ρ3 : SetEnv}
                            → (f : SetEnvMorph ρ1 ρ2) 
                            → (g : SetEnvMorph ρ2 ρ3)
                            → ∀ {x}
                            → NatTypeSem3-map αs ⟦F⟧ ⟦G⟧ (g ∘SetEnv f) x
                            ≡ NatTypeSem3-map αs ⟦F⟧ ⟦G⟧ g 
                              (NatTypeSem3-map αs ⟦F⟧ ⟦G⟧ f x)
-- NatEnv-eq : {ρ ρ' : SetEnv} → SetEnvMorph ρ ρ' → NatEnv ρ ≡ NatEnv ρ'
NatTypeSem3-homomorphism αs ⟦F⟧ ⟦G⟧ f@(record { eqTC = ≡.refl ; fv = fv₁ }) g@(record { eqTC = ≡.refl ; fv = fv }) = ≡.refl
-- with NatEnv-eq f | NatEnv-eq g | NatEnv-eq (g ∘SetEnv f)
-- ... | ≡.refl | ≡.refl | ≡.refl = ≡.refl 

NatTypeSem3-resp : ∀ {k} (αs : Vec (FVar 0) k) ⟦F⟧ ⟦G⟧ {ρ ρ' : SetEnv}
                     (f g : SetEnvMorph ρ ρ')
                     (f≈g : SetEnvCat Categories.Category.[ f ≈ g ]) 
                     → Sets Categories.Category.[ 
                       NatTypeSem3-map αs ⟦F⟧ ⟦G⟧ f 
                     ≈ NatTypeSem3-map αs ⟦F⟧ ⟦G⟧ g ]
NatTypeSem3-resp αs ⟦F⟧ ⟦G⟧ f@(record { eqTC = ≡.refl ; fv = fv }) g@(record { eqTC = ≡.refl ; fv = fv' }) f≈g = ≡.refl
-- with NatEnv-eq f | NatEnv-eq g 
-- ... | ≡.refl | ≡.refl = ≡.refl 



-- This definition of NatTypeSem should work well with SetSem-weaken proofs.
-- Since it takes SetSem F and SetSem G directly as arguments (as opposed to types ⊢F and ⊢G),
-- we can easily prove NatTypeSem ⟦F⟧ ⟦G⟧ ≡ NatTypeSem (weaken ⟦F⟧) (weaken ⟦G⟧)
--
-- 
NatTypeSem : ∀ {k : ℕ} → (αs : Vec (FVar 0) k) → (SemF SemG : Functor SetEnvCat Sets)
              → Functor SetEnvCat Sets
NatTypeSem αs ⟦F⟧ ⟦G⟧ = record
  -- use NatEnv to forget about functorial part of ρ 
  { F₀ = λ ρ → NatType3 αs (NatEnv ρ) ⟦F⟧ ⟦G⟧
  ; F₁ = NatTypeSem3-map αs ⟦F⟧ ⟦G⟧  
  ; identity = ≡.refl
  ; homomorphism = λ {ρ1 ρ2 ρ3 f g} → NatTypeSem3-homomorphism αs ⟦F⟧ ⟦G⟧ f g 
  ; F-resp-≈ = λ {ρ ρ' f g} f≈g → NatTypeSem3-resp αs ⟦F⟧ ⟦G⟧ f g f≈g
  }


-- maybe could move NatEnv part to functor level instead of object level? 
-- 
-- Like define NatTypeSem without NatEnv... (but this is difficult on its own without NatEnv trick ... )
-- and then compose NatTypeSem with a functor-level NatEnv that forgets fv part of environment 

VarSem-FV : ∀ {k : ℕ} (φ : FVar k) → Functor SetEnvCat [Sets^ k ,Sets]
VarSem-FV φ = ApplySetEnv-FV φ 




VarSem-TC : ∀ {k : ℕ} (φ : TCVar k) → Functor SetEnvCat [Sets^ k ,Sets]
VarSem-TC φ = ApplySetEnv-TC φ 



SetSemVec : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx}
              → {Fs : Vec TypeExpr k}
              → foreach (λ F → Γ ≀ Φ ⊢ F) Fs
              → Functor SetEnvCat (Sets^ k)
SetSemVec {zero} {Γ} {Φ} {[]} _ = ConstF []
SetSemVec {suc k} {Γ} {Φ} {F ∷ Fs} (⊢F , ⊢Fs) = 
  let SetSemF×SetSemFs : Functor SetEnvCat (Product Sets (Sets^ k))
      SetSemF×SetSemFs = SetSem ⊢F ※ SetSemVec ⊢Fs
    in Sets^cons k ∘F SetSemF×SetSemFs



-- make MuSem parameterized by interpretation of arguments (Ks) 
-- so proofs involving substitution, etc. are easily proved without needlessly unwinding 
-- eval ∘F ... 
MuSem : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
              {φ : FVar k} {αs : Vec (FVar 0) k}
            → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
            → Functor SetEnvCat (Sets^ k) → Functor SetEnvCat Sets 
MuSem {k} ⊢H SemKs = 
  let fixT : Functor SetEnvCat [Sets^ k ,Sets]
      -- explicitly forget functorial part of environment before taking fixpoint. 
      fixT = (fixH ∘F TEnv ⊢H) ∘F ForgetFVSetEnv
  in eval ∘F (fixT ※ SemKs)


-- end abstract 



SetSem 𝟘-I = ConstF ⊥
SetSem 𝟙-I = ConstF ⊤
SetSem (Nat-I {αs = αs} ⊢F ⊢G) = NatTypeSem αs (SetSem ⊢F) (SetSem ⊢G) 
SetSem (+-I ⊢F ⊢G) = SetSum ∘F (SetSem ⊢F ※ SetSem ⊢G)
SetSem (×-I ⊢F ⊢G) = SetProd ∘F (SetSem ⊢F ※ SetSem ⊢G)
SetSem (AppT-I {φ = φ} Γ∋φ Gs ⊢Gs) = eval ∘F (VarSem-TC φ ※ SetSemVec ⊢Gs)
SetSem (AppF-I {φ = φ} Φ∋φ Gs ⊢Gs) = eval ∘F (VarSem-FV φ ※ SetSemVec ⊢Gs)
SetSem (μ-I {k = k} ⊢F Ks ⊢Ks) = MuSem ⊢F (SetSemVec ⊢Ks)





module other where 



    -- extend an environment by sending a variable α to interpretation of some type H 
    extendEnvFVar : ∀ {Γ : TCCtx} {Φ  : FunCtx} {H : TypeExpr} → (α : FVar 0) → (⊢H : Γ ≀ Φ ⊢ H)
                → Functor SetEnvCat SetEnvCat
    extendEnvFVar α ⊢H = extendSetEnv-α α ∘F (idF ※ SetSem ⊢H)


    -- if we explicitly forget about functorial part of environment, 
    -- any extensions of the functorial part of the environment have no effect 
    ForgetFVSetEnv∘extendEnvFVar≃ForgetFVSetEnv : ∀ {Γ} {Φ} {H} (α : FVar 0) → (⊢H : Γ ≀ Φ ⊢ H)
                                    → ForgetFVSetEnv ∘F extendEnvFVar α ⊢H 
                                    ≃ ForgetFVSetEnv 
    ForgetFVSetEnv∘extendEnvFVar≃ForgetFVSetEnv α ⊢H = 
                record { F⇒G = record { η = λ _ → Category.id SetEnvCat ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl } 
                        ; F⇐G = record { η = λ _ → Category.id SetEnvCat ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl } 
                        ; iso = λ _ → record { isoˡ = ≡.refl ; isoʳ = ≡.refl } } 


-- -- if we extend environment with a variable that isn't equal to φ, the extension doesn't matter 
-- VarSem-FV-extend-diffArity : ∀ {k : ℕ} {Γ} {Φ} {H} → (α : FVar 0) → (⊢H : Γ ≀ Φ ⊢ H) → (φ : FVar (suc k))
--                              → VarSem-FV φ
--                              ≃ VarSem-FV φ ∘F extendEnvFVar α ⊢H 
-- VarSem-FV-extend-diffArity α ⊢H φ = {!   !}


    import Relation.Binary.HeterogeneousEquality as Het
    -- NatTypeSem3-map always behaves as identity 
    NatTypeSem3-map-id : ∀ {k} (αs : Vec (FVar 0) k) (⟦F⟧ ⟦G⟧ : Functor SetEnvCat Sets) 
                    → {ρ ρ' : SetEnv}
                    → (f : SetEnvMorph ρ ρ')
                    → {x : NatType3 αs (NatEnv ρ) ⟦F⟧ ⟦G⟧}
                    → NatTypeSem3-map αs ⟦F⟧ ⟦G⟧ f x Het.≅ x 
    NatTypeSem3-map-id αs ⟦F⟧ ⟦G⟧ record { eqTC = ≡.refl ; fv = fv } = Het.refl
    -- rewrite (NatEnv-eq f) = Het.refl 




    -- this is an instance of precomposition, i.e.,
    -- λ F → F ∘ extendSetEnv-αs αs ρ 
    -- 
    -- TODO 
    -- should be able to define this in terms of more general precomposition construction 
    -- 
    -- this is also just whiskering 
    extendSetSem-αs-higher : ∀ {k} → (αs : Vec (FVar 0) k) 
        → (ρ : SetEnv)
        → Functor (Functors SetEnvCat Sets) (Functors (Sets^ k) Sets)
    extendSetSem-αs-higher αs ρ = record
        { F₀ = λ ⟦F⟧ → extendSetSem-αs αs ρ ⟦F⟧  
        ; F₁ = λ {F} {G} η → 
            record { η = λ Xs → NaturalTransformation.η η (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , Xs)) 
                    ; commute = λ f → NaturalTransformation.commute η (Functor.F₁ (extendSetEnv-αs αs ρ) f) 
                    ; sym-commute = λ f → NaturalTransformation.sym-commute η (Functor.F₁ (extendSetEnv-αs αs ρ) f) }
        ; identity = ≡.refl
        ; homomorphism = ≡.refl
        ; F-resp-≈ = λ f≈g → f≈g
        } 


open other public 

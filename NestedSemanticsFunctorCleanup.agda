{-# OPTIONS --allow-unsolved-metas #-}


open import NestedSyntax6NoStrings using (_≀_⊢_ ; TypeContext ; _∋_ ; AppF0 ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; ∅ ; _,++_ ; _,,_)
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open _∋_ 

-- open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (if_then_else_; true; false)
open import Categories.Category using (Category)
open import Categories.Category.Product using (Product ; _※_ )
open import Categories.Functor using (Functor ; _∘F_)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
-- open import Categories.Diagram.Cocone
open import Data.Nat using (ℕ ; _≤_ )
open ℕ
open _≤_
open import Data.Unit using (⊤)
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning
open import Data.Product hiding (curry) renaming (_×_ to _×'_)
open import Data.Sum
open import Data.Sum.Properties using (inj₂-injective)
open import SetCatslzero
open import Utils
open import EnvironmentsInnerRecCleanupExt
open import HFixFunctorLib 

module NestedSemanticsFunctorCleanup where


-- mutual

  -------------------------------------------------------
  -- SetSem functor -- 
  -------------------------------------------------------
  
SetSem : ∀ (Γ : TCCtx) → (Φ : FunCtx) → (F : TypeExpr)
            → Γ ≀ Φ ⊢ F
            → Functor SetEnvCat Sets

{-

SetSem : ∀ (Γ : TCCtx) → (Φ : FunCtx) → (F : TypeExpr)
            → Γ ≀ Φ ⊢ F
            → Functor SetEnvCat Sets

SetSemObj : ∀ {Γ : TCCtx} {Φ : FunCtx} {F : TypeExpr}
            → Γ ≀ Φ ⊢ F → SetEnv → Set

SetSemMap : ∀ {Γ} {Φ} {F} (⊢F : Γ ≀ Φ ⊢ F) {ρ ρ' : SetEnv}
              → (f : SetEnvMorph ρ ρ')
              → SetSemObj ⊢F ρ → SetSemObj ⊢F ρ'

SetSemMapId : ∀ {Γ} {Φ} {F} {ρ : SetEnv} (⊢F : Γ ≀ Φ ⊢ F) 
              → ∀ {x : SetSemObj ⊢F ρ} 
              → SetSemMap ⊢F (Category.id SetEnvCat {ρ}) x ≡ x


SetSemMapHomo : ∀ {Γ} {Φ} {F}  {ρ} {ρ'} {ρ''}
                → (⊢F : Γ ≀ Φ ⊢ F)
                → (f : SetEnvMorph ρ ρ') → (g : SetEnvMorph ρ' ρ'')
                → ∀ {x : SetSemObj ⊢F ρ}
                → SetSemMap ⊢F (g ∘SetEnv f) x ≡ SetSemMap ⊢F g (SetSemMap ⊢F f x)

SetSemMapF-resp : ∀ {Γ} {Φ} {F} (⊢F : Γ ≀ Φ ⊢ F) {ρ} {ρ'}
                  {f g : SetEnvMorph ρ ρ'}
                  (f≈g : SetEnvCat Categories.Category.[ f ≈ g ]) 
                  → Sets Categories.Category.[ SetSemMap ⊢F f ≈ SetSemMap ⊢F g ]


-- interpretation of vectors of types 
SetSemObjVec : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx}
              → {Fs : Vec TypeExpr k}
              → foreach (λ F → Γ ≀ Φ ⊢ F) Fs
              → SetEnv 
              → Vec Set k

SetSemMapVec : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} {ρ ρ' : SetEnv}
              {Fs : Vec TypeExpr k}
              → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
              → SetEnvMorph ρ ρ'
              → VecFSpace (SetSemObjVec ⊢Fs ρ) (SetSemObjVec ⊢Fs ρ')

SetSemMapVecId : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} {ρ : SetEnv} 
              → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
              → pointwise-≈ (SetSemMapVec ⊢Fs (Category.id SetEnvCat {ρ})) (Category.id (Sets^ k))

SetSemMapVecHomo : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k}  {ρ} {ρ'} {ρ''}
                  → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
                  → (f : SetEnvMorph ρ ρ')
                  → (g : SetEnvMorph ρ' ρ'')
                  → pointwise-≈ (SetSemMapVec ⊢Fs (g ∘SetEnv f)) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f)

SetSemMapVecF-resp : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} {ρ} {ρ'}
                  {f g : SetEnvMorph ρ ρ'}
                  (f≈g : SetEnvCat Categories.Category.[ f ≈ g ]) 
                  → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
                  → (Sets^ k) Categories.Category.[ SetSemMapVec ⊢Fs f ≈ SetSemMapVec ⊢Fs g ]


-}
---------------------------------------------------
-----------------------------------------------------
extendSetSem-αs : ∀ {k} {Γ} {Φ} {H} → (αs : Vec (FVar 0) k) → SetEnv
              → (⊢H : Γ ≀ Φ ,++ αs ⊢ H)
              → Functor (Sets^ k) Sets

-----------------------------------------------------
-------------------------------------------------------
-- use this definition for interp of nat types 
-- extendSetSem-αs : ∀ {k} {Γ} {Φ} {H} → (αs : Vec (FVar 0) k) → SetEnv
--               → (⊢H : Γ ≀ Φ ,++ αs ⊢ H)
--               → Functor (Sets^ k) Sets
-- extendSetSem-αs {k} {Γ} {Φ} {H} αs ρ ⊢H = SetSem Γ (Φ ,++ αs) H ⊢H  ∘F extendSetEnv-αs αs ρ 

{-# NO_UNIVERSE_CHECK   #-}
{-# NO_POSITIVITY_CHECK #-}
record NatType {n : ℕ} {Γ : TCCtx} {F G : TypeExpr} {αs : Vec (FVar 0) n} (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G) (ρ : SetEnv) : Set 

-----------------------------------------------------
-------------------------------------------------------

-------------------------------------------------------
----------
-- TENV -- 
----------
TEnvProd : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
          {φ : FVar k} {αs : Vec (FVar 0) k}
        → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
        → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) Sets


TEnv : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
          {φ : FVar k} {αs : Vec (FVar 0) k}
        → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
        → Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])


T^H : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
        {φ : FVar k} {αs : Vec (FVar 0) k}
      → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
      → SetEnv 
      → Functor [Sets^ k ,Sets] [Sets^ k ,Sets]

-------------------------------------------------------
-- END TYPES
-------------------------------------------------------


-------------------------------------------------------
-- semantics for Nat type 
-------------------------------------------------------
record NatType {n} {Γ} {F G} {αs} ⊢F ⊢G ρ where
  constructor NatT[_]
  eta-equality
  field
    nat : NaturalTransformation (extendSetSem-αs αs ρ ⊢F) (extendSetSem-αs αs ρ ⊢G)
    -- NatType ⊢F ⊢G (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As))
    -- means record has type 
    -- nat : NaturalTransformation (extendSetSem-αs αs (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As)) ⊢F) 
    --                             (extendSetSem-αs αs ρ ⊢G)



-- extendSetSem-αs : ∀ {k} {Γ} {Φ} {H} → (αs : Vec (FVar 0) k) → SetEnv
--               → (⊢H : Γ ≀ Φ ,++ αs ⊢ H)
--               → Functor (Sets^ k) Sets
extendSetSem-αs {k} {Γ} {Φ} {H} αs ρ ⊢H = SetSem Γ (Φ ,++ αs) H ⊢H  ∘F extendSetEnv-αs αs ρ 


-------------------------------------------------------
-- TENV definitions 
-------------------------------------------------------

-- TEnvProd : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
--           {φ : FVar k} {αs : Vec (FVar 0) k}
--         → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
--         → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) Sets
TEnvProd {k} {Γ} {H} {φ} {αs} ⊢H = SetSem Γ ((∅ ,++ αs) ,, φ) H ⊢H ∘F extendTEnv2 φ αs



-- TEnv : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
--           {φ : FVar k} {αs : Vec (FVar 0) k}
--         → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
--         → Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
TEnv {k} {Γ} {H} {φ} {αs} ⊢H = curry.F₀ (curry.F₀ (TEnvProd ⊢H))



-- T^H : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
--         {φ : FVar k} {αs : Vec (FVar 0) k}
--       → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
--       → SetEnv 
--       → Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
T^H ⊢H ρ = Functor.F₀ (TEnv ⊢H) ρ


-----------------------------------------------------
-----------------------------------------------------



-----------------------------------------------------
-- -- -- Set semantics functor
-----------------------------------------------------

-----------------------------------------------------
-- Action on objects
-----------------------------------------------------



-- this is used in the interpretation of Nat types to 
-- ignore forget about the functorial part of the environment.
-- This makes it much easier to prove NatType F G ρ ≡ NatType F G ρ' 
-- when there is a morphism f : ρ → ρ'
NatEnv : SetEnv → SetEnv
NatEnv Env[ tc , fv ] = Env[ tc , trivFVEnv ]
-- record { tc = λ {k} → SetEnv.tc ρ {k} ; fv = trivFVEnv }

-- proof that NatEnv ρ ≡ NatEnv ρ' when there is a morphism ρ → ρ'
NatEnv-eq : {ρ ρ' : SetEnv} → SetEnvMorph ρ ρ' → NatEnv ρ ≡ NatEnv ρ'
NatEnv-eq f = ≡.cong₂ Env[_,_] (SetEnvMorph.eqTC f) ≡.refl


NT-eq : ∀ {o l e} {C : Category o l e} {F G F' G' : Functor C Sets}
         → F ≡ F' → G ≡ G' 
         → NaturalTransformation F G ≡ NaturalTransformation F' G'
NT-eq = ≡.cong₂ NaturalTransformation 

make-NT-eq : ∀ {o l e} {C : Category o l e} {F G F' G' : Functor C Sets}
         → F ≡ F' → G ≡ G' 
         → NaturalTransformation F G 
         → NaturalTransformation F' G'
make-NT-eq p q η rewrite (NT-eq p q) = η 

-- used in SetSemMapHomo Nat case 
make-NT-eq-comp : ∀ {o l e} {C : Category o l e} {F1 F2 F3 G1 G2 G3 : Functor C Sets}
         → (F12 : F1 ≡ F2) → (G12 : G1 ≡ G2)
         → (F23 : F2 ≡ F3) → (G23 : G2 ≡ G3)
         → (F13 : F1 ≡ F3) → (G13 : G1 ≡ G3)
         → (η : NaturalTransformation F1 G1)
         → make-NT-eq F13 G13 η ≡ make-NT-eq F23 G23 (make-NT-eq F12 G12 η)
make-NT-eq-comp ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl η = ≡.refl 

-- -- used in SetSemMapF-resp Nat case 
make-NT-eq-lem : ∀ {o l e} {C : Category o l e} {F F' G G' : Functor C Sets}
         → (p p' : F ≡ F') → (q q' : G ≡ G')
         → (η : NaturalTransformation F G)
         → make-NT-eq  p q  η ≡ make-NT-eq p' q' η
make-NT-eq-lem ≡.refl ≡.refl ≡.refl ≡.refl η = ≡.refl

nat-extend-lem : ∀ {k} {Γ : TCCtx} {αs : Vec (FVar 0) k} {F : TypeExpr} {ρ ρ' : SetEnv} 
                 → SetEnvMorph ρ ρ' → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F)
                 → extendSetSem-αs αs (NatEnv ρ) ⊢F ≡ extendSetSem-αs αs (NatEnv ρ') ⊢F
nat-extend-lem {αs = αs} f ⊢F = ≡.cong₂ (extendSetSem-αs αs) (NatEnv-eq f) ≡.refl 




-- -- SetSemObjVec : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx}
-- --               → {Fs : Vec TypeExpr k}
-- --               → foreach (λ F → Γ ≀ Φ ⊢ F) Fs
-- --               → SetEnv 
-- --               → Vec Set k
-- -- -- SetSemObjVec Fs ⊢Fs ρt ρf = vmap (λ x₁ → SetSemObj (proj₂ x₁) ρt ρf) (foreach-toVec ⊢Fs) 
-- SetSemObjVec {Fs = Vec.[]} _ _ = Vec.[]
-- SetSemObjVec {Fs = F ∷ Fs} (⊢F , ⊢Fs) ρ = (SetSemObj ⊢F ρ) ∷ SetSemObjVec ⊢Fs ρ


-- -- SetSemObj : ∀ {Γ : TCCtx} {Φ : FunCtx} {F : TypeExpr}
-- --             → Γ ≀ Φ ⊢ F
-- --             → SetEnv 
-- --             → Set
-- SetSemObj 𝟘-I _   = ⊥'
-- SetSemObj 𝟙-I _   = ⊤
-- SetSemObj (+-I ⊢F ⊢G) ρ  = SetSemObj ⊢F ρ ⊎ SetSemObj ⊢G ρ 
-- SetSemObj (×-I ⊢F ⊢G) ρ  = SetSemObj ⊢F ρ ×' SetSemObj ⊢G ρ 
-- SetSemObj (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) ρ  = Functor.F₀ (SetEnv.tc ρ φ) (SetSemObjVec ⊢Fs ρ)
-- SetSemObj (AppF-I {φ = φ} Φ∋φ Fs ⊢Fs) ρ  = Functor.F₀ (SetEnv.fv ρ φ) (SetSemObjVec ⊢Fs ρ)
-- SetSemObj (Nat-I ⊢F ⊢G) ρ  = NatType ⊢F ⊢G (NatEnv ρ)
-- -- placeholder until relational semantics is defined.. 
    
-- -- SetSemObj (μ-I {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) ρ  = HFixFunctor (T^H ⊢F ρ) (SetSemObjVec ⊢Gs ρ)
-- SetSemObj (μ-I {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) ρ  = Functor.F₀ (fixHFunc (T^H ⊢F ρ)) (SetSemObjVec ⊢Gs ρ)




-- -----------------------------------------------------
-- -- SetSem functorial action
-- -----------------------------------------------------


-- -- -- mapping of SetSemMap over vectors 
-- -- SetSemMapVec : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} {ρ ρ' : SetEnv}
-- --               {Fs : Vec TypeExpr k}
-- --               → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
-- --               → SetEnvMorph ρ ρ'
-- --               → VecFSpace (SetSemObjVec ⊢Fs ρ) (SetSemObjVec ⊢Fs ρ')
-- SetSemMapVec {Fs = Vec.[]} Data.Unit.tt f = fnil
-- SetSemMapVec {Fs = F ∷ Fs} (⊢F , ⊢Fs) f = fcons (SetSemMap ⊢F f) (SetSemMapVec ⊢Fs f) 

-- -- SetSemMap : ∀ {Γ} {Φ} {F} (⊢F : Γ ≀ Φ ⊢ F) {ρ ρ' : SetEnv}
-- --               → (f : SetEnvMorph ρ ρ')
-- --               → SetSemObj ⊢F ρ 
-- --               → SetSemObj ⊢F ρ'
-- SetSemMap 𝟙-I {ρ} {ρ'} f Fρ = Data.Unit.tt
-- SetSemMap (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) {ρ} {ρ'} f Fρ = 
--     NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ') 
--         (Functor.F₁ (SetEnv.tc ρ φ) (SetSemMapVec ⊢Fs f) Fρ)

--     -- -- equivalently, by naturality 
--     -- Functor.F₁ (SetEnv.tc ρ' φ) (SetSemMapVec ⊢Fs f) 
--     --   (NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ) Fρ)
-- SetSemMap (AppF-I {φ = φ} Ψ∋φ Fs ⊢Fs) {ρ} {ρ'} f Fρ = 
--   NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ') 
--       (Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs f) Fρ)
--     -- -- equivalently, by naturality 
--     -- Functor.F₁ (SetEnv.fv ρ' φ) (SetSemMapVec ⊢Fs f) 
--     --   (NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ) Fρ)
-- SetSemMap (+-I ⊢F ⊢G) {ρ} {ρ'} f (inj₁ x) = inj₁ (SetSemMap ⊢F f x)
-- SetSemMap (+-I ⊢F ⊢G) {ρ} {ρ'} f (inj₂ y) = inj₂ (SetSemMap ⊢G f y)
-- SetSemMap (×-I ⊢F ⊢G) {ρ} {ρ'} f (fst , snd) = (SetSemMap ⊢F f fst) , (SetSemMap ⊢G f snd)
-- -- goal : NaturalTransformation (extendSetSem-αs αs ρ' ⊢F) (extendSetSem-αs αs ρ' ⊢G) 
-- -- -- need lemma that extendSetSem-αs ρ ⊢F = extendSetSem-αs ρ' ⊢F whenever Φ = ∅ 
-- -- 
-- -- TODO ?? could redefine set interp of NAt types to not depend on fv part of ρ environment..
-- SetSemMap (Nat-I ⊢F ⊢G) f NatT[ nat ]  = NatT[ make-NT-eq (nat-extend-lem f ⊢F) (nat-extend-lem f ⊢G) nat ]
-- -- 
-- -- naturality square 
-- -- have : HFixFunctor (T^H ⊢F ρ)  (SetSemObjVec ⊢Gs ρ)
-- -- goal : HFixFunctor (T^H ⊢F ρ') (SetSemObjVec ⊢Gs ρ')
-- SetSemMap (μ-I F ⊢F Gs ⊢Gs) {ρ} {ρ'} f Fρ = 
--     let μTFρ'-Gsf : HFixFunctor (T^H ⊢F ρ') (SetSemObjVec ⊢Gs ρ)
--                   → HFixFunctor (T^H ⊢F ρ') (SetSemObjVec ⊢Gs ρ')
--         μTFρ'-Gsf   = HFix-fmap (T^H ⊢F ρ') (SetSemMapVec ⊢Gs f) 
--         --
--         TFf : NaturalTransformation (Functor.F₀ (TEnv ⊢F) ρ) (Functor.F₀ (TEnv ⊢F) ρ')
--         TFf   = Functor.F₁ (TEnv ⊢F) f 
--         -- 
--         μTFf : NaturalTransformation (fixHFunc (T^H ⊢F ρ)) (fixHFunc (T^H ⊢F ρ'))
--         μTFf = HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ') TFf
--         in μTFρ'-Gsf (NaturalTransformation.η μTFf (SetSemObjVec ⊢Gs ρ)  Fρ  )
--         -- -- equivalently, by naturality 
--         -- μT^HρGf       = HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs f) 
--         -- in NaturalTransformation.η μT^Hρ→μT^Hρ' (SetSemObjVec ⊢Gs ρ') (μT^HρGf Fρ)



-- -----------------------------------------------------
-- -- SetSem functorial action preserves identity
-- -----------------------------------------------------

-- -- -- proof that SetSemMapVec preserves identity morphisms 
-- -- SetSemMapVecId : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} {ρ : SetEnv} 
-- --               → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
-- --               → pointwise-≈ (SetSemMapVec ⊢Fs (Category.id SetEnvCat {ρ})) (Category.id (Sets^ k))
-- SetSemMapVecId {Fs = Vec.[]} Data.Unit.tt = lift Data.Unit.tt
-- SetSemMapVecId {Fs = F ∷ Fs} (⊢F , ⊢Fs) = (SetSemMapId ⊢F) , (SetSemMapVecId ⊢Fs) 

-- -- -- proof that SetSemMap preserves identity morphisms 
-- -- SetSemMapId : ∀ {Γ} {Φ} {F} {ρ : SetEnv} (⊢F : Γ ≀ Φ ⊢ F) 
-- --               → ∀ {x : SetSemObj ⊢F ρ} 
-- --               → SetSemMap ⊢F (Category.id SetEnvCat {ρ}) x ≡ x
-- SetSemMapId 𝟙-I {Data.Unit.tt} = ≡.refl
-- SetSemMapId {ρ = ρ} (AppT-I {k = k} {φ = φ} Γ∋φ Fs ⊢Fs) {x} = 
--   begin Functor.F₁ (SetEnv.tc ρ φ) (SetSemMapVec ⊢Fs (Category.id SetEnvCat)) x 
--     ≡⟨ Functor.F-resp-≈ (SetEnv.tc ρ φ) (SetSemMapVecId ⊢Fs) ⟩ 
--     Functor.F₁ (SetEnv.tc ρ φ) (Category.id (Sets^ k)) x 
--     ≡⟨ Functor.identity (SetEnv.tc ρ φ) {SetSemObjVec ⊢Fs ρ} {x} ⟩ 
--     x ∎

-- SetSemMapId {ρ = ρ} (AppF-I {k = k} {φ = φ} Φ∋φ Fs ⊢Fs) {x} = 
--   begin  Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs (Category.id SetEnvCat)) x 
--   ≡⟨ Functor.F-resp-≈ (SetEnv.fv ρ φ) (SetSemMapVecId ⊢Fs) ⟩ 
--   Functor.F₁ (SetEnv.fv ρ φ) (Category.id (Sets^ k)) x   
--   ≡⟨ Functor.identity (SetEnv.fv ρ φ) {SetSemObjVec ⊢Fs ρ} {x} ⟩ 
--   x ∎ 


-- SetSemMapId (+-I ⊢F ⊢G) {inj₁ x} = ≡.cong inj₁ (SetSemMapId ⊢F {x})
-- SetSemMapId (+-I ⊢F ⊢G) {inj₂ y} = ≡.cong inj₂ (SetSemMapId ⊢G {y})
-- SetSemMapId (×-I ⊢F ⊢G) {fst , snd} = ×'-cong (SetSemMapId ⊢F {fst}) (SetSemMapId ⊢G {snd})
-- SetSemMapId (Nat-I ⊢F ⊢G) {NatT[ nat ]} = ≡.refl

-- -- goal : T^H0-Map ⊢F ρ (fixHFunc (T^H ⊢F ρ))
-- --       (SetSemMapVec ⊢Gs idρ)
-- --       (NaturalTransformation.η
-- --        (TEnv-Map-η ⊢F ρ ρ idρ (fixHFunc (T^H ⊢F ρ)))
-- --        (SetSemObjVec ⊢Gs ρ)
-- --        (NaturalTransformation.η
-- --         (T^H-Map ⊢F ρ (HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ) (TEnv-Map ⊢F ρ ρ idρ)))
-- --         (SetSemObjVec ⊢Gs ρ) 
-- --           x))
-- --       ≡ x


-- -- TEnv : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
-- --           {φ : FVar k} {αs : Vec (FVar 0) k}
-- --         → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
-- --         → Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])


-- -- START HERE 
-- -- 
-- -- 
-- SetSemMapId {Γ} {Φ} {H} {ρ} (μ-I {k = k} {φ} {αs} F ⊢F Gs ⊢Gs) {hffin x} = {!   !} 
-- {-
--     let Gsid = SetSemMapVec {ρ = ρ} ⊢Gs idSetEnv
--         {-
--         -- 
--         idGs : pointwise-≈ (SetSemMapVec ⊢Gs idSetEnv) (Category.id (Sets^ k))
--         idGs = SetSemMapVecId {Fs = Gs} {ρ} ⊢Gs 
--         -- 
--         μTρF : Functor (Sets^ k) Sets
--         μTρF = fixHFunc (T^H ⊢F ρ)
--         -- 
--         TμTρF : Functor (Sets^ k) Sets
--         TμTρF = Functor.F₀ (T^H ⊢F ρ) μTρF
--         -- 
--         TμTρF-Gsid≈TμTρF-id : Sets Categories.Category.[
--                                 Functor.F₁ TμTρF Gsid
--                                 ≈ Functor.F₁ TμTρF (Category.id (Sets^ k)) ]
--         TμTρF-Gsid≈TμTρF-id = Functor.F-resp-≈ TμTρF idGs
--         -- 
--         TμTρF-id≈id : Sets Categories.Category.[
--                           Functor.F₁ TμTρF (Category.id (Sets^ k)) 
--                           ≈ Category.id Sets ]
--         TμTρF-id≈id = Functor.identity TμTρF {SetSemObjVec ⊢Gs ρ}
--         -- 
--         TEnvFid : NaturalTransformation (Functor.F₀ (TEnv ⊢F) ρ)  (Functor.F₀ (TEnv ⊢F) ρ)
--         TEnvFid = Functor.F₁ (TEnv ⊢F) (idSetEnv {ρ})
--         -- 
--         TEnvFid≈id : [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] Categories.Category.[
--                   Functor.F₁ (TEnv ⊢F) SEC.id ≈ Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] ]
--         TEnvFid≈id = Functor.identity (TEnv ⊢F) {ρ}
--         -- 
--         μTEnvFid : NaturalTransformation (fixHFunc (T^H ⊢F ρ)) (fixHFunc (T^H ⊢F ρ))
--         μTEnvFid = HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ) TEnvFid
--         -- 
--         TEnvFid-TρF = NaturalTransformation.η TEnvFid (fixHFunc (T^H ⊢F ρ))
--         -- 
--         TρFid-Gs-x : Functor.F₀ (Functor.F₀ (T^H ⊢F ρ) (fixHFunc (T^H ⊢F ρ)))
--                                 (SetSemObjVec ⊢Gs ρ) 
--         TρFid-Gs-x = NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid) (SetSemObjVec ⊢Gs ρ) x
--         -- 
--         TEnvFid≈id2 : NaturalTransformation.η TEnvFid-TρF (SetSemObjVec ⊢Gs ρ) TρFid-Gs-x
--                       ≡ TρFid-Gs-x
--         TEnvFid≈id2 = TEnvFid≈id {μTρF} {SetSemObjVec ⊢Gs ρ} {TρFid-Gs-x}
--         -- 
--         TρFμTEnvFid : NaturalTransformation (Functor.F₀ (T^H ⊢F ρ) (fixHFunc (T^H ⊢F ρ))) 
--                                             (Functor.F₀ (T^H ⊢F ρ) (fixHFunc (T^H ⊢F ρ)))
--         TρFμTEnvFid = Functor.F₁ (T^H ⊢F ρ) μTEnvFid 
--         -- 
--         TEnvFid-TρF-Gs-TρFid-Gs-x = NaturalTransformation.η TEnvFid-TρF (SetSemObjVec ⊢Gs ρ) TρFid-Gs-x
--         -- eq : Functor.F₁ TμTρF Gsid (NaturalTransformation.η TEnvFid-TρF (SetSemObjVec ⊢Gs ρ) TρFid-Gs-x)
--         --       ≡ x 
--         -- eq = begin Functor.F₁ TμTρF Gsid (NaturalTransformation.η TEnvFid-TρF (SetSemObjVec ⊢Gs ρ) TρFid-Gs-x) 
--         --           ≡⟨ {!   !} ⟩ 
--         --            NaturalTransformation.η TEnvFid-TρF (SetSemObjVec ⊢Gs ρ) TρFid-Gs-x
--         --           ≡⟨ {!   !} ⟩ 
--         --            TρFid-Gs-x
--         --           ≡⟨ {!   !} ⟩ 
--         --           (x ∎)
--         -}
--         in   {!  !}
--         -- ≡.cong hffin 
--         --   (begin {!    !}
--         --   ≡⟨ {!!} ⟩
--         --     {!!}
--         --   ( {!!} ∎ ))
--         -- ≡.cong hffin eq 
  
--   -}

-- -- {F : Functor (Sets^ k) Sets}
-- -- {Xs : Vec Set k}
-- -- {x : SetSemObj ⊢F
-- --    (Functor.F₀ (extendSetEnv-ρ×As αs)
-- --     ((_A_2112 [ φ :fv= F ]) , Xs))} →
-- -- SetSemMap ⊢F
-- -- (Functor.F₁ (extendSetEnv-ρ×As αs)
-- --  ((extendmorph-η _A_2112 φ idnat ∘SetEnv
-- --    extendmorph-idF _A_2112 _A_2112 idSetEnv)
-- --   , makeIdTuple Xs))
-- -- x
-- -- ≡ x



-- -- Functor.F₁ (Functor.F₀ (T^H ⊢F ρ) (fixHFunc (T^H ⊢F ρ)))
-- --       (SetSemMapVec ⊢Gs idSetEnv)
-- --       (NaturalTransformation.η
-- --        (NaturalTransformation.η (Functor.F₁ (TEnv ⊢F) idSetEnv)
-- --         (fixHFunc (T^H ⊢F ρ)))
-- --        (SetSemObjVec ⊢Gs ρ)
-- --        (NaturalTransformation.η
-- --         (Functor.F₁ (T^H ⊢F ρ) (HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ) (Functor.F₁ (TEnv ⊢F) idSetEnv)))
-- --         (SetSemObjVec ⊢Gs ρ) x))
-- --       ≡ x


-- -- Functor.F₁ TμTρF idGs
-- --       (NaturalTransformation.η
-- --         (NaturalTransformation.η TEnvFid (fixHFunc (T^H ⊢F ρ)))
-- --         (SetSemObjVec ⊢Gs ρ)
-- --       (NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid)
-- --           (SetSemObjVec ⊢Gs ρ) x))
-- -- -- idGs says (SetSemMapVec ⊢Gs idSetEnv) ≈ Category.id (Sets^ k)
-- -- -- F-resp-≈ idGs says (TμTρF Gsid) ≈ (TμTρF Category.id (Sets^ k))
-- -- -- then Functor.identity (TμTρF) says (TμTρF Category.id (Sets^ k)) ≈ (Category.id Sets)
-- -- 
-- -- ≡ (NaturalTransformation.η
-- --         (NaturalTransformation.η TEnvFid (fixHFunc (T^H ⊢F ρ)))
-- --         (SetSemObjVec ⊢Gs ρ)
-- --       (NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid)
-- --           (SetSemObjVec ⊢Gs ρ) x))
-- -- 
-- -- -- use Functor.identity (TEnv ⊢F) {ρ} {μTρF} {SetSemObjVec ⊢Gs ρ} {...}
-- -- 
-- -- ≡ NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid)
-- --           (SetSemObjVec ⊢Gs ρ) x
-- -- ≡ x

-- -- begin 
-- -- Functor.F₁ TμTρF idGs (NaturalTransformation.η TEnvFid-TρF (SetSemObjVec ⊢Gs ρ) TρFid-Gs-x)
-- -- ≡⟨ ? ⟩ 
-- -- x ∎
-- -- -- 


--     -- identity     : ∀ {A} → D [ F₁ (C.id {A}) ≈ D.id ]
--     -- homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
--     --                  D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
--     -- F-resp-≈     : ∀ {A B} {f g : C [ A , B ]} → C [ f ≈ g ] → D [ F₁ f ≈ F₁ g ]




-- -- T^H0-identity : ∀ {k} {Γ} {H} {φ : FVar k} {αs : Vec (FVar 0) k}
-- --                 → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ ⊢ H)
-- --                 → (ρ : SetEnv) (F : Functor (Sets^ k) Sets) 
-- --                 → (As : Vec Set k)
-- --                 → Sets Categories.Category.[ 
-- --                       T^H0-Map ⊢H ρ F {As} {As} (Category.id (Sets^ k))
-- --                       ≈ Category.id Sets ]


--   -- begin  
--   -- HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs (Category.id SetEnvCat {ρ})) x
--   -- ≡⟨ HFix-resp (T^H ⊢F ρ) (SetSemMapVecId ⊢Gs)  ⟩ 
--   -- HFix-fmap (T^H ⊢F ρ) (Category.id (Sets^ k)) x
--   -- ≡⟨ HFix-id ((T^H ⊢F ρ)) ⟩ 
--   -- x ∎ 



-- -----------------------------------------------------
-- -- SetSem functorial action preserves composition 
-- -----------------------------------------------------



-- -- SetSemMapVecHomo : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k}  {ρ} {ρ'} {ρ''}
-- --                   → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
-- --                   → (f : SetEnvMorph ρ ρ')
-- --                   → (g : SetEnvMorph ρ' ρ'')
-- --                   → pointwise-≈ (SetSemMapVec ⊢Fs (g ∘SetEnv f)) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f)
-- SetSemMapVecHomo {Fs = Vec.[]} _ f g = lift Data.Unit.tt
-- SetSemMapVecHomo {Fs = F ∷ Fs} (⊢F , ⊢Fs) f g = SetSemMapHomo ⊢F f g , SetSemMapVecHomo ⊢Fs f g 

-- -- SetSemMapHomo : ∀ {Γ} {Φ} {F}  {ρ} {ρ'} {ρ''}
-- --                 → (⊢F : Γ ≀ Φ ⊢ F)
-- --                 → (f : SetEnvMorph ρ ρ')
-- --                 → (g : SetEnvMorph ρ' ρ'')
-- --                 -- → ∀ {x : Functor.F₀ (SetEnv.fv ρ φ) Xs}
-- --                 → ∀ {x : SetSemObj ⊢F ρ}
-- --                 → SetSemMap ⊢F (g ∘SetEnv f) x ≡ SetSemMap ⊢F g (SetSemMap ⊢F f x)
-- SetSemMapHomo (𝟙-I) f g {x} = ≡.refl
-- -- AppT case 
-- SetSemMapHomo {ρ = ρ1} {ρ2} {ρ3} (AppT-I {k = k} {φ} _ Fs ⊢Fs) f g  {x} = 
--     let gφ-Fsρ3       = NaturalTransformation.η (mkIdTCNT g φ) (SetSemObjVec ⊢Fs ρ3)
--         fφ-Fsρ3       = NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ3)
--         ρ1φ-mapFsg∘f  = Functor.F₁ (SetEnv.tc ρ1 φ) (SetSemMapVec ⊢Fs (g ∘SetEnv f)) 
--         ρ1φ-mapFsg    = Functor.F₁ (SetEnv.tc ρ1 φ) (SetSemMapVec ⊢Fs g)
--         ρ1φ-mapFsf    = Functor.F₁ (SetEnv.tc ρ1 φ) (SetSemMapVec ⊢Fs f)
--         Fsg∘f≈Fsg∘Fsf = SetSemMapVecHomo ⊢Fs f g
--         ρ1φ-resp : Sets Categories.Category.[
--                       ρ1φ-mapFsg∘f
--                       ≈ Functor.F₁ (SetEnv.tc ρ1 φ) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f) ]
--         ρ1φ-resp = Functor.F-resp-≈ (SetEnv.tc ρ1 φ) Fsg∘f≈Fsg∘Fsf
--         -- --
--         ρ1φ-hom : Sets Categories.Category.[
--            Functor.F₁ (SetEnv.tc ρ1 φ) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f )
--            ≈ ρ1φ-mapFsg ∘' ρ1φ-mapFsf ]
--         ρ1φ-hom = Functor.homomorphism (SetEnv.tc ρ1 φ) {f = SetSemMapVec ⊢Fs f} {g = SetSemMapVec ⊢Fs g}
--         -- -- 
--         ρ2φ-mapFsg = Functor.F₁ (SetEnv.tc ρ2 φ) (SetSemMapVec ⊢Fs g)
--         -- 
--         fφ-Fsρ2 = NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ2)
--         -- -- 
--         ρ1φ-mapFsf = Functor.F₁ (SetEnv.tc ρ1 φ) (SetSemMapVec ⊢Fs f) 
--         -- --         
--         fφ-com : ∀ {x} → NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ3)
--                         (Functor.F₁ (SetEnv.tc ρ1 φ) (SetSemMapVec ⊢Fs g) x)
--                         ≡ Functor.F₁ (SetEnv.tc ρ2 φ) (SetSemMapVec ⊢Fs g)
--                         (NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ2) x)
--         fφ-com = NaturalTransformation.commute (mkIdTCNT f φ) {SetSemObjVec ⊢Fs ρ2} {SetSemObjVec ⊢Fs ρ3} (SetSemMapVec ⊢Fs g)

--         g∘fφ-Fsρ3 = NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) φ) (SetSemObjVec ⊢Fs ρ3)

--       in begin
--         g∘fφ-Fsρ3 (ρ1φ-mapFsg∘f x)
--       ≡⟨ mkIdTCNT-comp f g φ ⟩
--         gφ-Fsρ3 (fφ-Fsρ3 (ρ1φ-mapFsg∘f x))
--       ≡⟨ ≡.cong (gφ-Fsρ3 ∘' fφ-Fsρ3)  (≡.trans ρ1φ-resp ρ1φ-hom) ⟩
--         gφ-Fsρ3 (fφ-Fsρ3 (ρ1φ-mapFsg (ρ1φ-mapFsf x)))
--       ≡⟨ ≡.cong gφ-Fsρ3 fφ-com ⟩
--         gφ-Fsρ3 (ρ2φ-mapFsg (fφ-Fsρ2 (ρ1φ-mapFsf x)))
--       ∎

-- -- AppF case: 
-- -- NaturalTransformation.η (SetEnvMorph.fv g φ) (SetSemObjVec ⊢Fs ρ3)
-- --     (NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ3)
-- --         (Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs (g ∘SetEnv f)) x))
-- -- ≡ NaturalTransformation.η (SetEnvMorph.fv g φ) (SetSemObjVec ⊢Fs ρ3)
-- --   (Functor.F₁ (SetEnv.fv ρ2 φ) (SetSemMapVec ⊢Fs g)
-- --      (NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ2)
-- --          (Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs f) x)))
-- SetSemMapHomo {ρ = ρ1} {ρ2} {ρ3} (AppF-I {k = k} {φ = φ} Φ∋φ Fs ⊢Fs) f g   {x} = 
--     let gφ-Fsρ3       = NaturalTransformation.η (SetEnvMorph.fv g φ) (SetSemObjVec ⊢Fs ρ3)
--         fφ-Fsρ3       = NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ3)
--         ρ1φ-mapFsg∘f  = Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs (g ∘SetEnv f)) 
--         ρ1φ-mapFsg    = Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs g)
--         ρ1φ-mapFsf    = Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs f)
--         Fsg∘f≈Fsg∘Fsf = SetSemMapVecHomo ⊢Fs f g
--         --
--         ρ1φ-resp : Sets Categories.Category.[
--                       ρ1φ-mapFsg∘f
--                       ≈ Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f) ]
--         ρ1φ-resp = Functor.F-resp-≈ (SetEnv.fv ρ1 φ) Fsg∘f≈Fsg∘Fsf
--         --
--         ρ1φ-hom : Sets Categories.Category.[
--            Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f )
--            ≈ ρ1φ-mapFsg ∘' ρ1φ-mapFsf ]
--         ρ1φ-hom = Functor.homomorphism (SetEnv.fv ρ1 φ) {f = SetSemMapVec ⊢Fs f} {g = SetSemMapVec ⊢Fs g}
--         -- 
--         ρ2φ-mapFsg = Functor.F₁ (SetEnv.fv ρ2 φ) (SetSemMapVec ⊢Fs g)
--         -- 
--         fφ-Fsρ2 = NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ2)
--         -- 
--         ρ1φ-mapFsf = Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs f) 
--         --         
--         fφ-com : ∀ {x} → NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ3)
--                         (Functor.F₁ (SetEnv.fv ρ1 φ) (SetSemMapVec ⊢Fs g) x)
--                         ≡ Functor.F₁ (SetEnv.fv ρ2 φ) (SetSemMapVec ⊢Fs g)
--                         (NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ2) x)
--         fφ-com = NaturalTransformation.commute (SetEnvMorph.fv f φ) {SetSemObjVec ⊢Fs ρ2} {SetSemObjVec ⊢Fs ρ3} (SetSemMapVec ⊢Fs g)
--       in begin
--         gφ-Fsρ3 (fφ-Fsρ3  (ρ1φ-mapFsg∘f x))
--       ≡⟨ ≡.cong (gφ-Fsρ3 ∘' fφ-Fsρ3) (≡.trans ρ1φ-resp ρ1φ-hom) ⟩
--         gφ-Fsρ3 (fφ-Fsρ3 (ρ1φ-mapFsg (ρ1φ-mapFsf x)))
--       ≡⟨ ≡.cong gφ-Fsρ3 fφ-com ⟩
--         gφ-Fsρ3 (ρ2φ-mapFsg (fφ-Fsρ2 (ρ1φ-mapFsf x)))
--       ∎ 

-- SetSemMapHomo (+-I ⊢F ⊢G) f g {inj₁ x} = ≡.cong inj₁ (SetSemMapHomo ⊢F f g )
-- SetSemMapHomo (+-I ⊢F ⊢G) f g {inj₂ y} = ≡.cong inj₂ (SetSemMapHomo ⊢G f g )
-- SetSemMapHomo (×-I ⊢F ⊢G) f g {fst , snd} = ×'-cong (SetSemMapHomo  ⊢F f g ) (SetSemMapHomo ⊢G f g )
-- SetSemMapHomo {ρ = ρ1} {ρ2} {ρ3} (Nat-I {k = k} {αs = αs} ⊢F ⊢G) f g {NatT[ nat ]} = 
--       ≡.cong NatT[_] (make-NT-eq-comp (nat-extend-lem f ⊢F) (nat-extend-lem f ⊢G) 
--                                       (nat-extend-lem g ⊢F) (nat-extend-lem g ⊢G) 
--                                       (nat-extend-lem (g ∘SetEnv f) ⊢F) (nat-extend-lem (g ∘SetEnv f) ⊢G) nat)


-- -- goal : 
-- -- HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs (g ∘SetEnv f)) x ≡
-- -- HFix-fmap (T^H ⊢F ρ') (SetSemMapVec ⊢Gs g) (HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs f) x)
-- SetSemMapHomo (μ-I F ⊢F Gs ⊢Gs) f g {hffin x} = {!   !} 


-- -- SetSemMapVecF-resp : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} {ρ} {ρ'}
-- --                   {f g : SetEnvMorph ρ ρ'}
-- --                   (f≈g : SetEnvCat Categories.Category.[ f ≈ g ]) 
-- --                   → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
-- --                   → (Sets^ k) Categories.Category.[ SetSemMapVec ⊢Fs f ≈ SetSemMapVec ⊢Fs g ]
-- SetSemMapVecF-resp {Fs = []}     f≈g Data.Unit.tt   = lift Data.Unit.tt
-- SetSemMapVecF-resp {Fs = F ∷ Fs} f≈g (⊢F , ⊢Fs)     = (SetSemMapF-resp ⊢F f≈g) , (SetSemMapVecF-resp f≈g ⊢Fs)

-- -- SetSemMapF-resp : ∀ {Γ} {Φ} {F} (⊢F : Γ ≀ Φ ⊢ F) {ρ} {ρ'}
-- --                   {f g : SetEnvMorph ρ ρ'}
-- --                   (f≈g : SetEnvCat Categories.Category.[ f ≈ g ]) 
-- --                   → Sets Categories.Category.[ SetSemMap ⊢F f ≈ SetSemMap ⊢F g ]
-- SetSemMapF-resp 𝟙-I f≈g = ≡.refl
-- SetSemMapF-resp (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) {ρ} {ρ'} {f} {g} f≈g {x} = 
--       let fφ≈gφ   = mkIdTCNT-eq f g φ {SetSemObjVec ⊢Fs ρ'} 
--           fφ-Fsρ' = NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ')
--           gφ-Fsρ' = NaturalTransformation.η (mkIdTCNT g φ) (SetSemObjVec ⊢Fs ρ')
--         in begin
--           fφ-Fsρ' (Functor.F₁ (SetEnv.tc ρ φ) (SetSemMapVec ⊢Fs f) x)
--         ≡⟨ ≡.cong fφ-Fsρ' (Functor.F-resp-≈ (SetEnv.tc ρ φ) (SetSemMapVecF-resp f≈g ⊢Fs)) ⟩
--           fφ-Fsρ' (Functor.F₁ (SetEnv.tc ρ φ) (SetSemMapVec ⊢Fs g) x)
--         ≡⟨ fφ≈gφ ⟩
--           gφ-Fsρ' (Functor.F₁ (SetEnv.tc ρ φ) (SetSemMapVec ⊢Fs g) x)
--         ∎



--       -- NaturalTransformation.η (SetEnvMorph.fv f φ)
--       -- (SetSemObjVec ⊢Fs ρ')
--       -- (Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs f) x)
--       -- ≡
--       -- NaturalTransformation.η (SetEnvMorph.fv g φ) (SetSemObjVec ⊢Fs ρ')
--       -- (Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs g) x)
-- SetSemMapF-resp (AppF-I {φ = φ} Φ∋φ Fs ⊢Fs) {ρ} {ρ'} {f} {g} f≈g {x} = 
--   let fφ-Fsρ' = NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ')
--       gφ-Fsρ' = NaturalTransformation.η (SetEnvMorph.fv g φ) (SetSemObjVec ⊢Fs ρ')
--     in begin
--         fφ-Fsρ' (Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs f) x)
--       ≡⟨ ≡.cong fφ-Fsρ' (Functor.F-resp-≈ (SetEnv.fv ρ φ) (SetSemMapVecF-resp f≈g ⊢Fs)) ⟩ 
--         fφ-Fsρ' (Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs g) x)
--       ≡⟨ f≈g ⟩
--         gφ-Fsρ' (Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs g) x)
--       ∎

-- SetSemMapF-resp (+-I ⊢F ⊢G) f≈g {inj₁ x} = ≡.cong inj₁ (SetSemMapF-resp ⊢F f≈g)
-- SetSemMapF-resp (+-I ⊢F ⊢G) f≈g {inj₂ y} = ≡.cong inj₂ (SetSemMapF-resp ⊢G f≈g)
-- SetSemMapF-resp (×-I ⊢F ⊢G) f≈g {x , y} = ×'-cong (SetSemMapF-resp ⊢F f≈g) (SetSemMapF-resp ⊢G f≈g)
-- SetSemMapF-resp (Nat-I ⊢F ⊢G) {ρ} {ρ'} {f} {g} f≈g {NatT[ nat ]} = 
--   ≡.cong NatT[_] (make-NT-eq-lem (nat-extend-lem f ⊢F) (nat-extend-lem g ⊢F) (nat-extend-lem f ⊢G) (nat-extend-lem g ⊢G) nat)


-- {-
-- Functor.F₁ (Functor.F₀ (T^H ⊢F ρ') (fixHFunc (T^H ⊢F ρ')))
--       (SetSemMapVec ⊢Gs f)

--       (NaturalTransformation.η
--        (NaturalTransformation.η (Functor.F₁ (TEnv ⊢F) f) (fixHFunc (T^H ⊢F ρ')))
--        (SetSemObjVec ⊢Gs ρ)

--        (NaturalTransformation.η
--         (Functor.F₁ (T^H ⊢F ρ) (HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ') (Functor.F₁ (TEnv ⊢F) f)))
--         (SetSemObjVec ⊢Gs ρ) x))
--       ≡
--       Functor.F₁ (Functor.F₀ (T^H ⊢F ρ') (fixHFunc (T^H ⊢F ρ')))
--       (SetSemMapVec ⊢Gs g) -- f to g (F-resp-≈ )

--       (NaturalTransformation.η
--        (NaturalTransformation.η (Functor.F₁ (TEnv ⊢F) g) (fixHFunc (T^H ⊢F ρ')))
--                                               -- f to g
--        (SetSemObjVec ⊢Gs ρ)

--        (NaturalTransformation.η
--         (Functor.F₁ (T^H ⊢F ρ) (HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ') (Functor.F₁ (TEnv ⊢F) g))) -- f to g
--                                   -- need HFix-hmap-F-resp
--         (SetSemObjVec ⊢Gs ρ) x))
-- -}
-- SetSemMapF-resp (μ-I {k = k} F ⊢F Gs ⊢Gs) {ρ} {ρ'} {f} {g} f≈g {hffin x} = {!   !}
-- {-}
-- -- THIS DEFINITION TYPE CHECKS
--     let TFρ  : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
--         TFρ        = T^H ⊢F ρ  
--         TFρ' : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
--         TFρ'       = T^H ⊢F ρ' 
--         TFρ'μTFρ' : Functor (Sets^ k) Sets
--         TFρ'μTFρ'  = Functor.F₀ TFρ' (fixHFunc TFρ')
--         Gsf : VecFSpace (SetSemObjVec ⊢Gs ρ) (SetSemObjVec ⊢Gs ρ') 
--         Gsf        = SetSemMapVec ⊢Gs f 
--         Gsg : VecFSpace (SetSemObjVec ⊢Gs ρ) (SetSemObjVec ⊢Gs ρ') 
--         Gsg        = SetSemMapVec ⊢Gs g
--         --
--         TFf : NaturalTransformation (Functor.F₀ (TEnv ⊢F) ρ) (Functor.F₀ (TEnv ⊢F) ρ')
--         TFf           = Functor.F₁ (TEnv ⊢F) f 
--         TFf-μTFρ' : NaturalTransformation (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ) (fixHFunc TFρ')) (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ') (fixHFunc TFρ'))
--         TFf-μTFρ'     = NaturalTransformation.η TFf (fixHFunc TFρ')
--         TFf-μTFρ'-Gsρ : (Functor.F₀ (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ) (fixHFunc TFρ')) (SetSemObjVec ⊢Gs ρ)) → (Functor.F₀ (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ') (fixHFunc TFρ')) (SetSemObjVec ⊢Gs ρ))
--         TFf-μTFρ'-Gsρ = NaturalTransformation.η TFf-μTFρ' (SetSemObjVec ⊢Gs ρ)
--         -- 
--         TFg : NaturalTransformation (Functor.F₀ (TEnv ⊢F) ρ) (Functor.F₀ (TEnv ⊢F) ρ')
--         TFg           = Functor.F₁ (TEnv ⊢F) g 
--         TFg-μTFρ' : NaturalTransformation (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ) (fixHFunc TFρ')) (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ') (fixHFunc TFρ'))
--         TFg-μTFρ'     = NaturalTransformation.η TFg (fixHFunc TFρ')
--         TFg-μTFρ'-Gsρ : (Functor.F₀ (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ) (fixHFunc TFρ')) (SetSemObjVec ⊢Gs ρ)) → (Functor.F₀ (Functor.F₀ (Functor.F₀ (TEnv ⊢F) ρ') (fixHFunc TFρ')) (SetSemObjVec ⊢Gs ρ))
--         TFg-μTFρ'-Gsρ = NaturalTransformation.η TFg-μTFρ' (SetSemObjVec ⊢Gs ρ)
--         --
--         TFf≈TFg : [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] Categories.Category.[ Functor.F₁ (TEnv ⊢F) f ≈ Functor.F₁ (TEnv ⊢F) g ]
--         TFf≈TFg =  Functor.F-resp-≈ (TEnv ⊢F) {f = f} {g = g} f≈g  
--         -- TFρ-μTFf-Gsρ≈TFρ-μTFg-Gsρ = Functor.F-resp-≈ TFρ (HFix-hmap-F-resp TFρ TFρ' TFf TFg TFf≈TFg )
--         -- 
--         μTFf : NaturalTransformation (fixHFunc TFρ) (fixHFunc TFρ') 
--         μTFf = HFix-hmap TFρ TFρ' TFf 
--         TFρ-μTFf : NaturalTransformation (Functor.F₀ TFρ (fixHFunc TFρ)) (Functor.F₀ TFρ (fixHFunc TFρ'))
--         TFρ-μTFf = Functor.F₁ TFρ μTFf 
--         TFρ-μTFf-Gsρ : Functor.F₀ (Functor.F₀ TFρ (fixHFunc TFρ)) (SetSemObjVec ⊢Gs ρ) →  Functor.F₀ (Functor.F₀ TFρ (fixHFunc TFρ')) (SetSemObjVec ⊢Gs ρ) 
--         TFρ-μTFf-Gsρ = NaturalTransformation.η TFρ-μTFf (SetSemObjVec ⊢Gs ρ)
--         -- 
--         μTFg : NaturalTransformation (fixHFunc TFρ) (fixHFunc TFρ') 
--         μTFg = HFix-hmap TFρ TFρ' TFg
--         TFρ-μTFg : NaturalTransformation (Functor.F₀ TFρ (fixHFunc TFρ)) (Functor.F₀ TFρ (fixHFunc TFρ'))
--         TFρ-μTFg = Functor.F₁ TFρ μTFg 
--         TFρ-μTFg-Gsρ : Functor.F₀ (Functor.F₀ TFρ (fixHFunc TFρ)) (SetSemObjVec ⊢Gs ρ) →  Functor.F₀ (Functor.F₀ TFρ (fixHFunc TFρ')) (SetSemObjVec ⊢Gs ρ) 
--         TFρ-μTFg-Gsρ = NaturalTransformation.η TFρ-μTFg (SetSemObjVec ⊢Gs ρ)

--       in ≡.cong hffin 
--         (begin 
--         Functor.F₁ TFρ'μTFρ' Gsf (TFf-μTFρ'-Gsρ (TFρ-μTFf-Gsρ x))
--         ≡⟨ ≡.cong  (Functor.F₁ TFρ'μTFρ' Gsf ∘' TFf-μTFρ'-Gsρ)  (Functor.F-resp-≈ TFρ (HFix-hmap-F-resp TFρ TFρ' TFf TFg TFf≈TFg )) ⟩ 
--         Functor.F₁ TFρ'μTFρ' Gsf (TFf-μTFρ'-Gsρ (TFρ-μTFg-Gsρ x))
--         ≡⟨ ≡.cong  (Functor.F₁ TFρ'μTFρ' Gsf)  TFf≈TFg ⟩ 
--         Functor.F₁ TFρ'μTFρ' Gsf (TFg-μTFρ'-Gsρ (TFρ-μTFg-Gsρ x))
--         ≡⟨ Functor.F-resp-≈ TFρ'μTFρ' (SetSemMapVecF-resp f≈g ⊢Gs) ⟩ 
--         Functor.F₁ TFρ'μTFρ' Gsg (TFg-μTFρ'-Gsρ (TFρ-μTFg-Gsρ x))
--         ∎)
--   -}


-- -- SetSem : ∀ (Γ : TCCtx) → (Φ : FunCtx) → (F : TypeExpr)
-- --             → Γ ≀ Φ ⊢ F
-- --             → Functor SetEnvCat Sets
-- SetSem Γ Φ F ⊢F = record
--   { F₀ = SetSemObj ⊢F   -- DONE 
--   ; F₁ = λ f →  SetSemMap ⊢F f  -- DONE 
--   ; identity = λ {ρ} → SetSemMapId {ρ = ρ} ⊢F -- DONE except Mu case 
--   ; homomorphism = λ {ρ} {ρ'} {ρ''} {f} {g} → SetSemMapHomo ⊢F f g -- Done trivial cases 
--   ; F-resp-≈ = λ {ρ ρ'} {f g} f≈g → SetSemMapF-resp ⊢F f≈g
--   } 


SetSemVec : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx}
              → {Fs : Vec TypeExpr k}
              → foreach (λ F → Γ ≀ Φ ⊢ F) Fs
              → Functor SetEnvCat (Sets^ k)
SetSemVec {zero} {Γ} {Φ} {[]} Data.Unit.tt = ConstF []
SetSemVec {suc k} {Γ} {Φ} {F ∷ Fs} (⊢F , ⊢Fs) = 
  let SetSemF×SetSemFs : Functor SetEnvCat (Product Sets (Sets^ k))
      SetSemF×SetSemFs = SetSem Γ Φ F ⊢F ※ SetSemVec ⊢Fs
    in Sets^cons k ∘F SetSemF×SetSemFs


VarSem-FV : ∀ {k : ℕ} (φ : FVar k) → Functor SetEnvCat [Sets^ k ,Sets]
VarSem-FV φ = record
  { F₀ = λ ρ → SetEnv.fv ρ φ 
  ; F₁ = λ f → SetEnvMorph.fv f φ
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≈ = λ f≈g → f≈g
  } 

VarSem-TC : ∀ {k : ℕ} (φ : TCVar k) → Functor SetEnvCat [Sets^ k ,Sets]
VarSem-TC φ = record
  { F₀ = λ ρ → SetEnv.tc ρ φ 
  ; F₁ = λ f → mkIdTCNT f φ 
  ; identity = ≡.refl
  ; homomorphism = λ { {ρ1} {ρ2} {ρ3} {f} {g} → mkIdTCNT-comp f g φ }
  ; F-resp-≈ = λ { {ρ} {ρ'} {f} {g} f≈g → mkIdTCNT-eq f g φ } 
  } 

-- record NatType {n : ℕ} {Γ : TCCtx} {F G : TypeExpr} {αs : Vec (FVar 0) n} (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G) (ρ : SetEnv) : Set 
NatTypeSem : ∀ {n : ℕ} {Γ : TCCtx} {F G : TypeExpr} {αs : Vec (FVar 0) n} (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G) 
          → Functor SetEnvCat Sets
NatTypeSem ⊢F ⊢G = record
  { F₀ = λ ρ → NatType ⊢F ⊢G (NatEnv ρ)
  ; F₁ = λ { f NatT[ nat ] → NatT[ make-NT-eq (nat-extend-lem f ⊢F) (nat-extend-lem f ⊢G) nat ] } 
  ; identity = ≡.refl
  ; homomorphism = λ { {ρ1} {ρ2} {ρ3} {f} {g} {NatT[ nat ]}
       → ≡.cong NatT[_] (make-NT-eq-comp (nat-extend-lem f ⊢F) (nat-extend-lem f ⊢G) 
                                         (nat-extend-lem g ⊢F) (nat-extend-lem g ⊢G) 
                                         (nat-extend-lem (g ∘SetEnv f) ⊢F) (nat-extend-lem (g ∘SetEnv f) ⊢G) nat)  }

  ; F-resp-≈ = λ { {ρ} {ρ'} {f} {g} f≈g {NatT[ nat ]} → ≡.cong NatT[_] (make-NT-eq-lem (nat-extend-lem f ⊢F) (nat-extend-lem g ⊢F) (nat-extend-lem f ⊢G) (nat-extend-lem g ⊢G) nat)  }
  } 
  


SetSem Γ Φ 𝟘 ⊢F = ConstF ⊥'
SetSem Γ Φ 𝟙 ⊢F = ConstF ⊤
SetSem Γ Φ Nat^ βs [ F , G ] (Nat-I ⊢F ⊢G)  = NatTypeSem ⊢F ⊢G
SetSem Γ Φ (F + G) (+-I ⊢F ⊢G) = SetSum ∘F (SetSem Γ Φ F ⊢F ※ SetSem Γ Φ G ⊢G)
SetSem Γ Φ (F × G) (×-I ⊢F ⊢G) = SetProd ∘F (SetSem Γ Φ F ⊢F ※ SetSem Γ Φ G ⊢G)
SetSem Γ Φ AppT φ [ Gs ] (AppT-I Γ∋φ Gs ⊢Gs) = 
  let SetSemGs = SetSemVec ⊢Gs 
    in eval ∘F (VarSem-TC φ ※ SetSemGs)
SetSem Γ Φ AppF φ [ Gs ] (AppF-I Φ∋φ Gs ⊢Gs) = 
  let SetSemGs = SetSemVec ⊢Gs 
    in eval ∘F (VarSem-FV φ ※ SetSemGs)
SetSem Γ Φ (μ φ [λ αs , F ] Ks) (μ-I {k = k} .F ⊢F .Ks ⊢Ks) = 
  let SetSemKs : Functor SetEnvCat (Sets^ k)
      SetSemKs = SetSemVec ⊢Ks
      fixT : Functor SetEnvCat [Sets^ k ,Sets]
      fixT = fixH ∘F TEnv ⊢F
    in eval ∘F (fixT ※ SetSemKs)


-------------------------------------------------------------------------
-- END MUTUAL 
---------------------------------------------------------------------------








-- extendSetEnv-αs : ∀ {k} → (αs : Vec (FVar 0) k) → SetEnv
--                 → Functor (Sets^ k) SetEnvCat
-- extendSetEnv-αs αs ρ = Functor.F₀ (curry.F₀ (extendSetEnv-ρ×As αs)) ρ 
-- 
-- extendSetEnv-ρ×As : ∀ {k} → (αs : Vec (FVar 0) k) 
--                 → Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
-- extendSetEnv-ρ×As [] = πˡ 
-- extendSetEnv-ρ×As {suc k} (α ∷ αs) = ...


-- -- need lemma that extendSetSem-αs ρ ⊢F = extendSetSem-αs ρ' ⊢F whenever Φ = ∅ 






-- this is for 'naive' definition of NatType that doesn't 
-- ignore the functorial part of ρ 
{- 
mutual 
  extendSetSem-Nat-lem : ∀ {k} {Γ} {F} → (αs : Vec (FVar 0) k) 
                        → {ρ ρ' : SetEnv}
                        → SetEnvMorph ρ ρ'
                        → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F)
                        → extendSetSem-αs αs ρ ⊢F 
                          ≡ extendSetSem-αs αs ρ' ⊢F 
  --                          
  -- λ ⊢H → SetSem _Γ_1848 _Φ_1849 _H_1850 ⊢H ∘F
  -- Categories.Category.Product.πˡ ∘F
  -- (Categories.Functor.Construction.Constant.const ρ
  --  Categories.Category.Product.※ Categories.Functor.id)


  -- extendSetSem-αs [] ρ ⊢F ≡ extendSetSem-αs [] ρ' ⊢F
  -- normalizes to 
  -- 
  -- SetSem Γ ∅ F ⊢F ∘F
  -- Categories.Category.Product.πˡ ∘F
  -- (Categories.Functor.Construction.Constant.const ρ
  --  Categories.Category.Product.※ Categories.Functor.id)
  -- ≡
  -- SetSem Γ ∅ F ⊢F ∘F
  -- Categories.Category.Product.πˡ ∘F
  -- (Categories.Functor.Construction.Constant.const ρ'
  --  Categories.Category.Product.※ Categories.Functor.id)

  -- -- WAIT can't do this by induction on αs because ⊢F ... 
  extendSetSem-Nat-lem {k} {Γ} {F} αs {ρ} {ρ'} f ⊢F = {!   !} 


  -- -- WAIT can't do this by induction on αs because ⊢F ... 
  extendSetSem-Nat-lem-ptwise : ∀ {k} {Γ} {F} → (αs : Vec (FVar 0) k) 
                        → (ρ ρ' : SetEnv)
                        → SetEnvMorph ρ ρ'
                        → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F)
                        → (As : Vec Set k)
                        → Functor.F₀ (extendSetSem-αs αs ρ ⊢F) As
                          ≡ Functor.F₀ (extendSetSem-αs αs ρ' ⊢F) As
  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f 𝟘-I As = ≡.refl
  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f 𝟙-I As = ≡.refl
  -- Functor.F₀ (SetEnv.tc (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As)) φ)
  -- (SetSemObjVec ⊢Fs (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As)))
  -- ≡ Functor.F₀ (SetEnv.tc (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ' , As)) φ)
  -- (SetSemObjVec ⊢Fs (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ' , As)))
  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f (AppT-I Γ∋φ Fs ⊢Fs) As = {!   !}
  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f (AppF-I Φ∋φ Fs ⊢Fs) As = {!   !}
  --   (SetSemObj ⊢F (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As)) ⊎
  --    SetSemObj ⊢G (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As)))
  -- ≡ (SetSemObj ⊢F (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ' , As)) ⊎
  --    SetSemObj ⊢G (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ' , As)))
  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f (+-I ⊢F ⊢G) As = ≡.cong₂ _⊎_  (extendSetSem-Nat-lem-ptwise αs ρ ρ' f ⊢F As) (extendSetSem-Nat-lem-ptwise αs ρ ρ' f ⊢G As)
  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f (×-I ⊢F ⊢G) As = ≡.cong₂ _×'_ (extendSetSem-Nat-lem-ptwise αs ρ ρ' f ⊢F As) (extendSetSem-Nat-lem-ptwise αs ρ ρ' f ⊢G As)
  -- NatType ⊢F ⊢G (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As)) ≡
  -- NatType ⊢F ⊢G (Functor.F₀ (extendSetEnv-ρ×As αs) (ρ' , As))
  -- 
  -- sub goal : Functor.₀ (extendSetEnv-αs αs ρ) As ≡ Functor.₀ (extendSetEnv-αs αs ρ') As
  -- -- but this isn't true... 
  -- -- ρ [ αs := As ] is not the same as ρ' [ αs := As ] in general.. 

  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f (Nat-I ⊢F ⊢G) As = {!   !}
  extendSetSem-Nat-lem-ptwise {k} {Γ} αs ρ ρ' f (μ-I F ⊢F Gs ⊢Gs) As = {!   !}


  extendSetSem-TC-Vec-lem : ∀ {k} {Γ} {Fs : Vec TypeExpr k} {ρ ρ' : SetEnv}
                        → SetEnvMorph ρ ρ'
                        → (⊢Fs : foreach (λ F → Γ ≀ ∅ ⊢ F) Fs)
                        → SetSemObjVec ⊢Fs ρ ≡ SetSemObjVec ⊢Fs ρ'
  extendSetSem-TC-Vec-lem {Fs = []} f ⊢Fs = ≡.refl
  extendSetSem-TC-Vec-lem {Fs = F ∷ Fs} f (⊢F , ⊢Fs) = 
    cong-both (≡.cong (_∷_) (extendSetSem-TC-lem f ⊢F)) (extendSetSem-TC-Vec-lem f ⊢Fs) 

  extendSetSem-TC-lem : ∀ {Γ} {F} {ρ ρ' : SetEnv}
                        → SetEnvMorph ρ ρ'
                        → (⊢F : Γ ≀ ∅ ⊢ F)
                        → SetSemObj ⊢F ρ ≡ SetSemObj ⊢F ρ'
  extendSetSem-TC-lem f 𝟘-I = ≡.refl
  extendSetSem-TC-lem f 𝟙-I = ≡.refl
  extendSetSem-TC-lem f (AppT-I {k = k} {φ} Γ∋φ Fs ⊢Fs) = 
  -- Functor.F₀ (SetEnv.tc ρ φ) (SetSemObjVec ⊢Fs ρ) ≡
  --       Functor.F₀ (SetEnv.tc ρ' φ) (SetSemObjVec ⊢Fs ρ')
    let ρφ≡ρ'φ = eqTC-ext f φ
      in ≡.cong₂ Functor.F₀ ρφ≡ρ'φ (extendSetSem-TC-Vec-lem f ⊢Fs)
--       cong-both (≡.cong Functor.F₀ ρφ≡ρ'φ) (extendSetSem-TC-Vec-lem f ⊢Fs)
      -- in cong-both (≡.cong Functor.F₀ ρφ≡ρ'φ) (extendSetSem-TC-Vec-lem f ⊢Fs)

  -- 
  -- no case for AppF because FunCtx is empty 
  -- 
  extendSetSem-TC-lem f (+-I ⊢F ⊢G) = ≡.cong₂ _⊎_ (extendSetSem-TC-lem f ⊢F) (extendSetSem-TC-lem f ⊢G)
  extendSetSem-TC-lem f (×-I ⊢F ⊢G) = ≡.cong₂ _×'_ (extendSetSem-TC-lem f ⊢F) (extendSetSem-TC-lem f ⊢G)

    -- NatType ... where 
    -- nat : NaturalTransformation (extendSetSem-αs αs ρ ⊢F) (extendSetSem-αs αs ρ ⊢G)
    -- 
    -- WTS NatType ⊢F ⊢G ρ ≡ NatType ⊢F ⊢G ρ'
  extendSetSem-TC-lem {ρ = ρ} {ρ'} f (Nat-I ⊢F ⊢G) = {!   !}

  -- goal: Functor.F₀ (fixHFunc (T^H ⊢F ρ)) (SetSemObjVec ⊢Gs ρ) 
  --     ≡ Functor.F₀ (fixHFunc (T^H ⊢F ρ')) (SetSemObjVec ⊢Gs ρ')
  extendSetSem-TC-lem {ρ = ρ} {ρ'} f (μ-I F ⊢F Gs ⊢Gs) = 
      let Gsρ≡Gsρ′ = extendSetSem-TC-Vec-lem f ⊢Gs
          TρF≡Tρ′F = {!   !} 
          μTρF≡μTρ′F = ≡.cong fixHFunc TρF≡Tρ′F 
        -- in ≡.cong₂ Functor.F₀ μTρF≡μTρ′F Gsρ≡Gsρ′ 
        in {!   !} 

  extendSetSem-TC-T-lem : ∀ {k} {Γ} {F} {φ : FVar k} {αs : Vec (FVar 0) k} 
                        → {ρ ρ' : SetEnv}
                        → SetEnvMorph ρ ρ'
                        → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ ⊢ F)
                        → (As : Vec Set k)
                        → Functor.F₀ (fixHFunc (T^H ⊢F ρ)) As
                          ≡ Functor.F₀ (fixHFunc (T^H ⊢F ρ')) As
  extendSetSem-TC-T-lem  {φ = φ} {αs} {ρ} {ρ'} f ⊢F As = {!   !}  
  -}

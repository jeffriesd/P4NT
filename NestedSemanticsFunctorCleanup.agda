module NestedSemanticsFunctorCleanup where
open import NestedSyntax6NoStrings using (_≀_⊢_ ; TypeContext ; _∋_ ; AppF0 ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; ∅ ; _,++_ ; _,,_)
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open _∋_ 

-- open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (if_then_else_; true; false)
open import Categories.Category using (Category)
open import Categories.Category.Product using (Product)
open import Categories.Functor using (Functor ; _∘F_)
open import Categories.Category.Construction.Functors using (Functors ; module curry)
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
open import EnvironmentsInnerRecCleanup
open import HFixFunctorLib 



-- mutual

  -------------------------------------------------------
  -- SetSem functor -- 
  -------------------------------------------------------
  
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
  field
    nat : NaturalTransformation (extendSetSem-αs αs ρ ⊢F) (extendSetSem-αs αs ρ ⊢G)

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
TEnvProd {k} {Γ} {H} {φ} {αs} ⊢H = SetSem Γ ((∅ ,++ αs) ,, φ) H ⊢H ∘F extendTEnv φ αs



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

-- SetSemObjVec : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx}
--               → {Fs : Vec TypeExpr k}
--               → foreach (λ F → Γ ≀ Φ ⊢ F) Fs
--               → SetEnv 
--               → Vec Set k
-- -- SetSemObjVec Fs ⊢Fs ρt ρf = vmap (λ x₁ → SetSemObj (proj₂ x₁) ρt ρf) (foreach-toVec ⊢Fs) 
SetSemObjVec {Fs = Vec.[]} _ _ = Vec.[]
SetSemObjVec {Fs = F ∷ Fs} (⊢F , ⊢Fs) ρ = (SetSemObj ⊢F ρ) ∷ SetSemObjVec ⊢Fs ρ




-- SetSemObj : ∀ {Γ : TCCtx} {Φ : FunCtx} {F : TypeExpr}
--             → Γ ≀ Φ ⊢ F
--             → SetEnv 
--             → Set
SetSemObj 𝟘-I _   = ⊥'
SetSemObj 𝟙-I _   = ⊤
SetSemObj (+-I ⊢F ⊢G) ρ  = SetSemObj ⊢F ρ ⊎ SetSemObj ⊢G ρ 
SetSemObj (×-I ⊢F ⊢G) ρ  = SetSemObj ⊢F ρ ×' SetSemObj ⊢G ρ 
SetSemObj (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) ρ  = Functor.F₀ (SetEnv.tc ρ φ) (SetSemObjVec ⊢Fs ρ )
SetSemObj (AppF-I {φ = φ} Φ∋φ Fs ⊢Fs) ρ  = Functor.F₀ (SetEnv.fv ρ φ) (SetSemObjVec ⊢Fs ρ )
SetSemObj (Nat-I ⊢F ⊢G) ρ  = NatType ⊢F ⊢G ρ
-- placeholder until relational semantics is defined.. 
    
-- SetSemObj (μ-I {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) ρ  = HFixFunctor (T^H ⊢F ρ) (SetSemObjVec ⊢Gs ρ)
SetSemObj (μ-I {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) ρ  = Functor.F₀ (fixHFunc (T^H ⊢F ρ)) (SetSemObjVec ⊢Gs ρ)




-----------------------------------------------------
-- SetSem functorial action
-----------------------------------------------------


-- -- mapping of SetSemMap over vectors 
-- SetSemMapVec : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} {ρ ρ' : SetEnv}
--               {Fs : Vec TypeExpr k}
--               → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
--               → SetEnvMorph ρ ρ'
--               → VecFSpace (SetSemObjVec ⊢Fs ρ) (SetSemObjVec ⊢Fs ρ')
SetSemMapVec {Fs = Vec.[]} Data.Unit.tt f = fnil
SetSemMapVec {Fs = F ∷ Fs} (⊢F , ⊢Fs) f = fcons (SetSemMap ⊢F f) (SetSemMapVec ⊢Fs f) 

-- SetSemMap : ∀ {Γ} {Φ} {F} (⊢F : Γ ≀ Φ ⊢ F) {ρ ρ' : SetEnv}
--               → (f : SetEnvMorph ρ ρ')
--               → SetSemObj ⊢F ρ 
--               → SetSemObj ⊢F ρ'
SetSemMap 𝟙-I {ρ} {ρ'} f Fρ = Data.Unit.tt
SetSemMap (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) {ρ} {ρ'} f Fρ = 
  Functor.F₁ (SetEnv.tc ρ' φ) (SetSemMapVec ⊢Fs f) 
    (NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec ⊢Fs ρ) Fρ)
    -- -- equivalently, by naturality 
    -- NaturalTransformation.η (mkIdTCNT f φ) (SetSemObjVec Fs ⊢Fs ρ') 
    --     (Functor.F₁ (SetEnv.tc ρ φ) (SetSemMapVec ⊢Fs f) Fρ)
SetSemMap (AppF-I {φ = φ} Ψ∋φ Fs ⊢Fs) {ρ} {ρ'} f Fρ = 
  NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ') 
      (Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs f) Fρ)
    -- -- equivalently, by naturality 
    -- Functor.F₁ (SetEnv.fv ρ' φ) (SetSemMapVec ⊢Fs f) 
    --   (NaturalTransformation.η (SetEnvMorph.fv f φ) (SetSemObjVec ⊢Fs ρ) Fρ)
SetSemMap (+-I ⊢F ⊢G) {ρ} {ρ'} f (inj₁ x) = inj₁ (SetSemMap ⊢F f x)
SetSemMap (+-I ⊢F ⊢G) {ρ} {ρ'} f (inj₂ y) = inj₂ (SetSemMap ⊢G f y)
SetSemMap (×-I ⊢F ⊢G) {ρ} {ρ'} f (fst , snd) = (SetSemMap ⊢F f fst) , (SetSemMap ⊢G f snd)
-- goal : NaturalTransformation (extendSetSem-αs αs ρ' ⊢F) (extendSetSem-αs αs ρ' ⊢G) 
-- -- need lemma that extendSetSem-αs ρ ⊢F = extendSetSem-αs ρ' ⊢F whenever Φ = ∅ 
-- 
-- TODO ?? - do we need 
SetSemMap (Nat-I {αs = αs} ⊢F ⊢G) {ρ} {ρ'} record { eqTC = eqTC ; fv = fv } record { nat = nat } = record { nat = {!   !} } 
-- 
-- naturality square 
-- have : HFixFunctor (T^H ⊢F ρ)  (SetSemObjVec ⊢Gs ρ)
-- goal : HFixFunctor (T^H ⊢F ρ') (SetSemObjVec ⊢Gs ρ')
SetSemMap (μ-I F ⊢F Gs ⊢Gs) {ρ} {ρ'} f Fρ = 
    let μT^Hρ'Gf     = HFix-fmap (T^H ⊢F ρ') (SetSemMapVec ⊢Gs f) 
        T^Hρ→T^Hρ'   = Functor.F₁ (TEnv ⊢F) f 
        μT^Hρ→μT^Hρ' = HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ') T^Hρ→T^Hρ'
        in μT^Hρ'Gf (NaturalTransformation.η μT^Hρ→μT^Hρ' (SetSemObjVec ⊢Gs ρ) Fρ)
        -- -- equivalently, by naturality 
        -- μT^HρGf       = HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs f) 
        -- in NaturalTransformation.η μT^Hρ→μT^Hρ' (SetSemObjVec ⊢Gs ρ') (μT^HρGf Fρ)



-----------------------------------------------------
-- SetSem functorial action preserves identity
-----------------------------------------------------

-- -- proof that SetSemMapVec preserves identity morphisms 
-- SetSemMapVecId : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} {ρ : SetEnv} 
--               → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
--               → pointwise-≈ (SetSemMapVec ⊢Fs (Category.id SetEnvCat {ρ})) (Category.id (Sets^ k))
SetSemMapVecId {Fs = Vec.[]} Data.Unit.tt = lift Data.Unit.tt
SetSemMapVecId {Fs = F ∷ Fs} (⊢F , ⊢Fs) = (SetSemMapId ⊢F) , (SetSemMapVecId ⊢Fs) 

-- -- proof that SetSemMap preserves identity morphisms 
-- SetSemMapId : ∀ {Γ} {Φ} {F} {ρ : SetEnv} (⊢F : Γ ≀ Φ ⊢ F) 
--               → ∀ {x : SetSemObj ⊢F ρ} 
--               → SetSemMap ⊢F (Category.id SetEnvCat {ρ}) x ≡ x
SetSemMapId 𝟙-I {Data.Unit.tt} = ≡.refl
SetSemMapId {ρ = ρ} (AppT-I {k = k} {φ = φ} Γ∋φ Fs ⊢Fs) {x} = 
  begin Functor.F₁ (SetEnv.tc ρ φ) (SetSemMapVec ⊢Fs (Category.id SetEnvCat)) x 
    ≡⟨ Functor.F-resp-≈ (SetEnv.tc ρ φ) (SetSemMapVecId ⊢Fs) ⟩ 
    Functor.F₁ (SetEnv.tc ρ φ) (Category.id (Sets^ k)) x 
    ≡⟨ Functor.identity (SetEnv.tc ρ φ) {SetSemObjVec ⊢Fs ρ} {x} ⟩ 
    x ∎

SetSemMapId {ρ = ρ} (AppF-I {k = k} {φ = φ} Φ∋φ Fs ⊢Fs) {x} = 
  begin  Functor.F₁ (SetEnv.fv ρ φ) (SetSemMapVec ⊢Fs (Category.id SetEnvCat)) x 
  ≡⟨ Functor.F-resp-≈ (SetEnv.fv ρ φ) (SetSemMapVecId ⊢Fs) ⟩ 
  Functor.F₁ (SetEnv.fv ρ φ) (Category.id (Sets^ k)) x   
  ≡⟨ Functor.identity (SetEnv.fv ρ φ) {SetSemObjVec ⊢Fs ρ} {x} ⟩ 
  x ∎ 


SetSemMapId (+-I ⊢F ⊢G) {inj₁ x} = ≡.cong inj₁ (SetSemMapId ⊢F {x})
SetSemMapId (+-I ⊢F ⊢G) {inj₂ y} = ≡.cong inj₂ (SetSemMapId ⊢G {y})
SetSemMapId (×-I ⊢F ⊢G) {fst , snd} = ×'-cong (SetSemMapId ⊢F {fst}) (SetSemMapId ⊢G {snd})
SetSemMapId (Nat-I ⊢F ⊢G) {x} = {!   !}

-- goal : T^H0-Map ⊢F ρ (fixHFunc (T^H ⊢F ρ))
--       (SetSemMapVec ⊢Gs idρ)
--       (NaturalTransformation.η
--        (TEnv-Map-η ⊢F ρ ρ idρ (fixHFunc (T^H ⊢F ρ)))
--        (SetSemObjVec ⊢Gs ρ)
--        (NaturalTransformation.η
--         (T^H-Map ⊢F ρ (HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ) (TEnv-Map ⊢F ρ ρ idρ)))
--         (SetSemObjVec ⊢Gs ρ) 
--           x))
--       ≡ x


-- TEnv : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
--           {φ : FVar k} {αs : Vec (FVar 0) k}
--         → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
--         → Functor (SetEnvCat) ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])


-- START HERE 
-- 
-- 
SetSemMapId {Γ} {Φ} {H} {ρ} (μ-I {k = k} {φ} {αs} F ⊢F Gs ⊢Gs) {hffin x} = 
    let idGs = SetSemMapVecId {Fs = Gs} {ρ} ⊢Gs 
        TEnvFid = Functor.F₁ (TEnv ⊢F) (idSetEnv {ρ})
        μTEnvFid = HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ) TEnvFid
        TρFμTEnvFid = Functor.F₁ (T^H ⊢F ρ) μTEnvFid 
        μTρF : Functor (Sets^ k) Sets
        μTρF = fixHFunc (T^H ⊢F ρ)
        TμTρF = Functor.F₀ (T^H ⊢F ρ) μTρF
        TρFid-Gs-x = NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid) (SetSemObjVec ⊢Gs ρ) x
        in {! ≡.cong hffin ?  !}

-- SetSemMapId {ρ = ρ} (μ-I {k = k} F ⊢F Gs ⊢Gs) {hffin x} = 
--     let idGs = SetSemMapVecId {Fs = Gs} {ρ} ⊢Gs 
--         TEnvFid = Functor.F₁ (TEnv ⊢F) idSetEnv
--         μTEnvFid = HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ) TEnvFid
--         TρFμTEnvFid = Functor.F₁ (T^H ⊢F ρ) μTEnvFid
--         μTρF = fixHFunc (T^H ⊢F ρ)
--         TμTρF = Functor.F₀ (T^H ⊢F ρ) μTρF
        -- TρFid-Gs-x = NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid) (SetSemObjVec ⊢Gs ρ) x
      -- in ≡.cong hffin ?
        


-- SetSemMapVecId : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k} {ρ : SetEnv} 
--               → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
--               → pointwise-≈ (SetSemMapVec ⊢Fs (Category.id SetEnvCat {ρ})) (Category.id (Sets^ k))
-- 
        -- idT  = T^H0-identity ⊢F ρ (fixHFunc (T^H ⊢F ρ)) (SetSemObjVec ⊢Gs ρ)
      
  --     {! 
  -- begin  Functor.F₁ TμTρF idGs
  --   (NaturalTransformation.η
  --     (NaturalTransformation.η TEnvFid (fixHFunc (T^H ⊢F ρ)))
  --     (SetSemObjVec ⊢Gs ρ)
  --   (NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid)
  --       (SetSemObjVec ⊢Gs ρ) x))
  -- ≡⟨ ?  ⟩ 
  -- ?
  -- ≡⟨ ? ⟩ 
  -- x ∎ 
  --        !}

-- Functor.F₁ (Functor.F₀ (T^H ⊢F ρ) (fixHFunc (T^H ⊢F ρ)))
--       (SetSemMapVec ⊢Gs idSetEnv)
--       (NaturalTransformation.η
--        (NaturalTransformation.η (Functor.F₁ (TEnv ⊢F) idSetEnv)
--         (fixHFunc (T^H ⊢F ρ)))
--        (SetSemObjVec ⊢Gs ρ)
--        (NaturalTransformation.η
--         (Functor.F₁ (T^H ⊢F ρ) (HFix-hmap (T^H ⊢F ρ) (T^H ⊢F ρ) (Functor.F₁ (TEnv ⊢F) idSetEnv)))
--         (SetSemObjVec ⊢Gs ρ) x))
--       ≡ x


-- Functor.F₁ TμTρF idGs
--       (NaturalTransformation.η
--         (NaturalTransformation.η TEnvFid (fixHFunc (T^H ⊢F ρ)))
--         (SetSemObjVec ⊢Gs ρ)
--       (NaturalTransformation.η (Functor.F₁ (T^H ⊢F ρ) μTEnvFid)
--           (SetSemObjVec ⊢Gs ρ) x))
--       ≡ x








-- T^H0-identity : ∀ {k} {Γ} {H} {φ : FVar k} {αs : Vec (FVar 0) k}
--                 → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ ⊢ H)
--                 → (ρ : SetEnv) (F : Functor (Sets^ k) Sets) 
--                 → (As : Vec Set k)
--                 → Sets Categories.Category.[ 
--                       T^H0-Map ⊢H ρ F {As} {As} (Category.id (Sets^ k))
--                       ≈ Category.id Sets ]


  -- begin  
  -- HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs (Category.id SetEnvCat {ρ})) x
  -- ≡⟨ HFix-resp (T^H ⊢F ρ) (SetSemMapVecId ⊢Gs)  ⟩ 
  -- HFix-fmap (T^H ⊢F ρ) (Category.id (Sets^ k)) x
  -- ≡⟨ HFix-id ((T^H ⊢F ρ)) ⟩ 
  -- x ∎ 



-----------------------------------------------------
-- SetSem functorial action preserves composition 
-----------------------------------------------------



-- SetSemMapVecHomo : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k}  {ρ} {ρ'} {ρ''}
--                   → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
--                   → (f : SetEnvMorph ρ ρ')
--                   → (g : SetEnvMorph ρ' ρ'')
--                   → pointwise-≈ (SetSemMapVec ⊢Fs (g ∘SetEnv f)) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f)
SetSemMapVecHomo {Fs = Vec.[]} _ f g = lift Data.Unit.tt
SetSemMapVecHomo {Fs = F ∷ Fs} (⊢F , ⊢Fs) f g = SetSemMapHomo ⊢F f g , SetSemMapVecHomo ⊢Fs f g 

-- SetSemMapHomo : ∀ {Γ} {Φ} {F}  {ρ} {ρ'} {ρ''}
--                 → (⊢F : Γ ≀ Φ ⊢ F)
--                 → (f : SetEnvMorph ρ ρ')
--                 → (g : SetEnvMorph ρ' ρ'')
--                 -- → ∀ {x : Functor.F₀ (SetEnv.fv ρ φ) Xs}
--                 → ∀ {x : SetSemObj ⊢F ρ}
--                 → SetSemMap ⊢F (g ∘SetEnv f) x ≡ SetSemMap ⊢F g (SetSemMap ⊢F f x)
SetSemMapHomo (𝟙-I) f g {x} = ≡.refl

-- WTS 
-- Functor.F₁ F'' (g ∘ f) (η (g∘f) Fs x)
-- ≡
-- Functor.F₁ F'' g (ηg Fs' (Functor.F₁ F' (ηf Fs x))
--
-- SetSemMapVecHomo ⊢Fs f g  
-- gives:
-- pointwise-≈ (SetSemMapVec ⊢Fs (g ∘SetEnv f)) 
--              (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f)
--  
-- so we can use 
-- 
-- Functor.F-resp-≈ F to get
-- 
-- Functor.F₁ (SetSemMapVec ⊢Fs (g ∘SetEnv f)) 
-- ≈ Functor.F₁ (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f)
-- ≈ Functor.F₁ (SetSemMapVec ⊢Fs g) ∘ Functor.F₁ (SetSemMapVec ⊢Fs f)
-- 

-- SetSemMapVecHomo : ∀ {k} {Γ} {Φ} {Fs : Vec TypeExpr k}  {ρ} {ρ'} {ρ''}
--                   → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
--                   → (f : SetEnvMorph ρ ρ')
--                   → (g : SetEnvMorph ρ' ρ'')
--                   → pointwise-≈ (SetSemMapVec ⊢Fs (g ∘SetEnv f)) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f)
SetSemMapHomo {ρ = ρ1} {ρ2} {ρ3} (AppT-I {k = k} {φ = ψ} _ Fs ⊢Fs) f g  {x} = 
    let eq1 = SetEnvMorph.eqTC f {k} 
        eq2 = SetEnvMorph.eqTC g {k} 
        Fsg = SetSemMapVec ⊢Fs g 
        Fsf = SetSemMapVec ⊢Fs f 
        Fh  = Functor.homomorphism (SetEnv.tc ρ3 ψ) {f = Fsf} {g = Fsg}
        Vech = SetSemMapVecHomo ⊢Fs f g
        Fhresp = Functor.F-resp-≈ (SetEnv.tc ρ3 ψ) Vech
        g3 = NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) (SetSemObjVec ⊢Fs ρ1)
        nt = NaturalTransformation.commute (mkIdTCNT f ψ)
        -- for any k : VecFSpace Xs Ys
        -- NaturalTransformation.η (mkIdTCNT f ψ) Ys
        --   ∘' (Functor.F₁ (SetEnv.tc ρ1 ψ) k)
        -- ≈ Functor.F₁ (SetEnv.tc ρ2 ψ) k 
        --   ∘' NaturalTransformation.η (mkIdTCNT f ψ) Xs
        ntgf = NaturalTransformation.commute (mkIdTCNT (g ∘SetEnv f) ψ)
        --  NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) Y
        --     ∘' (Functor.F₁ (SetEnv.tc ρ1 ψ) k)
        --  ≈ 
        --     Functor.F₁ (SetEnv.tc ρ3 ψ) k)
        --     ∘' (NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) X)



    in 
  begin 
    Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs (g ∘SetEnv f))
      (NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) (SetSemObjVec ⊢Fs ρ1) x) 
    ≡⟨  Fhresp ⟩
    Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs g ∘Vec SetSemMapVec ⊢Fs f)
      (NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) (SetSemObjVec ⊢Fs ρ1) x) 
    ≡⟨ Fh  ⟩
    Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs g)
      (Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs f)
        (NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) (SetSemObjVec ⊢Fs ρ1) x))
      ≡⟨ ≡.cong (Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs g)) (≡.sym (ntgf (SetSemMapVec ⊢Fs f))) ⟩ 
    Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs g)
      (NaturalTransformation.η  (mkIdTCNT (g ∘SetEnv f) ψ) (SetSemObjVec ⊢Fs ρ2)
        (Functor.F₁ (SetEnv.tc ρ1 ψ) (SetSemMapVec ⊢Fs f) x))
      ≡⟨ {! Functor.homomorphism (SetEnv.tc ρ3 ψ) {f = Fsf} {g = Fsg}  !} ⟩ 
    Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs g)
    (NaturalTransformation.η (mkIdTCNT g ψ) (SetSemObjVec ⊢Fs ρ2)
      (Functor.F₁ (SetEnv.tc ρ2 ψ) (SetSemMapVec ⊢Fs f)
        (NaturalTransformation.η (mkIdTCNT f ψ) (SetSemObjVec ⊢Fs ρ1) x)
        )
      ) ∎


-- WTS 
--         (Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs f)
--           (NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) (SetSemObjVec ⊢Fs ρ1) x))
--     ≈ 
--         (Functor.F₁ (SetEnv.tc ρ3 ψ) (SetSemMapVec ⊢Fs f)
--           (NaturalTransformation.η (mkIdTCNT (g ∘SetEnv f) ψ) (SetSemObjVec ⊢Fs ρ1) x))
--     ≈ 
--      (NaturalTransformation.η (mkIdTCNT g ψ) (SetSemObjVec ⊢Fs ρ2)
--       NaturalTransformation.η (mkIdTCNT f ψ) (SetSemObjVec ⊢Fs ρ2)
--           ∘' (Functor.F₁ (SetEnv.tc ρ1 ψ) (SetSemMapVec ⊢Fs f)))
--     ≈ 
--      (NaturalTransformation.η (mkIdTCNT g ψ) (SetSemObjVec ⊢Fs ρ2)
--       (Functor.F₁ (SetEnv.tc ρ2 ψ) (SetSemMapVec ⊢Fs f)
--          (NaturalTransformation.η (mkIdTCNT f ψ) (SetSemObjVec ⊢Fs ρ1) x)
--         )) 

    -- by nt 
    -- (Functor.F₁ (SetEnv.tc ρ2 ψ) (SetSemMapVec ⊢Fs f)
    --    (NaturalTransformation.η (mkIdTCNT f ψ) (SetSemObjVec ⊢Fs ρ1) x)
    -- ≈
  --       NaturalTransformation.η (mkIdTCNT f ψ) (SetSemObjVec ⊢Fs ρ2)
  --         ∘' (Functor.F₁ (SetEnv.tc ρ1 ψ) (SetSemMapVec ⊢Fs f))

SetSemMapHomo (AppF-I {k = k} {φ = φ} Φ∋φ Fs ⊢Fs) f g   {x} = {!   !}
SetSemMapHomo (+-I ⊢F ⊢G) f g   {inj₁ x} = ≡.cong inj₁ (SetSemMapHomo ⊢F f g )
SetSemMapHomo (+-I ⊢F ⊢G) f g   {inj₂ y} = ≡.cong inj₂ (SetSemMapHomo ⊢G f g )
SetSemMapHomo (×-I ⊢F ⊢G) f g   {fst , snd} = ×'-cong (SetSemMapHomo  ⊢F f g ) (SetSemMapHomo ⊢G f g )
SetSemMapHomo (Nat-I ⊢F ⊢G) f g   {x} = {!   !}

-- goal : 
-- HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs (g ∘SetEnv f)) x ≡
--  HFix-fmap (T^H ⊢F ρ') (SetSemMapVec ⊢Gs g) (HFix-fmap (T^H ⊢F ρ) (SetSemMapVec ⊢Gs f) x)
SetSemMapHomo (μ-I F ⊢F Gs ⊢Gs) f g {hffin x} = {!   !} 



-- SetSem : ∀ (Γ : TCCtx) → (Φ : FunCtx) → (F : TypeExpr)
--             → Γ ≀ Φ ⊢ F
--             → Functor SetEnvCat Sets
SetSem Γ Φ F ⊢F = record
  { F₀ = SetSemObj ⊢F   -- DONE 
  ; F₁ = λ f →  SetSemMap ⊢F f  -- DONE except Nat case
  ; identity = λ {ρ} → SetSemMapId {ρ = ρ} ⊢F -- DONE except Nat and Mu case 
  ; homomorphism = λ {ρ} {ρ'} {ρ''} {f} {g} → SetSemMapHomo ⊢F f g -- Done trivial cases 
  ; F-resp-≈ = λ {ρ ρ'} {f g} f≈g → {!   !}
  } 



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

extendSetSem-Nat-lem : ∀ {k} {Γ} {F} → (αs : Vec (FVar 0) k) 
                      → (ρ ρ' : SetEnv)
                      → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F)
                      → extendSetSem-αs αs ρ ⊢F 
                        ≡ extendSetSem-αs αs ρ' ⊢F 
--                          
-- λ ⊢H → SetSem _Γ_1848 _Φ_1849 _H_1850 ⊢H ∘F
-- Categories.Category.Product.πˡ ∘F
-- (Categories.Functor.Construction.Constant.const ρ
--  Categories.Category.Product.※ Categories.Functor.id)

extendSetSem-Nat-lem {k} {Γ} {F} [] ρ ρ' ⊢F = {!   !} 
extendSetSem-Nat-lem {k} {Γ} {F} (α ∷ αs) ρ ρ' ⊢F = {!   !} 

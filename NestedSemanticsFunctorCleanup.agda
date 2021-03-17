open import NestedSyntax6NoStrings 
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
open import Categories.Functor using (Functor ; _∘F_)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
-- open import Categories.Diagram.Cocone
-- open import Data.Nat using (ℕ ; _≤_ )
-- open ℕ
-- open _≤_
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)

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





-------------------------------------------------------
-- SetSem functor -- 
-------------------------------------------------------

SetSem : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
            → Γ ≀ Φ ⊢ F
            → Functor SetEnvCat Sets

-----------------------------------------------------
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

-------------------------------------------------------
-- END TYPES
-------------------------------------------------------



-- extendSetSem-αs : ∀ {k} {Γ} {Φ} {H} → (αs : Vec (FVar 0) k) → SetEnv
--               → (⊢H : Γ ≀ Φ ,++ αs ⊢ H)
--               → Functor (Sets^ k) Sets
extendSetSem-αs {k} {Γ} {Φ} {H} αs ρ ⊢H = SetSem {Γ} {Φ ,++ αs} {H} ⊢H  ∘F extendSetEnv-αs αs ρ 


-------------------------------------------------------
-- TENV definitions 
-------------------------------------------------------

-- TEnvProd : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
--           {φ : FVar k} {αs : Vec (FVar 0) k}
--         → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
--         → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) Sets
TEnvProd {k} {Γ} {H} {φ} {αs} ⊢H = SetSem {Γ} {(∅ ,++ αs) ,, φ} ⊢H ∘F extendTEnv2 φ αs



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



-- TODO make sure this is not reversing the order or anything 
SetSemVec : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx}
              → {Fs : Vec TypeExpr k}
              → foreach (λ F → Γ ≀ Φ ⊢ F) Fs
              → Functor SetEnvCat (Sets^ k)
SetSemVec {zero} {Γ} {Φ} {[]} Data.Unit.tt = ConstF []
SetSemVec {suc k} {Γ} {Φ} {F ∷ Fs} (⊢F , ⊢Fs) = 
  let SetSemF×SetSemFs : Functor SetEnvCat (Product Sets (Sets^ k))
      SetSemF×SetSemFs = SetSem ⊢F ※ SetSemVec ⊢Fs
    in Sets^cons k ∘F SetSemF×SetSemFs


SetSem 𝟘-I = ConstF ⊥'
SetSem 𝟙-I = ConstF ⊤
SetSem (Nat-I ⊢F ⊢G)  = NatTypeSem ⊢F ⊢G
SetSem (+-I ⊢F ⊢G) = SetSum ∘F (SetSem ⊢F ※ SetSem ⊢G)
SetSem (×-I ⊢F ⊢G) = SetProd ∘F (SetSem ⊢F ※ SetSem ⊢G)
SetSem (AppT-I {φ = φ} Γ∋φ Gs ⊢Gs) = eval ∘F (VarSem-TC φ ※ SetSemVec ⊢Gs)
SetSem (AppF-I {φ = φ} Φ∋φ Gs ⊢Gs) = eval ∘F (VarSem-FV φ ※ SetSemVec ⊢Gs)
SetSem (μ-I {k = k} F ⊢F Ks ⊢Ks) = 
  let SetSemKs : Functor SetEnvCat (Sets^ k)
      SetSemKs = SetSemVec ⊢Ks
      fixT : Functor SetEnvCat [Sets^ k ,Sets]
      fixT = fixH ∘F TEnv ⊢F
    in eval ∘F (fixT ※ SetSemKs)


--------------
-- END MUTUAL 
--------------

-- TODO 
-- - show that syntactic substitution works nicely with environment extension.... 
-- - prove demotion doesn't change semantics 
-- - 

  -- -- demotion of functorial variables to non-functorial variables 
  -- _[_:==_] : ∀ {k : ℕ} → TypeExpr → FVar k → TCVar k → TypeExpr
  

  -- demotion-preserves-typing : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : FVar k} {ψ : TCVar k}
  --                          → (F : TypeExpr)
  --                          → Γ ≀ (Φ ,, φ) ⊢ F
  --                          → (Γ ,, ψ ) ≀ Φ ⊢ F [ φ :== ψ ]


-- for demotion, we could use 
-- 
-- VarSem-FV φ ≡ VarSem-TC ψ 




-- mutual 
-- -- demotion for full functors 


--   -- weakenTCCtx  : ∀ {k : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φ : TCVar k)  (F : TypeExpr)
--   --                 → Γ ≀ Φ ⊢ F
--   --                 → Γ ,, φ ≀ Φ ⊢ F
--   -- 
--   -- 
--   -- weakenTCCtxVec :  ∀ {k n : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φs : Vec (TCVar k) n)  (F : TypeExpr)
--   --                   → Γ ≀ Φ ⊢ F
--   --                   -- → (¬ (Γ ∋ φ))
--   --                   → Γ ,++ φs ≀ Φ ⊢ F
--   -- weakenTCCtxVec {n = zero} [] F ⊢F = ⊢F
--   -- weakenTCCtxVec {n = suc n} (φ ∷ φs) F ⊢F = weakenTCCtx  φ F (weakenTCCtxVec φs F ⊢F)

--   -- foreach-preserves-weakening  : ∀ {k n : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : TCVar k}
--   --                                   → (Gs : Vec TypeExpr n)
--   --                                   → foreach (λ G → Γ ≀ Φ ⊢ G) Gs
--   --                                   → foreach (λ G → Γ ,, φ ≀ Φ ⊢ G) Gs

--   SetSem-weaken-Vec : ∀ {n} {Γ : TCCtx} → {Φ : FunCtx} → {Fs : Vec TypeExpr n}
--                     → {k : ℕ} → (ψ : TCVar k)
--                     → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
--                     → SetSemVec ⊢Fs
--                       ≡ SetSemVec (foreach-preserves-weakening {φ = ψ} Fs ⊢Fs)
--   SetSem-weaken-Vec {Fs = []} ψ ⊢Fs = ≡.refl 
--   -- goal : Sets^cons n ∘F (SetSem ⊢F                   ※ SetSemVec ⊢Fs) 
--   --      ≡ Sets^cons n ∘F (SetSem (weakenTCCtx ψ F ⊢F) ※ SetSemVec (foreach-preserves-weakening Fs ⊢Fs))
--   SetSem-weaken-Vec {suc n} {Fs = F ∷ Fs} ψ (⊢F , ⊢Fs) = 
--     let Fs≡wFs = SetSem-weaken-Vec ψ ⊢Fs 
--         F※Fs≡wF※wFs = ≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) Fs≡wFs
--       in ≡.cong (_∘F_ (Sets^cons n)) F※Fs≡wF※wFs

--   SetSem-weaken : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
--                     → {k : ℕ} → (ψ : TCVar k)
--                     → (⊢F : Γ ≀ Φ ⊢ F)
--                     → SetSem ⊢F
--                       ≡ SetSem (weakenTCCtx ψ F ⊢F)
--   SetSem-weaken ψ 𝟘-I = ≡.refl
--   SetSem-weaken ψ 𝟙-I = ≡.refl
--   SetSem-weaken (ψ ^T k) (AppT-I {φ = φ ^T j} Γ∋φ Fs ⊢Fs) with eqNat k j | ψ ≟ φ
--   -- goal : eval ∘F (VarSem-TC (ψ ^T k) ※ SetSemVec ⊢Fs) ≡
--   --        eval ∘F (VarSem-TC (ψ ^T k) ※ SetSemVec (foreach-preserves-weakening Fs ⊢Fs))
--   ... | yes ≡.refl | yes ≡.refl = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-TC (φ ^T j))) (SetSem-weaken-Vec (ψ ^T k) ⊢Fs)) 
--   ... | yes ≡.refl | no _       = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-TC (φ ^T j))) (SetSem-weaken-Vec (ψ ^T k) ⊢Fs)) 
--   ... | no _  | _               = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-TC (φ ^T j))) (SetSem-weaken-Vec (ψ ^T k) ⊢Fs)) 

--   -- goal : eval ∘F (VarSem-FV φ ※ SetSemVec ⊢Fs) ≡
--   --        eval ∘F (VarSem-FV φ ※ SetSemVec (foreach-preserves-weakening Fs ⊢Fs))
--   SetSem-weaken ψ (AppF-I {φ = φ} Γ∋φ Fs ⊢Fs) = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-FV φ)) (SetSem-weaken-Vec ψ ⊢Fs))
-- -- goal :   SetSum ∘F (SetSem ⊢F                   ※ SetSem ⊢G) ≡
-- --         SetSum ∘F  (SetSem (weakenTCCtx ψ F ⊢F) ※ SetSem (weakenTCCtx ψ G ⊢G))

--   SetSem-weaken ψ (+-I ⊢F ⊢G) = ≡.cong (_∘F_ SetSum)  (≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) (SetSem-weaken ψ ⊢G))
--   SetSem-weaken ψ (×-I ⊢F ⊢G) = ≡.cong (_∘F_ SetProd) (≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) (SetSem-weaken ψ ⊢G))
--   SetSem-weaken ψ (Nat-I ⊢F ⊢G) = {!   !}

--   -- goal : eval ∘F (fixH ∘F TEnv ⊢F                   ※ SetSemVec ⊢Gs) ≡
--   --        eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (foreach-preserves-weakening Gs ⊢Gs))
--   SetSem-weaken ψ (μ-I {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) = 
--       let Gs≡wGs = SetSem-weaken-Vec ψ ⊢Gs 
--           F∘ext : (SetSem ⊢F                   ∘F extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ))
--                 ≡ (SetSem (weakenTCCtx ψ F ⊢F) ∘F extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ))
--           F∘ext = ≡.cong-app (≡.cong _∘F_ (SetSem-weaken ψ ⊢F)) (extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ))
--         in {!   !} 
--   -- normalized goal  
-- --   eval ∘F (fixH ∘F curry₀ (curry₀
-- --   (SetSem ⊢F ∘F
-- --   --
-- --    extendSetEnv-ρ×As-inline αs ∘F
-- --    (extendSetEnv2 φ ∘F πˡ ※ πʳ)))
-- --    --
-- --  ※ SetSemVec ⊢Gs)
-- -- ≡
-- -- eval ∘F (fixH ∘F curry₀ (curry₀
-- --   (SetSem (weakenTCCtx ψ F ⊢F) ∘F
-- --   --
-- --    extendSetEnv-ρ×As-inline αs ∘F
-- --    (extendSetEnv2 φ ∘F πˡ ※ πʳ)))
-- --    --
-- --  ※ SetSemVec (foreach-preserves-weakening Gs ⊢Gs))


--   SetSem-demotion-Vec : ∀ {n : ℕ} {Γ : TCCtx} → {Φ : FunCtx} → {Fs : Vec TypeExpr n}
--                         → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
--                         → (⊢Fs : foreach (λ F → Γ ≀ Φ ,, φ ⊢ F) Fs)
--                         → VarSem-FV φ ≡ VarSem-TC ψ
--                       → SetSemVec ⊢Fs
--                         ≡ SetSemVec (demoteVec-preserves-typing {φ = φ} {ψ} Fs ⊢Fs)
--   SetSem-demotion-Vec {zero} {Fs = []} φ ψ Data.Unit.tt e = ≡.refl
--   -- ≡.refl
--   SetSem-demotion-Vec {suc n} {Fs = F ∷ Fs} φ ψ (⊢F , ⊢Fs) e = 
--     let Fs≡wFs = SetSem-demotion-Vec φ ψ ⊢Fs e 
--         F※Fs≡wF※wFs = ≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F e) Fs≡wFs
--         in ≡.cong (_∘F_ (Sets^cons n)) F※Fs≡wF※wFs

--   SetSem-demotion : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
--                     → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
--                     → (⊢F : Γ ≀ Φ ,, φ ⊢ F)
--                     → VarSem-FV φ ≡ VarSem-TC ψ
--                     -- maybe relax this and use ≈ from SEC 
--                     → SetSem ⊢F
--                       ≡ SetSem (demotion-preserves-typing {φ = φ} {ψ} F ⊢F)
--   SetSem-demotion φ ψ 𝟘-I ρφ≡ρψ = ≡.refl
--   SetSem-demotion φ ψ 𝟙-I ρφ≡ρψ = ≡.refl
--   SetSem-demotion φ ψ (AppT-I {φ = ϕ} Γ∋p  Fs ⊢Fs) ρφ≡ρψ = 
--   -- goal : eval ∘F (VarSem-TC p ※ SetSemVec ⊢Fs) 
--   --        ≡ eval ∘F (VarSem-TC p ※ SetSemVec (demoteVec-preserves-typing Fs ⊢Fs))
--     let Fs≡wFs = SetSem-demotion-Vec φ ψ ⊢Fs ρφ≡ρψ
--         eq-※ = ≡.cong (_※_ (VarSem-TC ϕ)) Fs≡wFs
--         in ≡.cong (_∘F_ eval) eq-※
-- -- goal : eval ∘F (VarSem-FV p ※ SetSemVec ⊢Fs) ≡ 
-- -- SetSem
-- --       (demotion-preserves-typing AppF p [ Fs ] (AppF-I Γ∋p Fs ⊢Fs))

--   SetSem-demotion (φ ^F k) (ψ ^T k) (AppF-I {φ = ϕ ^F j} Γ∋p  Fs ⊢Fs) ρφ≡ρψ with eqNat j k | ϕ ≟ φ
-- --   SetSem-demotion {k = k} (φ ^F k) ψ (AppF-I {φ = φ2 ^F j} Φ∋φ2 Fs ⊢Fs) ρ ρφ≡ρψ with eqNat j k | φ2 ≟ φ
-- -- 
-- --
-- -- yes yes goal : 
-- -- eval ∘F (VarSem-FV (φ ^F k) ※ SetSemVec ⊢Fs) 
-- -- ≡ eval ∘F (VarSem-TC (ψ ^T k) ※ SetSemVec (demoteVec-preserves-typing Fs ⊢Fs))
--   ... | yes ≡.refl | yes ≡.refl = 
--     let Fs≡wFs = SetSem-demotion-Vec (φ ^F k) (ψ ^T k) ⊢Fs ρφ≡ρψ
--         eq-※ = ≡.cong₂ _※_ ρφ≡ρψ Fs≡wFs
--         in ≡.cong (_∘F_ eval) eq-※
--   ... | yes ≡.refl | no _  = 
--     let Fs≡wFs = SetSem-demotion-Vec (φ ^F k) (ψ ^T k) ⊢Fs ρφ≡ρψ
--         eq-※ = ≡.cong (_※_  (VarSem-FV (ϕ ^F k))) Fs≡wFs  -- notice difference with second argument of ≡.cong₂ 
--         in ≡.cong (_∘F_ eval) eq-※
--       --   goal : eval ∘F (VarSem-FV (ϕ ^F k) ※ SetSemVec ⊢Fs) ≡
--       --          eval ∘F (VarSem-FV (ϕ ^F k) ※ SetSemVec (demoteVec-preserves-typing Fs ⊢Fs))

--   ... | no _ | yes ≡.refl   = 
--     let Fs≡wFs = SetSem-demotion-Vec (φ ^F k) (ψ ^T k) ⊢Fs ρφ≡ρψ
--         eq-※ = ≡.cong (_※_  (VarSem-FV (ϕ ^F j))) Fs≡wFs  -- notice difference with second argument of ≡.cong₂ 
--         in ≡.cong (_∘F_ eval) eq-※
--   ... | no _ | no _  = 
--     let Fs≡wFs = SetSem-demotion-Vec (φ ^F k) (ψ ^T k) ⊢Fs ρφ≡ρψ
--         eq-※ = ≡.cong (_※_  (VarSem-FV (ϕ ^F j))) Fs≡wFs  -- notice difference with second argument of ≡.cong₂ 
--         in ≡.cong (_∘F_ eval) eq-※

-- -- -- SetSum ∘F (SetSem ⊢F ※ SetSem ⊢G) ≡
-- --     SetSum ∘F
-- --     (SetSem (demotion-preserves-typing F ⊢F) ※
-- --      SetSem (demotion-preserves-typing G ⊢G))
--   SetSem-demotion φ ψ (+-I ⊢F ⊢G) ρφ≡ρψ = ≡.cong (_∘F_ SetSum)  (≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F ρφ≡ρψ ) (SetSem-demotion φ ψ ⊢G ρφ≡ρψ ))
--   SetSem-demotion φ ψ (×-I ⊢F ⊢G) ρφ≡ρψ = ≡.cong (_∘F_ SetProd) (≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F ρφ≡ρψ ) (SetSem-demotion φ ψ ⊢G ρφ≡ρψ ))
--   SetSem-demotion φ ψ (Nat-I ⊢F ⊢G) ρφ≡ρψ = {!   !}
--   SetSem-demotion φ ψ (μ-I F ⊢F Gs ⊢Gs) ρφ≡ρψ = {! eval ∘F (fixH ∘F TEnv ⊢F ※ SetSemVec ⊢Gs) ≡ eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (demoteVec-preserves-typing Gs ⊢Gs)) !} 
-- -- goal : eval ∘F (fixH ∘F TEnv ⊢F                   ※ SetSemVec ⊢Gs) ≡
-- --        eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (demoteVec-preserves-typing Gs ⊢Gs))

-- -- normalized goal : 
-- -- 
-- -- eval ∘F (fixH ∘F curry₀ (curry₀
-- --   --
-- --   (SetSem ⊢F ∘F
-- --   -- 
-- --    extendSetEnv-ρ×As-inline αs ∘F
-- --    (extendSetEnv2 φ₁ ∘F πˡ ※ πʳ)))
-- -- 
-- -- --
-- --  ※ SetSemVec ⊢Gs)
-- -- ≡
-- -- eval ∘F (fixH ∘F curry₀ (curry₀ 
-- --   --* SetSem-weakenTCCtx
-- --   (SetSem (weakenTCCtx ψ F ⊢F) ∘F
-- -- 
-- --   --* same
-- --    extendSetEnv-ρ×As-inline αs ∘F
-- --    (extendSetEnv2 φ₁ ∘F πˡ ※ πʳ)))
-- -- 
-- --   --* SetSem-demotion-Vec
-- --  ※ SetSemVec (demoteVec-preserves-typing Gs ⊢Gs))



-- -- mutual

-- --   -- demotion for objects... 

-- --   SetSem-demotion-Vec : ∀ {n : ℕ} {Γ : TCCtx} → {Φ : FunCtx} → {Fs : Vec TypeExpr n}
-- --                         → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
-- --                         → (⊢Fs : foreach (λ F → Γ ≀ Φ ,, φ ⊢ F) Fs)
-- --                         → (ρ : SetEnv) 
-- --                         → (SetEnv.fv ρ φ) ≡ (SetEnv.tc ρ ψ) 
-- --                         → Functor.F₀ (SetSemVec ⊢Fs) ρ 
-- --                           ≡ Functor.F₀ (SetSemVec (demoteVec-preserves-typing {φ = φ} {ψ} Fs ⊢Fs)) ρ
-- --   SetSem-demotion-Vec {zero} {Fs = []} φ ψ Data.Unit.tt ρ e = ≡.refl
-- --   -- goal : 
-- --   -- Functor.F₀ (SetSem ⊢F) ρ ∷ Functor.F₀ (SetSemVec ⊢Fs) ρ ≡
-- --   -- Functor.F₀ (SetSem (demotion-preserves-typing F ⊢F)) ρ ∷
-- --   -- Functor.F₀ (SetSemVec (demoteVec-preserves-typing Fs ⊢Fs)) ρ
-- --   -- 
-- --   -- A ∷ As ≡ B ∷ Bs 
-- --   SetSem-demotion-Vec {suc n} {Fs = F ∷ Fs} φ ψ (⊢F , ⊢Fs) ρ e = ≡.cong₂ _∷_ (SetSem-demotion φ ψ ⊢F ρ e) (SetSem-demotion-Vec φ ψ ⊢Fs ρ e) 


-- --   SetSem-demotion : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
-- --                     → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
-- --                     → (⊢F : Γ ≀ Φ ,, φ ⊢ F)
-- --                     → (ρ : SetEnv) 
-- --                     -- maybe relax this and use ≈ from SEC 
-- --                     → (SetEnv.fv ρ φ) ≡ (SetEnv.tc ρ ψ) 
-- --                     → Functor.F₀ (SetSem ⊢F) ρ 
-- --                       ≡ Functor.F₀ (SetSem (demotion-preserves-typing {φ = φ} {ψ} F ⊢F)) ρ
-- --   SetSem-demotion φ ψ 𝟘-I ρ ρφ≡ρψ = ≡.refl
-- --   SetSem-demotion φ ψ 𝟙-I ρ ρφ≡ρψ = ≡.refl
-- --   -- goal : Functor.F₀ (SetEnv.tc ρ φ2) (Functor.F₀ (SetSemVec ⊢Fs) ρ) 
-- --   -- ≡ Functor.F₀ (SetEnv.tc ρ φ2)
-- --   -- (Functor.F₀ (SetSemVec (demoteVec-preserves-typing Fs ⊢Fs)) ρ)
-- --   SetSem-demotion φ ψ (AppT-I {φ = φ2} Γ∋φ2 Fs ⊢Fs) ρ ρφ≡ρψ = ≡.cong (Functor.F₀ (SetEnv.tc ρ φ2)) (SetSem-demotion-Vec φ ψ ⊢Fs ρ ρφ≡ρψ)
-- --   -- ≡.cong (Functor.F₀ (SetEnv.fv ρ φ2)) (SetSem-demotion-Vec φ ψ ⊢Fs ρ ρφ≡ρψ)
-- --   -- goal : 
-- --   -- Functor.F₀ (SetEnv.fv ρ φ2) (Functor.F₀ (SetSemVec ⊢Fs) ρ) ≡
-- --   -- Functor.F₀
-- --   -- (SetSem
-- --   --  (demotion-preserves-typing AppF φ2 [ Fs ] (AppF-I Φ∋φ2 Fs ⊢Fs))) ρ
-- --   SetSem-demotion {k = k} (φ ^F k) ψ (AppF-I {φ = φ2 ^F j} Φ∋φ2 Fs ⊢Fs) ρ ρφ≡ρψ with eqNat j k | φ2 ≟ φ
-- --   ... | yes ≡.refl | yes ≡.refl = {!   !} 
-- --   ... | yes ≡.refl | no _  = {!   !} 
-- --   ... | no _ | yes ≡.refl   = {!   !} 
-- --   ... | no _ | no _  = {!   !} 
-- --   SetSem-demotion φ ψ (+-I ⊢F ⊢G) ρ ρφ≡ρψ = ≡.cong₂ _⊎_ ((SetSem-demotion φ ψ ⊢F ρ ρφ≡ρψ)) ((SetSem-demotion φ ψ ⊢G ρ ρφ≡ρψ))
-- --   SetSem-demotion φ ψ (×-I ⊢F ⊢G) ρ ρφ≡ρψ = ≡.cong₂ _×'_ (SetSem-demotion φ ψ ⊢F ρ ρφ≡ρψ) ((SetSem-demotion φ ψ ⊢G ρ ρφ≡ρψ))
-- --   -- Σ (Functor.F₀ (SetSem ⊢F) ρ) (λ x → Functor.F₀ (SetSem ⊢G) ρ) ≡
-- --   -- Σ (Functor.F₀ (SetSem (demotion-preserves-typing F ⊢F)) ρ)
-- --   -- (λ x → Functor.F₀ (SetSem (demotion-preserves-typing G ⊢G)) ρ)
-- --   SetSem-demotion φ ψ (Nat-I ⊢F ⊢G) ρ ρφ≡ρψ = {!   !}
-- --   SetSem-demotion φ ψ (μ-I F ⊢F Gs ⊢Gs) ρ ρφ≡ρψ = 
-- --     let Gs≈wGs = SetSem-demotion-Vec φ ψ ⊢Gs ρ ρφ≡ρψ
-- --         ⊢wF = weakenTCCtx ψ F ⊢F 
-- --         ⊢wGs = demoteVec-preserves-typing Gs ⊢Gs

-- --         fix∘TF※Gs = fix∘F TEnv ⊢F ※ SetSemVec ⊢Gs
-- --         fix∘TwF※wGs = fix∘F TEnv ⊢wF ※ SetSemVec ⊢wGs
-- --         -- can we prove ⊢F ≡ (weakenTCCtx ψ ... ) ? 
-- --         -- -- no. but does TEnv do anything with TC vars? 
-- --         TF≡TwF = ≡.cong TEnv ()
-- --         in ≡.cong (Functor.F₀ eval) {! ≡.cong   !} 
-- -- 
-- -- 

-- -- eval (Functor.₀ (fixH ∘F TEnv ⊢F ※ SetSemVec ⊢Gs) ρ)
-- --   ≡ eval (Functor.₀
-- --        (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※
-- --         SetSemVec (demoteVec-preserves-typing Gs ⊢Gs))
-- --        ρ)
-- -- 
-- -- Functor.F₀ (fix ∘F TF ※ Gs) ρ
-- -- ≡  Functor.F₀ (fix ∘F TwF ※ wGs) ρ
-- -- 
-- -- Functor.F₀ (fix ∘F As) ρ
-- -- ≡  Functor.F₀ (fix ∘F Bs) ρ


-- -- normalized goal : 
-- --   HFixFunctor
-- -- (curry₀
-- --  (SetSem ⊢F ∘F                     --** SetSem⊢F≡SetSem⊢wF  -- but can we prove *functors* are equal?
-- --   extendSetEnv-ρ×As-inline αs ∘F   -** same 
-- --   (extendSetEnv2 φ₁ ∘F πˡ ※        --** same 
-- --    πʳ))
-- -- 
-- --  ∘F
-- -- 
-- --  (Constant.const ρ ※             --**  same as below
-- --   Categories.Functor.id))
-- --        (Functor.F₀ (SetSemVec ⊢Gs) ρ) --** Gs≡wGs
-- -- ≡
-- -- HFixFunctor
-- -- (curry₀
-- --  (SetSem (weakenTCCtx ψ F ⊢F) ∘F   -- 
-- --   extendSetEnv-ρ×As-inline αs ∘F   
-- --   (extendSetEnv2 φ₁ ∘F πˡ ※
-- --    πʳ))
-- -- 
-- --  ∘F
-- -- 
-- --  (Constant.const ρ ※
-- --   Categories.Functor.id))
-- --          (Functor.F₀ (SetSemVec (demoteVec-preserves-typing Gs ⊢Gs)) ρ)



-- -- normalized goal : 
-- --   HFixFunctor
-- -- (Categories.Category.Construction.Functors.curry₀
-- --  (SetSem ⊢F ∘F
-- --   extendSetEnv-ρ×As-inline αs ∘F
-- --   (extendSetEnv2 φ₁ ∘F Categories.Category.Product.πˡ ※
-- --    Categories.Category.Product.πʳ))
-- --  ∘F
-- --  (Categories.Functor.Construction.Constant.const ρ ※
-- --   Categories.Functor.id))
-- -- (Functor.F₀ (SetSemVec ⊢Gs) ρ)
-- -- ≡
-- -- HFixFunctor
-- -- (Categories.Category.Construction.Functors.curry₀
-- --  (SetSem (weakenTCCtx ψ F ⊢F) ∘F
-- --   extendSetEnv-ρ×As-inline αs ∘F
-- --   (extendSetEnv2 φ₁ ∘F Categories.Category.Product.πˡ ※
-- --    Categories.Category.Product.πʳ))
-- --  ∘F
-- --  (Categories.Functor.Construction.Constant.const ρ ※
-- --   Categories.Functor.id))
-- -- (Functor.F₀ (SetSemVec (demoteVec-preserves-typing Gs ⊢Gs)) ρ)



-- -- tODO maybe natural iso? 
--   -- SetSem-demotion-full : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
--   --                   → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
--   --                   → (⊢F : Γ ≀ Φ ,, φ ⊢ F)
--   --                   → (ρ : SetEnv) 
--   --                   -- → (SetEnv.fv ρ φ) ≡ (SetEnv.tc ρ ψ) 
--   --                   → NaturalIsomorphism 
--   --                       (SetSem ⊢F)
--   --                       (SetSem (demotion-preserves-typing {φ = φ} {ψ} F ⊢F)) 

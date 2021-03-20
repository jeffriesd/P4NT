open import NestedTypeSyntax 
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open FVar
open _∋_ 

-- open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
-- open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (if_then_else_; true; false)
open import Categories.Category using (Category)
open import Categories.Category.Product using (Product ; _※_  ; πˡ ; πʳ)
open import Categories.Functor using (Functor ; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
-- open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
-- open import Data.Nat using (ℕ ; _≤_ )
-- open ℕ
-- open _≤_
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)

open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
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
open import SetCats
open import Utils
open import SetEnvironments

open import NestedSetSemantics 




-- taking set interpretation after weakening non-functorial context 
-- gives precisely the same functor 

module SetSemWeakenTCCtx where 




mutual 
  SetSem-weaken-TEnvProd : ∀ {Γ : TCCtx} →  {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                    → {j : ℕ} (ψ : TCVar j)
                    → (⊢F : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ F)
                    → TEnvProd ⊢F
                      ≡ TEnvProd (weakenTCCtx ψ F ⊢F)

  SetSem-weaken-TEnvProd {Γ} {F} {k} φ αs ψ ⊢F rewrite (SetSem-weaken ψ ⊢F) = ≡.refl
  -- ≡.cong (λ G → G ∘F (extendTEnv2 φ αs)) (SetSem-weaken ψ ⊢F)
  
--   normalized goal : 
--   SetSem ⊢F 
--     ∘F extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ)
-- ≡ SetSem (weakenTCCtx ψ F ⊢F) 
--     ∘F extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ)
  -- 
  -- 
-- SetSem {Γ} {(∅ ,++ αs) ,, φ} ⊢H ∘F extendTEnv2 φ αs




  SetSem-weaken-curry : ∀ {Γ : TCCtx} →  {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                    → {j : ℕ} (ψ : TCVar j)
                    → (⊢F : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ F)
                    → curry.F₀ (TEnvProd ⊢F)
                      ≡ curry.F₀ (TEnvProd (weakenTCCtx ψ F ⊢F))

  -- NB : for some reason the ≡.cong curry.F₀ definition takes a really long time to type-checl
  -- SetSem-weaken-curry {Γ} {F} {k} φ αs ψ ⊢F = {!≡.cong curry.F₀ (SetSem-weaken-TEnvProd φ αs ψ ⊢F)!}
  SetSem-weaken-curry {Γ} {F} {k} φ αs ψ ⊢F rewrite (SetSem-weaken-TEnvProd φ αs ψ ⊢F) = ≡.refl 
  -- SetSem-weaken-curry {Γ} {F} {k} φ αs ψ ⊢F rewrite (≡.cong curry.F₀ (SetSem-weaken-TEnvProd φ αs ψ ⊢F)) = ≡.refl 
                                                

  SetSem-weaken-curry2 : ∀ {Γ : TCCtx} →  {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                    → {j : ℕ} (ψ : TCVar j)
                    → (⊢F : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ F)
                    → curry.F₀ (curry.F₀ (TEnvProd ⊢F))
                      ≡ curry.F₀ (curry.F₀ (TEnvProd (weakenTCCtx ψ F ⊢F)))
  -- SetSem-weaken-curry2 {Γ} {F} {k} φ αs ψ ⊢F rewrite (≡.cong curry.F₀ (SetSem-weaken-curry φ αs ψ ⊢F)) = ≡.refl 
  SetSem-weaken-curry2 {Γ} {F} {k} φ αs ψ ⊢F rewrite (SetSem-weaken-curry φ αs ψ ⊢F) = ≡.refl 
                                                
                    
  SetSem-weaken-TEnv : ∀ {Γ : TCCtx} →  {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                    → {j : ℕ} (ψ : TCVar j)
                    → (⊢F : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ F)
                    → TEnv ⊢F
                      ≡ TEnv (weakenTCCtx ψ F ⊢F)
  -- SetSem-weaken-TEnv {Γ} {F} {k} φ αs ψ ⊢F rewrite (SetSem-weaken-curry2 φ αs ψ ⊢F) = ≡.refl
  SetSem-weaken-TEnv {Γ} {F} {k} φ αs ψ ⊢F = SetSem-weaken-curry2 φ αs ψ ⊢F



  SetSem-weaken-Vec : ∀ {n} {Γ : TCCtx} → {Φ : FunCtx} → {Fs : Vec TypeExpr n}
                    → {k : ℕ} → (ψ : TCVar k)
                    → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
                    → SetSemVec ⊢Fs
                      ≡ SetSemVec (foreach-preserves-weakening {φ = ψ} Fs ⊢Fs)
  SetSem-weaken-Vec {Fs = []} ψ ⊢Fs = ≡.refl 
  -- goal : Sets^cons n ∘F (SetSem ⊢F                   ※ SetSemVec ⊢Fs) 
  --      ≡ Sets^cons n ∘F (SetSem (weakenTCCtx ψ F ⊢F) ※ SetSemVec (foreach-preserves-weakening Fs ⊢Fs))

  SetSem-weaken-Vec {suc n} {Fs = F ∷ Fs} ψ (⊢F , ⊢Fs) rewrite (SetSem-weaken ψ ⊢F) | (SetSem-weaken-Vec ψ ⊢Fs) = ≡.refl
    -- let Fs≡wFs = SetSem-weaken-Vec ψ ⊢Fs 
    --     F※Fs≡wF※wFs = ≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) Fs≡wFs
    --   in ≡.cong (_∘F_ (Sets^cons n)) F※Fs≡wF※wFs

  SetSem-weaken : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
                    → {k : ℕ} → (ψ : TCVar k)
                    → (⊢F : Γ ≀ Φ ⊢ F)
                    → SetSem ⊢F
                      ≡ SetSem (weakenTCCtx ψ F ⊢F)
  SetSem-weaken ψ 𝟘-I = ≡.refl
  SetSem-weaken ψ 𝟙-I = ≡.refl
  -- using rewrite here is more efficient than inlining proofs of equality
  -- because with rewrite, (SetSem-weaken-Vec ...) is only computed once 
  SetSem-weaken (ψ ^T k) (AppT-I {φ = φ ^T j} Γ∋φ Fs ⊢Fs) rewrite (SetSem-weaken-Vec (ψ ^T k) ⊢Fs) with eqNat k j | ψ ≟ φ
  ... | yes ≡.refl | yes ≡.refl = ≡.refl
  ... | yes ≡.refl | no _       = ≡.refl
  ... | no _  | _               = ≡.refl
  -- -- goal : eval ∘F (VarSem-TC (ψ ^T k) ※ SetSemVec ⊢Fs) ≡
  -- --        eval ∘F (VarSem-TC (ψ ^T k) ※ SetSemVec (foreach-preserves-weakening Fs ⊢Fs))
  -- ... | yes ≡.refl | yes ≡.refl = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-TC (φ ^T j))) (SetSem-weaken-Vec (ψ ^T k) ⊢Fs)) 
  -- ... | yes ≡.refl | no _       = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-TC (φ ^T j))) (SetSem-weaken-Vec (ψ ^T k) ⊢Fs)) 
  -- ... | no _  | _               = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-TC (φ ^T j))) (SetSem-weaken-Vec (ψ ^T k) ⊢Fs)) 

  -- goal : eval ∘F (VarSem-FV φ ※ SetSemVec ⊢Fs) ≡
  --        eval ∘F (VarSem-FV φ ※ SetSemVec (foreach-preserves-weakening Fs ⊢Fs))
  -- SetSem-weaken ψ (AppF-I {φ = φ} Γ∋φ Fs ⊢Fs) = ≡.cong (_∘F_ eval) (≡.cong (_※_ (VarSem-FV φ)) (SetSem-weaken-Vec ψ ⊢Fs))
  SetSem-weaken ψ (AppF-I {φ = φ} Γ∋φ Fs ⊢Fs) rewrite (SetSem-weaken-Vec ψ ⊢Fs) = ≡.refl

-- goal :   SetSum ∘F (SetSem ⊢F                   ※ SetSem ⊢G) ≡
--         SetSum ∘F  (SetSem (weakenTCCtx ψ F ⊢F) ※ SetSem (weakenTCCtx ψ G ⊢G))

  -- SetSem-weaken ψ (+-I ⊢F ⊢G) = ≡.cong (_∘F_ SetSum)  (≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) (SetSem-weaken ψ ⊢G))
  -- SetSem-weaken ψ (×-I ⊢F ⊢G) = ≡.cong (_∘F_ SetProd) (≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) (SetSem-weaken ψ ⊢G))
  SetSem-weaken ψ (+-I ⊢F ⊢G) rewrite (SetSem-weaken ψ ⊢F) | (SetSem-weaken ψ ⊢G)  = ≡.refl
  SetSem-weaken ψ (×-I ⊢F ⊢G) rewrite (SetSem-weaken ψ ⊢F) | (SetSem-weaken ψ ⊢G)  = ≡.refl
  SetSem-weaken ψ (Nat-I {αs = αs} {F} {G} ⊢F ⊢G) rewrite (SetSem-weaken ψ ⊢F) | (SetSem-weaken ψ ⊢G)  = ≡.refl

  -- goal : eval ∘F (fixH ∘F TEnv ⊢F                   ※ SetSemVec ⊢Gs) ≡
  --        eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (foreach-preserves-weakening Gs ⊢Gs))
  -- 
  -- 
  SetSem-weaken ψ (μ-I {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) rewrite (SetSem-weaken-TEnv φ αs ψ ⊢F) | (SetSem-weaken-Vec ψ ⊢Gs) = ≡.refl
  -- or more explictly, 
  --     let 
  --         Gs≡wGs = SetSem-weaken-Vec ψ ⊢Gs 
  --         fixF≡fixwF = ≡.cong (_∘F_ fixH) (SetSem-weaken-TEnv φ αs ψ ⊢F)
  --         fixF※Gs≡fixwF※wGs = ≡.cong₂ _※_ fixF≡fixwF Gs≡wGs
  --       in ≡.cong (_∘F_ eval) fixF※Gs≡fixwF※wGs


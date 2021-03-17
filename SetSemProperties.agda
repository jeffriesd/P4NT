open import NestedSyntax6NoStrings 
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
open import SetCatslzero
open import Utils
open import EnvironmentsInnerRecCleanupExt
open import HFixFunctorLib using (fixH)

open import NestedSemanticsFunctorCleanup 



module SetSemProperties where 



-- extendSetEnv-refl  : ∀  {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
--               → (extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ))
--               ≡ (extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ))
-- extendSetEnv-refl φ αs = ≡.refl 
-- {x = (extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ))}


mutual 
-- weakning for full functors 

  -- type syntax definitions 

  -- weakenTCCtx  : ∀ {k : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φ : TCVar k)  (F : TypeExpr)
  --                 → Γ ≀ Φ ⊢ F
  --                 → Γ ,, φ ≀ Φ ⊢ F
  -- 
  -- 
  -- weakenTCCtxVec :  ∀ {k n : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φs : Vec (TCVar k) n)  (F : TypeExpr)
  --                   → Γ ≀ Φ ⊢ F
  --                   -- → (¬ (Γ ∋ φ))
  --                   → Γ ,++ φs ≀ Φ ⊢ F
  -- weakenTCCtxVec {n = zero} [] F ⊢F = ⊢F
  -- weakenTCCtxVec {n = suc n} (φ ∷ φs) F ⊢F = weakenTCCtx  φ F (weakenTCCtxVec φs F ⊢F)

  -- foreach-preserves-weakening  : ∀ {k n : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : TCVar k}
  --                                   → (Gs : Vec TypeExpr n)
  --                                   → foreach (λ G → Γ ≀ Φ ⊢ G) Gs
  --                                   → foreach (λ G → Γ ,, φ ≀ Φ ⊢ G) Gs

-- {-
  SetSem-weaken-TEnvProd : ∀ {Γ : TCCtx} →  {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                    → {j : ℕ} (ψ : TCVar j)
                    → (⊢F : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ F)
                    → TEnvProd ⊢F
                      ≡ TEnvProd (weakenTCCtx ψ F ⊢F)

  SetSem-weaken-TEnvProd {Γ} {F} {k} φ αs ψ ⊢F = ≡.cong (λ G → G ∘F (extendTEnv2 φ αs)) (SetSem-weaken ψ ⊢F)
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
  SetSem-weaken-curry {Γ} {F} {k} φ αs ψ ⊢F rewrite (≡.cong curry.F₀ (SetSem-weaken-TEnvProd φ αs ψ ⊢F)) = ≡.refl 
                                                

  SetSem-weaken-curry2 : ∀ {Γ : TCCtx} →  {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                    → {j : ℕ} (ψ : TCVar j)
                    → (⊢F : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ F)
                    → curry.F₀ (curry.F₀ (TEnvProd ⊢F))
                      ≡ curry.F₀ (curry.F₀ (TEnvProd (weakenTCCtx ψ F ⊢F)))
  SetSem-weaken-curry2 {Γ} {F} {k} φ αs ψ ⊢F rewrite (≡.cong curry.F₀ (SetSem-weaken-curry φ αs ψ ⊢F)) = ≡.refl 
                                                
                    
  SetSem-weaken-TEnv : ∀ {Γ : TCCtx} →  {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                    → {j : ℕ} (ψ : TCVar j)
                    → (⊢F : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ F)
                    → TEnv ⊢F
                      ≡ TEnv (weakenTCCtx ψ F ⊢F)
  -- SetSem-weaken-TEnv {Γ} {F} {k} φ αs ψ ⊢F rewrite (SetSem-weaken-curry2 φ αs ψ ⊢F) = ≡.refl
  SetSem-weaken-TEnv {Γ} {F} {k} φ αs ψ ⊢F = SetSem-weaken-curry2 φ αs ψ ⊢F
 --  -}



-- -- for reference 
-- NatTypeSem : ∀ {n : ℕ} {Γ : TCCtx} {F G : TypeExpr} {αs : Vec (FVar 0) n} (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G) 
--           → Functor SetEnvCat Sets
-- NatTypeSem ⊢F ⊢G = record
--   { F₀ = λ ρ → NatType ⊢F ⊢G (NatEnv ρ)
--   ; F₁ = λ { f NatT[ nat ] → NatT[ make-NT-eq (nat-extend-lem f ⊢F) (nat-extend-lem f ⊢G) nat ] } 
--   ; identity = ≡.refl
--   ; homomorphism = λ { {ρ1} {ρ2} {ρ3} {f} {g} {NatT[ nat ]}
--        → ≡.cong NatT[_] (make-NT-eq-comp (nat-extend-lem f ⊢F) (nat-extend-lem f ⊢G) 
--                                          (nat-extend-lem g ⊢F) (nat-extend-lem g ⊢G) 
--                                          (nat-extend-lem (g ∘SetEnv f) ⊢F) (nat-extend-lem (g ∘SetEnv f) ⊢G) nat)  }

--   ; F-resp-≈ = λ { {ρ} {ρ'} {f} {g} f≈g {NatT[ nat ]} → ≡.cong NatT[_] (make-NT-eq-lem (nat-extend-lem f ⊢F) (nat-extend-lem g ⊢F) (nat-extend-lem f ⊢G) (nat-extend-lem g ⊢G) nat)  }
--   } 
  

-- -- for reference 
-- record NatType {n} {Γ} {F G} {αs} ⊢F ⊢G ρ where
--   constructor NatT[_]
--   eta-equality
--   field
--     nat : NaturalTransformation (extendSetSem-αs αs ρ ⊢F) (extendSetSem-αs αs ρ ⊢G)


-- extendSetSem-αs : ∀ {k} {Γ} {Φ} {H} → (αs : Vec (FVar 0) k) → SetEnv
--               → (⊢H : Γ ≀ Φ ,++ αs ⊢ H)
--               → Functor (Sets^ k) Sets
-- extendSetSem-αs {k} {Γ} {Φ} {H} αs ρ ⊢H = SetSem {Γ} {Φ ,++ αs} {H} ⊢H  ∘F extendSetEnv-αs αs ρ 


  extendSetSem-αs-weaken  : ∀ {k j} {Γ} {Φ} {F} → (ψ : TCVar j) 
                            → (αs : Vec (FVar 0) k) → (ρ : SetEnv)
                            → (⊢F : Γ ≀ Φ ,++ αs ⊢ F) 
                            → extendSetSem-αs αs ρ ⊢F
                            ≡ extendSetSem-αs αs ρ (weakenTCCtx ψ F ⊢F)
  extendSetSem-αs-weaken ψ αs ρ ⊢F rewrite (SetSem-weaken ψ ⊢F) = ≡.refl 


  -- goal : NatTypeSem ⊢F ⊢G ≡ NatTypeSem (weakenTCCtx ψ F ⊢F) (weakenTCCtx ψ G ⊢G)
  -- i.e., need to prove functors are equal... 
  NatTypeSem-weaken : ∀ {Γ} {k j}  {F} {G} 
                      → (ψ : TCVar j) → (αs : Vec (FVar 0) k)
                      → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F)
                      → (⊢G : Γ ≀ ∅ ,++ αs ⊢ G) 
                      → SetSem {Γ}      {∅ ,++ αs} (Nat-I ⊢F ⊢G) 
                      ≡ SetSem {Γ ,, ψ} {∅ ,++ αs} (weakenTCCtx ψ Nat^ αs [ F , G ] (Nat-I ⊢F ⊢G))
  NatTypeSem-weaken ψ αs ⊢F ⊢G  = {!   !}

  NatTypeSem-weaken-obj : ∀ {Γ} {k j}  {F} {G} 
                      → (ψ : TCVar j) → (αs : Vec (FVar 0) k)
                      → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F)
                      → (⊢G : Γ ≀ ∅ ,++ αs ⊢ G) 
                      → (ρ : SetEnv)
                      → NatType ⊢F ⊢G (NatEnv ρ)
                      ≡ NatType (weakenTCCtx ψ F ⊢F) (weakenTCCtx ψ G ⊢G) (NatEnv ρ)
  NatTypeSem-weaken-obj {F = F} {G} ψ αs ⊢F ⊢G ρ rewrite (extendSetSem-αs-weaken ψ αs ρ ⊢F) | (extendSetSem-αs-weaken ψ αs ρ ⊢G)
    = {!   !} 
-- NaturalTransformation (extendSetSem-αs αs ρ ⊢F) (extendSetSem-αs αs ρ ⊢G)

  NatTypeSem-weaken-NT : ∀ {Γ} {k j}  {F} {G} 
                      → (ψ : TCVar j) → (αs : Vec (FVar 0) k)
                      → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F)
                      → (⊢G : Γ ≀ ∅ ,++ αs ⊢ G) 
                      → (ρ : SetEnv)
                      → NaturalTransformation (extendSetSem-αs αs ρ ⊢F) (extendSetSem-αs αs ρ ⊢G)
                      ≡ NaturalTransformation (extendSetSem-αs αs ρ (weakenTCCtx ψ F ⊢F)) (extendSetSem-αs αs ρ (weakenTCCtx ψ G ⊢G))
  NatTypeSem-weaken-NT ψ αs ⊢F ⊢G ρ rewrite (extendSetSem-αs-weaken ψ αs ρ ⊢F) | (extendSetSem-αs-weaken ψ αs ρ ⊢G) = ≡.refl 
 

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

  SetSem-weaken ψ (+-I ⊢F ⊢G) = ≡.cong (_∘F_ SetSum)  (≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) (SetSem-weaken ψ ⊢G))
  SetSem-weaken ψ (×-I ⊢F ⊢G) = ≡.cong (_∘F_ SetProd) (≡.cong₂ _※_ (SetSem-weaken ψ ⊢F) (SetSem-weaken ψ ⊢G))
  SetSem-weaken ψ (Nat-I {αs = αs} {F} {G} ⊢F ⊢G) = NatTypeSem-weaken ψ αs ⊢F ⊢G 
  -- goal : NatTypeSem ⊢F ⊢G 
  --      ≡ NatTypeSem (weakenTCCtx ψ F ⊢F) (weakenTCCtx ψ G ⊢G)


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


-- mutual
  SetSem-demotion-Vec : ∀ {n : ℕ} {Γ : TCCtx} → {Φ : FunCtx} → {Fs : Vec TypeExpr n}
                        → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
                        → (⊢Fs : foreach (λ F → Γ ≀ Φ ,, φ ⊢ F) Fs)
                        → VarSem-FV φ ≡ VarSem-TC ψ
                      → SetSemVec ⊢Fs
                        ≡ SetSemVec (demoteVec-preserves-typing {φ = φ} {ψ} Fs ⊢Fs)
  SetSem-demotion-Vec {zero} {Fs = []} φ ψ Data.Unit.tt e = ≡.refl
  -- ≡.refl
  SetSem-demotion-Vec {suc n} {Fs = F ∷ Fs} φ ψ (⊢F , ⊢Fs) e = 
    let Fs≡wFs = SetSem-demotion-Vec φ ψ ⊢Fs e 
        F※Fs≡wF※wFs = ≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F e) Fs≡wFs
        in ≡.cong (_∘F_ (Sets^cons n)) F※Fs≡wF※wFs

  SetSem-demotion : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
                    → (⊢F : Γ ≀ Φ ,, φ ⊢ F)
                    → VarSem-FV φ ≡ VarSem-TC ψ
                    -- maybe relax this and use ≈ from SEC 
                    → SetSem ⊢F
                      ≡ SetSem (demotion-preserves-typing {φ = φ} {ψ} F ⊢F)
  SetSem-demotion φ ψ 𝟘-I ρφ≡ρψ = ≡.refl
  SetSem-demotion φ ψ 𝟙-I ρφ≡ρψ = ≡.refl
  SetSem-demotion φ ψ (AppT-I {φ = ϕ} Γ∋p  Fs ⊢Fs) ρφ≡ρψ = 
  -- goal : eval ∘F (VarSem-TC p ※ SetSemVec ⊢Fs) 
  --        ≡ eval ∘F (VarSem-TC p ※ SetSemVec (demoteVec-preserves-typing Fs ⊢Fs))
    let Fs≡wFs = SetSem-demotion-Vec φ ψ ⊢Fs ρφ≡ρψ
        eq-※ = ≡.cong (_※_ (VarSem-TC ϕ)) Fs≡wFs
        in ≡.cong (_∘F_ eval) eq-※
-- goal : eval ∘F (VarSem-FV p ※ SetSemVec ⊢Fs) ≡ 
-- SetSem
--       (demotion-preserves-typing AppF p [ Fs ] (AppF-I Γ∋p Fs ⊢Fs))

  SetSem-demotion (φ ^F k) (ψ ^T k) (AppF-I {φ = ϕ ^F j} Γ∋p  Fs ⊢Fs) ρφ≡ρψ rewrite (SetSem-demotion-Vec (φ ^F k) (ψ ^T k) ⊢Fs ρφ≡ρψ)
      with eqNat j k | ϕ ≟ φ

--   SetSem-demotion {k = k} (φ ^F k) ψ (AppF-I {φ = φ2 ^F j} Φ∋φ2 Fs ⊢Fs) ρ ρφ≡ρψ with eqNat j k | φ2 ≟ φ
-- 
--
-- yes yes goal : 
-- eval ∘F (VarSem-FV (φ ^F k) ※ SetSemVec ⊢Fs) 
-- ≡ eval ∘F (VarSem-TC (ψ ^T k) ※ SetSemVec (demoteVec-preserves-typing Fs ⊢Fs))
  ... | yes ≡.refl | yes ≡.refl rewrite ρφ≡ρψ = ≡.refl
  ... | yes ≡.refl | no _  = ≡.refl
  ... | no _ | yes ≡.refl   = ≡.refl
  ... | no _ | no _  = ≡.refl
-- -- SetSum ∘F (SetSem ⊢F ※ SetSem ⊢G) ≡
--     SetSum ∘F
--     (SetSem (demotion-preserves-typing F ⊢F) ※
--      SetSem (demotion-preserves-typing G ⊢G))
  SetSem-demotion φ ψ (+-I ⊢F ⊢G) ρφ≡ρψ = ≡.cong (_∘F_ SetSum)  (≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F ρφ≡ρψ ) (SetSem-demotion φ ψ ⊢G ρφ≡ρψ ))
  SetSem-demotion φ ψ (×-I ⊢F ⊢G) ρφ≡ρψ = ≡.cong (_∘F_ SetProd) (≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F ρφ≡ρψ ) (SetSem-demotion φ ψ ⊢G ρφ≡ρψ ))
  SetSem-demotion φ ψ (Nat-I ⊢F ⊢G) ρφ≡ρψ = {!   !}
  SetSem-demotion φ ψ (μ-I {φ = ϕ} {αs = αs} F ⊢F Gs ⊢Gs) ρφ≡ρψ 
        rewrite (SetSem-weaken-TEnv ϕ αs ψ ⊢F) | (SetSem-demotion-Vec φ ψ ⊢Gs ρφ≡ρψ) = ≡.refl 

  -- {! eval ∘F (fixH ∘F TEnv ⊢F ※ SetSemVec ⊢Gs) ≡ eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (demoteVec-preserves-typing Gs ⊢Gs)) !} 
-- goal : eval ∘F (fixH ∘F TEnv ⊢F                   ※ SetSemVec ⊢Gs) ≡
--        eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (demoteVec-preserves-typing Gs ⊢Gs))

  -- rewrite (SetSem-weaken-TEnv φ αs ψ ⊢F) | (SetSem-weaken-Vec ψ ⊢Gs) = ≡.refl





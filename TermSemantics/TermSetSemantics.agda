{-# OPTIONS --allow-unsolved-metas #-} 
module TermSemantics.TermSetSemantics where


open import Categories.Functor using (Functor ; _∘F_)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.Category using (Category)
open import Categories.Category.Product

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Unit renaming (⊤ to ⊤')
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Vec using (Vec ; [] ; _∷_ ; _++_)
open import Data.Sum renaming ([_,_] to [_,⊎_])
open import Data.Product renaming (_×_ to _×'_  ; map to ×'-map)
open import Function using (const ; flip) renaming (id to idf; _∘_ to _∘'_)
open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary using (_because_ ; Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (isYes)

open import SetEnvironments.Core using (SetEnvCat ; SetEnv)
open import SetEnvironments.EnvironmentExtension using (extendSetEnv-αs)
open import SetCats
open import TypeSemantics.SetSemantics
open import TypeSemantics.SetSem-properties using (extendEnvFVar)
open import Syntax.NestedTypeSyntax
open import Syntax.TermSyntax
open import Utils using (exFalso ; ×'-cong ; cong-app-impl ; bigtt)
-- open import TermSemantics.TermSetSemUtils using () hiding (curryNatType) 
open import SetEnvironments.Core
-- open import HFixFunctorLib using (HFixFunctorObj)


private
  variable
    o l e : Level
    C : Category o l e


-- interpretation of term context Δ is given as the product 
-- of the functors interpreting the types in Δ 
ContextInterp : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx Γ Φ 
                → Functor SetEnvCat Sets 
ContextInterp Δ∅ = ConstF ⊤'
ContextInterp (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) = ContextInterp Δ ×Set SetSem ⊢F



𝟘! : ∀ {F : Functor C Sets} 
      → NaturalTransformation (ConstF ⊥') F
𝟘! = record { η = λ _ → exFalso ;  commute = λ f → λ{} ; sym-commute = λ f → λ {} } 

𝟙! : ∀ {F : Functor C Sets} 
      → NaturalTransformation F (ConstF ⊤') 
𝟙! = record { η = λ _ → const tt ;  commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl } 


inl-Nat : ∀ {F G : Functor C Sets}
          → NaturalTransformation F ((F +Set G))
inl-Nat = record { η = λ _ → inj₁  ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl }

inr-Nat : ∀ {F G : Functor C Sets}
          → NaturalTransformation G ((F +Set G))
inr-Nat = record { η = λ _ → inj₂ ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl }


proj₁-commute : ∀ {F G : Functor C Sets} {X Y : Category.Obj C}
                (f : C Categories.Category.[ X , Y ])
                → Sets Categories.Category.[ 
                  proj₁ ∘' (Functor.F₁ (F ×Set G) f)
                ≈ Functor.F₁ F f ∘' proj₁  ]
proj₁-commute f {fst , snd} = ≡.refl 


proj₁Nat : ∀ {F G : Functor C Sets}
          → NaturalTransformation ((F ×Set G)) F
proj₁Nat {o} {l} {e} {C = C} {F} {G} = record { η = λ _ → proj₁ ; commute = λ f {x} → proj₁-commute {C = C} {F} {G} f {x} ; sym-commute = λ f {x} → ≡.sym (proj₁-commute {C = C} {F} {G} f {x}) } 


proj₂-commute : ∀ {F G : Functor C Sets} {X Y : Category.Obj C}
                (f : C Categories.Category.[ X , Y ])
                → Sets Categories.Category.[ 
                  proj₂ ∘' (Functor.F₁ ((F ×Set G)) f)
                ≈ Functor.F₁ G f ∘' proj₂  ]
proj₂-commute f {fst , snd} = ≡.refl 


proj₂Nat : ∀ {F G : Functor C Sets}
          → NaturalTransformation (F ×Set G) G
proj₂Nat {o} {l} {e} {C = C} {F} {G} = record { η = λ X → proj₂ ; commute = λ f {x} → proj₂-commute {C = C} {F} {G} f {x} ; sym-commute = λ f {x} → ≡.sym (proj₂-commute {C = C} {F} {G} f {x}) } 




prod-Nat-commute : ∀ {F G H : Functor C Sets} 
                    → (η₁ : NaturalTransformation F G)
                    → (η₂ : NaturalTransformation F H) 
                    → {X Y : Category.Obj C}
                    → (f : C Categories.Category.[ X , Y ]) 
                    → Sets Categories.Category.[ 
                      < NaturalTransformation.η η₁ Y , NaturalTransformation.η η₂ Y >
                      ∘' (Functor.F₁ F f)
                    ≈ 
                      (Functor.F₁ ((G ×Set H)) f)
                      ∘' < NaturalTransformation.η η₁ X , NaturalTransformation.η η₂ X >
                    ]
prod-Nat-commute η₁ η₂ f = ×'-cong (NaturalTransformation.commute η₁ f) (NaturalTransformation.commute η₂ f) 



prod-Nat : ∀ {F G H : Functor C Sets}
          → NaturalTransformation F G
          → NaturalTransformation F H
          → NaturalTransformation F ((G ×Set H))
prod-Nat η₁ η₂ = 
    record { η = λ X → < (NaturalTransformation.η η₁ X)  , (NaturalTransformation.η η₂ X ) > 
            ; commute     = λ f → prod-Nat-commute η₁ η₂ f 
            ; sym-commute = λ f → ≡.sym (prod-Nat-commute η₁ η₂ f) } 


prod-Nat2-commute : ∀ {F1 G1 F2 G2 : Functor C Sets} (η₁ : NaturalTransformation F1 G1)
                      (η₂ : NaturalTransformation F2 G2) {X Y : Category.Obj C}
                      (f : C Categories.Category.[ X , Y ]) 
                      → Sets Categories.Category.[ 
                        ×'-map (NaturalTransformation.η η₁ Y) (NaturalTransformation.η η₂ Y)
                          ∘' (Functor.F₁ (F1 ×Set F2) f)
                        ≈ (Functor.F₁ (G1 ×Set G2) f)
                        ∘' (×'-map (NaturalTransformation.η η₁ X) (NaturalTransformation.η η₂ X)) ]
prod-Nat2-commute η₁ η₂ f {x , y} = ×'-cong (NaturalTransformation.commute η₁ f) (NaturalTransformation.commute η₂ f) 



prod-Nat2 : ∀ {F1 G1 F2 G2 : Functor C Sets}
          → NaturalTransformation F1 G1
          → NaturalTransformation F2 G2
          → NaturalTransformation (F1 ×Set F2) (G1 ×Set G2)
prod-Nat2 {F1 = F1} {G1} {F2} {G2} η₁ η₂ = 
    record { η = λ X → ×'-map (NaturalTransformation.η η₁ X) (NaturalTransformation.η η₂ X) 
            ; commute = λ f → prod-Nat2-commute η₁ η₂ f 
            ; sym-commute = λ f → ≡.sym (prod-Nat2-commute η₁ η₂ f) } 


-- prod-Nat-gen : ∀ {F G H : Functor C Sets}
--           → NaturalTransformation F G
--           → NaturalTransformation F H
--           → NaturalTransformation F (SetProd ∘F (G ※ H))


sum-Nat-commute : ∀ {F G H : Functor C Sets} 
                  → (η₁ : NaturalTransformation F H)
                   → (η₂ : NaturalTransformation G H) 
                  → {X Y : Category.Obj C}
                  → (f : C Categories.Category.[ X , Y ]) 
                  → Sets Categories.Category.[
                    [ NaturalTransformation.η η₁ Y ,⊎ NaturalTransformation.η η₂ Y ]
                    ∘' Functor.F₁ ((F +Set G)) f
                    ≈ 
                      Functor.F₁ H f 
                      ∘' [ NaturalTransformation.η η₁ X ,⊎ NaturalTransformation.η η₂ X ]
                  ]
sum-Nat-commute {F = F} {G} {H} η₁ η₂ {X} {Y} f {inj₁ x} = NaturalTransformation.commute η₁ f
sum-Nat-commute {F = F} {G} {H} η₁ η₂ {X} {Y} f {inj₂ y} = NaturalTransformation.commute η₂ f 

-- -- this doesn't quite work 
-- curry-Nat : ∀ {F G H : Functor C Sets}
--           → NaturalTransformation (F ×Set G) H 
--           → NaturalTransformation F (ConstF (NaturalTransformation G H))
-- curry-Nat {F = F} {G} {H} η = {!   !}
--         -- record { η = λ X fx → record { η = λ Y gy → NaturalTransformation.η η Y ({!   !} , gy) ; commute = {!   !} ; sym-commute = {!   !} } 
--         --         ; commute = {!   !} 
--         --         ; sym-commute = {!   !} } 


sum-Nat : ∀ {F G H : Functor C Sets}
          → NaturalTransformation F H
          → NaturalTransformation G H
          → NaturalTransformation ((F +Set G)) H
sum-Nat η₁ η₂ = 
    record { η = λ X → [ (NaturalTransformation.η η₁ X) ,⊎ (NaturalTransformation.η η₂ X ) ] 
            ; commute     = λ f {x} → sum-Nat-commute η₁ η₂ f {x}
            ; sym-commute = λ f {x} → ≡.sym (sum-Nat-commute η₁ η₂ f {x}) }


var-interp : ∀ {Γ : TCCtx} {Φ : FunCtx} 
              → (Δ : TermCtx Γ Φ)
              → {x : TermId}
              → {F : TypeExpr}
              → (⊢F : Γ ≀ Φ ⊢ F)
              → {p : isYes (Δ-lookup x Δ) ≡ false}
              → NaturalTransformation (ContextInterp (Δ ,- x ∶ ⊢F ⟨ p ⟩)) 
                                      (SetSem ⊢F)
var-interp Δ ⊢F = proj₂Nat {F = ContextInterp Δ} {G = SetSem ⊢F}


open import TypeSemantics.SetSemWeakenFunCtx using (SetSem-weakenFunCtx-NT)

weaken-Δ-NT : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (α : FVar k)
            → (Δ : TermCtx Γ Φ)
            → NaturalTransformation (ContextInterp Δ) (ContextInterp (weakenFunCtx-Δ α Δ))
weaken-Δ-NT α Δ∅ = idnat
weaken-Δ-NT α (Δ ,- x ∶ ⊢F ⟨ p ⟩) = 
    let rec : NaturalTransformation (ContextInterp Δ) (ContextInterp (weakenFunCtx-Δ α Δ))
        rec = weaken-Δ-NT α Δ 
        w : NaturalTransformation (SetSem ⊢F) (SetSem (weakenFunCtximpl α ⊢F))
        w = SetSem-weakenFunCtx-NT α ⊢F 
      in prod-Nat2 rec w  
  
weaken-Δ-Vec-NT : ∀ {k n} {Γ : TCCtx} {Φ : FunCtx} (αs : Vec (FVar k) n)
            → (Δ : TermCtx Γ Φ)
            → NaturalTransformation (ContextInterp Δ) (ContextInterp (weakenFunCtx-Δ-Vec αs Δ))
weaken-Δ-Vec-NT []       Δ = idnat
weaken-Δ-Vec-NT (α ∷ αs) Δ = weaken-Δ-NT α (weakenFunCtx-Δ-Vec αs Δ) ∘v weaken-Δ-Vec-NT αs Δ


weakenFunCtx-Δ-∅-NT  : ∀ { Γ : TCCtx } → (Φ : FunCtx)
                       → (Δ : TermCtx Γ ∅)
                       → NaturalTransformation (ContextInterp Δ) (ContextInterp (weakenFunCtx-Δ-∅ Φ Δ))
weakenFunCtx-Δ-∅-NT ∅ Δ = idnat 
weakenFunCtx-Δ-∅-NT (Φ ,, φ) Δ = weaken-Δ-NT φ (weakenFunCtx-Δ-∅ Φ Δ)  ∘v   weakenFunCtx-Δ-∅-NT Φ Δ 





open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
import Categories.NaturalTransformation.NaturalIsomorphism as NI

-- open import TermSemantics.NatTermSemantics as NTS
-- open NTS.DConstNaturalIso using (DConst≃DExtend ; ContextInterp-Forget-iso)


postulate 
    DConst≃DExtend : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : SetEnv) (αs : Vec (FVar 0) k) 
                → ConstF {C = Sets^ k} (Functor.F₀ (ContextInterp Δ) ρ)
                ≃ ContextInterp Δ ∘F extendSetEnv-αs αs (NatEnv ρ)

    ContextInterp-Forget-iso : ∀ {Γ} → (Δ : TermCtx Γ ∅) 
                              → ContextInterp Δ
                              ≃ ContextInterp Δ ∘F ForgetFVSetEnv

    -- curryNatType : ∀ {Γ} {k} (αs : Vec (FVar 0) k) {F} {G} (Δ : TermCtx Γ ∅)
    --             → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G)
    --             → NaturalTransformation ((ContextInterp Δ) ×Set (SetSem ⊢F)) (SetSem ⊢G)
    --             → NaturalTransformation (ContextInterp Δ) (NatTypeFunctor αs ⊢F ⊢G)

    curryNatType : ∀ {Γ Φ} {Δ : TermCtx Γ ∅} {k} {αs : Vec (FVar 0) k} {F} {G}
            → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G)
            → NaturalTransformation (ContextInterp (weakenFunCtx-Δ-Vec αs Δ) ×Set SetSem ⊢F) (SetSem ⊢G)
            → NaturalTransformation (ContextInterp Δ) (SetSem {Γ} {Φ} (Nat-I ⊢F ⊢G))


    SetSem-extendFunCtx-NT : ∀ {Γ} {Φ} {F} {H} {α : FVar 0} (⊢F : Γ ≀ (Φ ,, α) ⊢ F)
                             → (⊢H : Γ ≀ Φ ⊢ H)
                             → NaturalTransformation
                                (SetSem {Γ} {Φ} {F [ α := H ] } (fo-subst-preserves-typing {Γ} {Φ} {α} ⊢F ⊢H))
                                ((SetSem {Γ} {Φ ,, α} {F} ⊢F) ∘F extendEnvFVar {Γ} {Φ} {H} α ⊢H)



-- semantics of abstraction
-- Lsem : ∀ {Γ Φ} {Δ : TermCtx Γ ∅} {k} {αs : Vec (FVar 0) k} {F} {G}
--         → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G)
--         → NaturalTransformation (ContextInterp (weakenFunCtx-Δ-Vec αs Δ) ×Set SetSem ⊢F) (SetSem ⊢G)
--         → NaturalTransformation (ContextInterp Δ) (SetSem {Γ} {Φ} (Nat-I ⊢F ⊢G))
-- Lsem {Γ} {Δ = Δ} {αs = αs} ⊢F ⊢G semt =
  -- let w-semt : NaturalTransformation (ContextInterp Δ ×Set SetSem ⊢F) (SetSem ⊢G)
  --     w-semt = semt ∘v prod-Nat2 (weaken-Δ-Vec-NT αs Δ) idnat
  --   in curryNatType αs Δ ⊢F ⊢G w-semt



--- SetSem-weakenFunCtx-∅-,++-NT : ∀ {k n} {Γ : TCCtx} (Φ : FunCtx) → (φs : Vec (FVar k) n)
---                     → {F : TypeExpr} → (⊢F : Γ ≀ (∅ ,++ φs) ⊢ F)
---                     → NaturalTransformation (SetSem ⊢F)
---                                             (SetSem (weakenFunCtx-∅-,++ {Φ = Φ} φs ⊢F))


TermSetSem : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx Γ Φ}
            → {F : TypeExpr} → {⊢F : Γ ≀ Φ ⊢ F}
            → {t : TermExpr}
            →  (⊢t : Γ ≀ Φ ∣ Δ ⊢ t ∶ ⊢F)
            → NaturalTransformation (ContextInterp Δ) (SetSem ⊢F)
TermSetSem (var-I Δ x ⊢F p) = var-interp Δ {x} ⊢F {p = p}
TermSetSem (⊥e-I _ _ t ⊢t) = 𝟘! ∘v TermSetSem ⊢t
TermSetSem (⊤-I _) = 𝟙!
TermSetSem (inl-I _ ⊢F ⊢G t ⊢t) = inl-Nat ∘v TermSetSem ⊢t
TermSetSem (inr-I _ ⊢F ⊢G t ⊢t) = inr-Nat ∘v TermSetSem ⊢t
TermSetSem (case-I Δ ⊢F ⊢G ⊢K _ ⊢t _ _ _ ⊢l _ _ _ ⊢r)  =
  let ⟦Δ⟧ : Functor SetEnvCat Sets
      ⟦Δ⟧ = ContextInterp Δ
      ⟦F⟧ : Functor SetEnvCat Sets
      ⟦F⟧ = SetSem ⊢F 
      ⟦G⟧ : Functor SetEnvCat Sets
      ⟦G⟧ = SetSem ⊢G

      [l,r] : NaturalTransformation ((⟦Δ⟧ ×Set ⟦F⟧) +Set (⟦Δ⟧ ×Set ⟦G⟧)) (SetSem ⊢K)
      [l,r] = sum-Nat (TermSetSem ⊢l) (TermSetSem ⊢r)

      distr : NaturalTransformation (⟦Δ⟧ ×Set (⟦F⟧ +Set ⟦G⟧))
                                    ((⟦Δ⟧ ×Set ⟦F⟧) +Set (⟦Δ⟧ ×Set ⟦G⟧))
      distr = ×Set-distr ⟦Δ⟧ ⟦F⟧ ⟦G⟧

      semt : NaturalTransformation ⟦Δ⟧ (⟦F⟧ +Set ⟦G⟧)
      semt = TermSetSem ⊢t

      ⟦Δ⟧×tsem : NaturalTransformation ⟦Δ⟧ (⟦Δ⟧ ×Set (⟦F⟧ +Set ⟦G⟧))
      ⟦Δ⟧×tsem = prod-Nat idnat (TermSetSem ⊢t)

      --   ⟦Δ⟧
      -- → ⟦Δ⟧ × (⟦F⟧ + ⟦G⟧)
      -- → (⟦Δ⟧ + ⟦F⟧) × (⟦Δ⟧ + ⟦G⟧)
      -- → 
      -- goal : NaturalTransformation (ContextInterp Δ) (SetSem ⊢K)
      -- goal = {! [l,r] ∘v distr ∘v ⟦Δ⟧×tsem!} 

    in [l,r] ∘v distr ∘v ⟦Δ⟧×tsem

TermSetSem (pair-I _ ⊢F ⊢G _ ⊢s _ ⊢t) = prod-Nat (TermSetSem ⊢s) (TermSetSem ⊢t)
TermSetSem (π₁-I _ _ ⊢G t ⊢t) = proj₁Nat ∘v TermSetSem ⊢t
TermSetSem (π₂-I _ ⊢F _ t ⊢t) = proj₂Nat ∘v TermSetSem ⊢t


-------------------------------------------------------

-- abstraction case
TermSetSem {Γ} {Φ} (L-I {αs = αs} ⊢F ⊢G Δ x p t ⊢t) = curryNatType {Γ = Γ} {Φ = Φ} ⊢F ⊢G (TermSetSem ⊢t)


-- application case 
--
-- t : Nat F G
-- s : F [ K ] 
TermSetSem {Γ} {Φ} (app-I {F = F} {G} ⊢F ⊢G _ Δ t ⊢t s ⊢s) = {!!}
-- TermSetSem {Γ} {Φ} (app-I {αs = []} {F = F} {G} {Ks = []} ⊢F ⊢G _ Δ t ⊢t s ⊢s) = {!!}
{-
TermSetSem {Γ} {Φ} (app-I {αs = []} {F = F} {G} {Ks = []} ⊢F ⊢G _ Δ t ⊢t s ⊢s) = {!!}
TermSetSem {Γ} {Φ} (app-I {αs = α ∷ []} {F = F} {G} {Ks = K ∷ []} ⊢F ⊢G (⊢K , bigtt)  Δ t ⊢t s ⊢s) = 
  let semt : NaturalTransformation (ContextInterp Δ) (NatTypeFunctor (α ∷ []) ⊢F ⊢G)
      semt = TermSetSem ⊢t

      sems : NaturalTransformation (ContextInterp (weakenFunCtx-Δ-∅ Φ Δ))
                                   -- (SetSem ([:=]Vec-preserves-typing (α ∷ []) (K ∷ []) (weakenFunCtx-∅-,++ (α ∷ []) ⊢F) (⊢K , bigtt)))
                                    (SetSem (fo-subst-preserves-typing (weakenFunCtx-∅-,++ (α ∷ []) ⊢F) ⊢K))
      sems = TermSetSem ⊢s

      w-sems : NaturalTransformation (ContextInterp Δ)
                (SetSem (fo-subst-preserves-typing (weakenFunCtx-∅-,++ (α ∷ []) ⊢F) ⊢K))
            
      w-sems = sems ∘v weakenFunCtx-Δ-∅-NT Φ Δ

      subst : NaturalTransformation 
                (SetSem (fo-subst-preserves-typing (weakenFunCtx-∅-,++ (α ∷ []) ⊢F) ⊢K))
                (SetSem (weakenFunCtx-∅-,++ {Γ = Γ} {Φ = Φ} (α ∷ []) ⊢F) ∘F extendEnvFVar α ⊢K) 
      subst =  SetSem-extendFunCtx-NT {Γ} {Φ} {F} {K} {α} (weakenFunCtx-∅-,++ {Γ = Γ} {Φ = Φ} (α ∷ []) ⊢F) ⊢K  


      weaken-F : NaturalTransformation 
                (SetSem (weakenFunCtx-∅-,++ {Γ = Γ} {Φ = Φ} (α ∷ []) ⊢F))
                (SetSem ⊢F)
      weaken-F = {!!} 

      weaken-F-subst : NaturalTransformation 
                (SetSem (weakenFunCtx-∅-,++ {Γ = Γ} {Φ = Φ} (α ∷ []) ⊢F) ∘F extendEnvFVar α ⊢K) 
                (SetSem ⊢F ∘F extendEnvFVar α ⊢K) 
      weaken-F-subst = weaken-F ∘ʳ (extendEnvFVar α ⊢K)  

      sems' : NaturalTransformation (ContextInterp Δ) (SetSem ⊢F ∘F extendEnvFVar α ⊢K) 
      sems' = weaken-F-subst ∘v subst ∘v w-sems

      prod : NaturalTransformation (ContextInterp Δ)
                                   ((SetSem ⊢F ∘F extendEnvFVar α ⊢K) ×Set (NatTypeFunctor (α ∷ []) ⊢F ⊢G))
      -- prod = {!prod-Nat {C = SetEnvCat} {F = ContextInterp Δ} {G = (SetSem ⊢F ∘F extendEnvFVar α ⊢K)} {H = (NatTypeFunctor (α ∷ []) ⊢F ⊢G)} sems' semt   !} 
      prod = prod-Nat {F = ContextInterp Δ} {G = (SetSem ⊢F ∘F extendEnvFVar α ⊢K)} {H = (NatTypeFunctor (α ∷ []) ⊢F ⊢G)} sems' semt    


      evalNat : NaturalTransformation ((SetSem ⊢F ∘F extendEnvFVar α ⊢K ∘F ForgetFVSetEnv) ×Set (NatTypeFunctor (α ∷ []) ⊢F ⊢G))
                                        (SetSem ⊢G ∘F extendEnvFVar α ⊢K ∘F ForgetFVSetEnv)
      evalNat = record { η = λ { ρ (FρK , NatT2[ nt ]) → NaturalTransformation.η nt (Functor.F₀ (SetSem ⊢K) (NatEnv ρ) ∷ []) FρK }
                       ; commute = λ { f {F , NatT2[ nt ] } → {!   !} } 
                       ; sym-commute = {!!} } 

   in {!evalNat!} 
-}


-- TermSetSem {Γ} {Φ} (app-I {αs = αs} {F = F} {G} {Ks = Ks} ⊢F ⊢G ⊢Ks Δ t ⊢t s ⊢s) = {!!}

{-
Have semt : NaturalTransformation (ContextInterp Δ) (NatTypeFunctor αs ⊢F ⊢G)

Goal: NaturalTransformation (ContextInterp (weakenFunCtx-Δ-∅ Φ Δ))
      (SetSem
       ([:=]Vec-preserves-typing αs Ks (weakenFunCtx-∅-,++ αs ⊢G) ⊢Ks))

Goal: NaturalTransformation (ContextInterp Δ)
      (SetSem ([:=]Vec-preserves-typing αs Ks ⊢G ⊢Ks))


Have semt : NaturalTransformation (ContextInterp Δ) (NatTypeFunctor αs ⊢F ⊢G)
Goal: NaturalTransformation (ContextInterp Δ)
      (SetSem ⊢G ∘F extendSetEnv-SetSemVec αs ⊢Ks)
-}

{- general case 
  let semt : NaturalTransformation (ContextInterp Δ) (NatTypeFunctor αs ⊢F ⊢G)
      semt = TermSetSem ⊢t

      sems : NaturalTransformation (ContextInterp (weakenFunCtx-Δ-∅ Φ Δ))
                                   (SetSem ([:=]Vec-preserves-typing αs Ks (weakenFunCtx-∅-,++ αs ⊢F) ⊢Ks))
      sems = TermSetSem ⊢s

      w-sems : NaturalTransformation (ContextInterp Δ)
                                   (SetSem {Γ} {Φ} ([:=]Vec-preserves-typing αs Ks (weakenFunCtx-∅-,++ αs ⊢F) ⊢Ks))
      w-sems = sems ∘v weakenFunCtx-Δ-∅-NT Φ Δ

      -- fo-substVec lemma gives
      -- (SetSem ([:=]Vec-preserves-typing αs F Ks (weakenFunCtx-∅-,++ αs ⊢F) ⊢Ks))
      -- ≃ (SetSem (weakenFunCtx-∅-,++ αs ⊢F)) ∘F extendEnvFVarVec αs ⊢Ks
      -- weakening lem gives
      -- ≃ (SetSem ⊢F) ∘F extendEnvFVarVec αs ⊢Ks

                          --  → SetSem ([:=]Vec-preserves-typing αs H Gs ⊢H ⊢Gs)
                          --  ≃ SetSem ⊢H ∘F extendEnvFVarVec αs ⊢Gs
      --
      -- w-sems : NaturalTransformation (ContextInterp Δ) (SetSem ⊢

      -- start with
      -- (ContextInterp Δ)
      --  -- use semt × sems
      -- (NatSem .. ) × (SetSem .... F)
      -- -- use evalNat
      -- (SetSem ... G)

    in {!     !}
-}

-- TermSetSem (map-I {k = ℕ.zero} {βs = []} {[]} ⊢H ⊢F ⊢G) =
--   let t : ∀ ρ → NaturalTransformation
--                 (extendSetSem-αs [] (NatEnv ρ) (NatTypeFunctor [] ⊢F ⊢G))
--                 (extendSetSem-αs [] (NatEnv ρ)
--                         (NatTypeFunctor []
--                             (so-subst-preserves-typing ⊢H (FunCtx-resp-++ [] [] ⊢F))
--                             (so-subst-preserves-typing ⊢H (FunCtx-resp-++ [] [] ⊢G))))
--       t ρ = record { η = λ { [] NatT2[ nt ] → NatT2[ (record { η = λ { [] → {!!} }  ; commute = {!!} ; sym-commute = {!!} }) ]  } ; commute = {!!} ; sym-commute = {!!} } 
-- 
--   in record { η = λ ρ tt → NatT2[ {!!} ]
--          ; commute = {!!} ; sym-commute = {!!} }

TermSetSem (map-I {βs = βs} {γs = γs} ⊢H ⊢F ⊢G) = {!!}

-- goal for in-I : NaturalTransformation
--                (extendSetSem-αs βs (NatEnv ρ) (SetSem (in-I-helper2 ⊢H)))
--                (extendSetSem-αs βs (NatEnv ρ) (MuSem ⊢H (SetSemVec (VarTypeVec βs))))
--
-- can use higher-order functoriality of extendSetSem-αs
-- and a natural transformation from
-- (SetSem (in-I-helper2 ⊢H)) to
-- (MuSem ⊢H (SetSemVec (VarTypeVec βs)))
TermSetSem (in-I {Γ = Γ} {φ = φ} {αs = αs} {βs = βs} ⊢H) =
  let f : NaturalTransformation (SetSem (in-I-helper {φ = φ} {αs} {βs} ⊢H)) (MuSem ⊢H (SetSemVec {Γ = Γ} (VarTypeVec {Φ = (∅ ,++ αs) ,, φ} βs)))
      -- codomain  = eval ∘F ((fixH ∘F TEnv ⊢H) ∘F ForgetFVSetEnv ※00 SetSemVec (VarTypeVec βs))

      -- first hole : HFixObj (Functor.F₀ (AbT.TEnv ⊢H) Env[ SetEnv.tc ρ , trivFVSetEnv ])
      --                          (Functor.F₀ (SetSemVec (VarTypeVec βs)) ρ)
      -- x : Functor.F₀ (SetSem (in-I-helper2 ⊢H)) ρ
      -- need to use hin (??? x)
      f = record { η = λ ρ x → {!   !} ; commute = {!   !} ; sym-commute = {!   !} }
    -- need to get from
    -- x : Functor.F₀ (SetSem (in-I-helper2 ⊢H)) ρ
    -- to
    -- Functor.F₀
    --   (Functor.F₀ (Functor.₀ (AbT.TEnv ⊢H) (Functor.₀ ForgetFVSetEnv ρ))
    --    (HFixFunctorLib.fixH₀ (Functor.₀ (AbT.TEnv ⊢H) (Functor.₀ ForgetFVSetEnv ρ))))
    --   (Functor.F₀ (SetSemVec (VarTypeVec βs)) ρ)


    in
    record { η = λ ρ x → NatT2[ {!   !} ] ; commute = {!   !} ; sym-commute = {!   !} }


-- make 
TermSetSem (fold-I {φ = φ} {[]} {[]} ⊢H ⊢F) =
  record { η = λ ρ tt → NatT2[ record { η = λ { [] NatT2[ nat ] → {!!} }  ; commute = {!!} ; sym-commute = {!!} } ] 
         ; commute = {!!} ; sym-commute = {!!} }
TermSetSem (fold-I {φ = φ} {α ∷ αs} {β ∷ βs} ⊢H ⊢F) = {!!}



open import Utils 
open import SetEnvironments.EnvironmentExtension
extendEnvVec : ∀ {k} {Ks : Vec TypeExpr k} {Γ} {Φ} (αs : Vec (FVar 0) k) 
               → (⊢Ks : foreach (Γ ≀ Φ ⊢_) Ks)
               → Functor SetEnvCat SetEnvCat 
extendEnvVec αs ⊢Ks = record
                        { F₀ = λ ρ → Functor.F₀ (extendSetEnv-αs αs ρ) (Functor.F₀ (SetSemVec ⊢Ks) ρ)  
                        ; F₁ = λ {ρ} {ρ'} f → extendfv-morph-vec αs (to0Functors (Functor.F₀ (SetSemVec ⊢Ks) ρ)) ( (to0Functors (Functor.F₀ (SetSemVec ⊢Ks) ρ'))) ρ ρ' f (toConstNats (Functor.F₁ (SetSemVec ⊢Ks) f)) 
                        ; identity = {! !}
                        ; homomorphism = {!!}
                        ; F-resp-≈ = {!!}
                        } 


-- Have semt : NaturalTransformation (ContextInterp Δ) (NatTypeFunctor αs ⊢F ⊢G)
-- Goal: NaturalTransformation (ContextInterp Δ)
--       (SetSem ⊢G ∘F extendSetEnv-SetSemVec αs ⊢Ks)

testapp : ∀ {k} {Ks : Vec TypeExpr k} {Γ} {Φ} (αs : Vec (FVar 0) k) 
               → (⊢Ks : foreach (Γ ≀ Φ ⊢_) Ks)
               → (Δ : TermCtx Γ ∅) 
               → {F G : TypeExpr} 
               → (⊢F : Γ ≀ ( ∅ ,++ αs ) ⊢ F) (⊢G : Γ ≀ ( ∅ ,++ αs ) ⊢ G)
               → NaturalTransformation (ContextInterp Δ) 
                        (SetSem ⊢F ∘F extendEnvVec αs ⊢Ks)
               → NaturalTransformation (ContextInterp Δ) (NatTypeFunctor αs ⊢F ⊢G) 
               → NaturalTransformation (ContextInterp Δ)
                        (SetSem ⊢G ∘F extendEnvVec αs ⊢Ks)
testapp αs ⊢Ks Δ ⊢F ⊢G sems semt =
  let t : (ρ : SetEnv) → (Functor.F₀ (ContextInterp Δ) ρ) → NaturalTransformation (SetSem ⊢F ∘F extendSetEnv-αs αs (NatEnv ρ)) (SetSem ⊢G ∘F extendSetEnv-αs αs (NatEnv ρ))
      t ρ d = NatTypeSem.nat (NaturalTransformation.η semt ρ d)
  in 
  record { η = λ ρ Dρ → {!NaturalTransformation.η (t ρ Dρ) (Functor.F₀ (SetSemVec ⊢Ks) ρ) ?   !}
         ; commute = {!!} ; sym-commute = {!!} } 





open import NestedTypeSyntax 
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open FVar
open _∋_ 

open import Categories.Category using (Category)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import NestedSetSemantics 
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import HFixFunctorLib using (fixH)

open import Agda.Builtin.Unit

open ≡.≡-Reasoning

open import Data.Vec using (Vec ; _∷_ ;  []) 
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Data.Product hiding (curry) renaming (_×_ to _×'_)
open import Utils
open ≃-Reasoning 

open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)

open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)

open import SetEnvironments
open import SetCats 
open import Categories.Category.Product using (Product ; _※_  ; πˡ ; πʳ ; _⁂_ ; _※ⁿⁱ_)
open import Categories.Category.Product.Properties using (※-distrib)

open import Level renaming (zero to lzero ; suc to lsuc)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)

import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation.NaturalIsomorphism as NI 
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) renaming (_ⓘˡ_ to _≃ˡ_)


module SetSemExtendEnv where 


private 
  variable 
    k : ℕ
    Γ : TCCtx
    Φ : FunCtx 
    F H : TypeExpr
    α : FVar 0

mutual 
  -- -- don't really need this 
  -- TEnv∘FEnv-extendFunCtx-≃ : ∀ {φ : FVar k} {αs : Vec (FVar 0) k}
  --         → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ F)
  --         → (⊢H : Γ ≀ Φ ⊢ H)
  --         → (TEnv ⊢F ∘F ForgetFVEnv)
  --         ≃ (TEnv ⊢F ∘F ForgetFVEnv) ∘F extendEnvFVar α ⊢H 
  -- TEnv∘FEnv-extendFunCtx-≃ {α = α} ⊢F ⊢H = begin≃
  --     TEnv ⊢F ∘F ForgetFVEnv
  --   ≃⟨ (TEnv ⊢F) ≃ˡ (NI.sym (ForgetFVEnv∘extendEnvFVar≃ForgetFVEnv α ⊢H)) ⟩
  --     TEnv ⊢F ∘F (ForgetFVEnv ∘F extendEnvFVar α ⊢H) 
  --   ≃˘⟨ NI.associator (extendEnvFVar α ⊢H) ForgetFVEnv (TEnv ⊢F) ⟩
  --     (TEnv ⊢F ∘F ForgetFVEnv) ∘F extendEnvFVar α ⊢H
  --   ≃∎


  -- [[F [ α := H ] ]] ρ  ≡   [[F]] ρ [ α := [[H]] ]
  -- but for vectors of F 
  SetSemVec-extendFunCtx-≃ : ∀ {H : TypeExpr} {Fs : Vec TypeExpr k} (⊢Fs : foreach (λ F → Γ ≀ (Φ ,, α) ⊢ F) Fs)
                          → (⊢H : Γ ≀ Φ ⊢ H)
                          → SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs))
                          ≃ SetSemVec ⊢Fs ∘F extendEnvFVar α ⊢H
  SetSemVec-extendFunCtx-≃ {α = α} {Fs = []} ⊢Fs ⊢H = ConstF-∘-≃  (Sets^ 0) (extendEnvFVar α ⊢H) -- need proof that ConstF G ≃ ConstF G ∘F .... 
  SetSemVec-extendFunCtx-≃ {k = suc n} {α = α} {H} {Fs = F ∷ Fs} (⊢F , ⊢Fs) ⊢H = 
    let ⟦F[H]⟧ = SetSem (fo-subst-preserves-typing F H ⊢F ⊢H) 
        ⟦Fs[H]⟧ = SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs))
        ⟦F⟧ = SetSem ⊢F
        ⟦Fs⟧ = SetSemVec ⊢Fs

        Cons = Sets^cons n 
        extendH = extendEnvFVar α ⊢H

        ⟦F[H]⟧≃⟦F⟧∘extend = SetSem-extendFunCtx-≃ ⊢F ⊢H 
        ⟦Fs[H]⟧≃⟦Fs⟧∘extend = SetSemVec-extendFunCtx-≃ ⊢Fs ⊢H 

        ※-≃ : (⟦F[H]⟧ ※ ⟦Fs[H]⟧) ≃ ((⟦F⟧ ∘F extendH) ※ (⟦Fs⟧ ∘F extendH))
        ※-≃ = ⟦F[H]⟧≃⟦F⟧∘extend  ※ⁿⁱ ⟦Fs[H]⟧≃⟦Fs⟧∘extend

        -- ※-distrib : {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂}
        --   → (F : Functor B C) → (G : Functor B D) → (H : Functor A B)
        --   → ((F ∘F H) ※ (G ∘F H)) ≃ ((F ※ G) ∘F H)
        distrib-≃ : ((⟦F⟧ ∘F extendH) ※ (⟦Fs⟧ ∘F extendH)) ≃ ((⟦F⟧ ※ ⟦Fs⟧) ∘F extendH)
        distrib-≃ = ※-distrib Sets (Sets^ n) ⟦F⟧ ⟦Fs⟧ extendH 

        in 
        begin≃
          Cons ∘F (⟦F[H]⟧ ※ ⟦Fs[H]⟧)
        ≃⟨ Cons ≃ˡ ※-≃ ⟩
          Cons ∘F ((⟦F⟧ ∘F extendH) ※ (⟦Fs⟧ ∘F extendH))
        ≃⟨ Cons ≃ˡ distrib-≃ ⟩
          Cons ∘F ((⟦F⟧ ※ ⟦Fs⟧) ∘F extendH)
       ≃˘⟨ NI.associator extendH (⟦F⟧ ※ ⟦Fs⟧) Cons ⟩
          (Cons ∘F (⟦F⟧ ※ ⟦Fs⟧)) ∘F extendH
        ≃∎ 

  -- if we explicitly forget about functorial part of environment, 
  -- any extensions of the functorial part of the environment have no effect 
  ForgetFVEnv∘extendEnvFVar≃ForgetFVEnv : ∀ (α : FVar 0) → (⊢H : Γ ≀ Φ ⊢ H)
                                 → ForgetFVEnv ∘F extendEnvFVar α ⊢H 
                                 ≃ ForgetFVEnv 
  ForgetFVEnv∘extendEnvFVar≃ForgetFVEnv α ⊢H = 
               record { F⇒G = record { η = λ _ → Category.id SetEnvCat ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl } 
                      ; F⇐G = record { η = λ _ → Category.id SetEnvCat ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl } 
                      ; iso = λ _ → record { isoˡ = ≡.refl ; isoʳ = ≡.refl } } 


  μ-SetSem-extend-≡ : ∀ {φ : FVar k}
                              {αs : Vec (FVar 0) k} {F : TypeExpr} 
                              → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ ⊢ F)
                              {Gs : Vec TypeExpr k} 
                              → (⊢Gs : foreach (_≀_⊢_ Γ (Φ ,, α)) Gs)
                              → (⊢H : Γ ≀ Φ ⊢ H) 
                              → SetSem (fo-subst-preserves-typing (μ φ [λ αs , F ] Gs) H (μ-I F ⊢F Gs ⊢Gs) ⊢H)
                              ≡ (eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec (replaceVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs))))
  μ-SetSem-extend-≡ ⊢F ⊢Gs ⊢H = ≡.refl 


-- SetSemVec : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx}
--               → {Fs : Vec TypeExpr k}
--               → foreach (λ F → Γ ≀ Φ ⊢ F) Fs
--               → Functor SetEnvCat (Sets^ k)



  -- fixT-extend-≃ : fixT∘FEnv
  --             ≃ fixT∘FEnv ∘F extendH
  -- fixT-extend-≃ = 
  --   begin≃
  --     (fixH  ∘F TF) ∘F ForgetFVEnv
  --     ≃˘⟨ (fixH  ∘F TF) ≃ˡ (ForgetFVEnv∘extendEnvFVar≃ForgetFVEnv α ⊢H) ⟩ --  (fixH  ∘F (TEnv ⊢F)) ≃ˡ (NI.sym ...Forget...)
  --     (fixH  ∘F TF) ∘F (ForgetFVEnv ∘F extendH)
  --     ≃˘⟨ NI.associator extendH ForgetFVEnv (fixH  ∘F TF) ⟩
  --     ((fixH  ∘F TF) ∘F ForgetFVEnv) ∘F extendH
  --     ≃∎


  -- μ-SetSem-extendFunCtx-≃3 : ∀ {φ : FVar k}
  --                             {αs : Vec (FVar 0) k} 
  --                             → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ ⊢ F)
  --                             {Gs : Vec TypeExpr k} 
  --                             → (⊢Gs : foreach (_≀_⊢_ Γ (Φ ,, α)) Gs)
  --                             → (⊢H : Γ ≀ Φ ⊢ H) 


  μ-SetSem-extendFunCtx-≃2 : ∀ {φ : FVar k}
                              {αs : Vec (FVar 0) k} 
                              → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ ⊢ F)
                              {Gs : Vec TypeExpr k} 
                              → (⊢Gs : foreach (_≀_⊢_ Γ (Φ ,, α)) Gs)
                              → (⊢H : Γ ≀ Φ ⊢ H) 
                              → ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs)))
                              ≃ ((((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs)) ∘F extendEnvFVar α ⊢H)
  μ-SetSem-extendFunCtx-≃2 {k} {Γ = Γ} {F} {Φ = Φ} {α} {H = H} {φ} {αs} ⊢F {Gs} ⊢Gs ⊢H = 
    let 
        ⟦Gs⟧ = SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs
        ⟦Gs[H]⟧ = SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs))
        extendH = extendEnvFVar α ⊢H

        ⟦Gs[H]⟧≃⟦Gs⟧∘extend : ⟦Gs[H]⟧ ≃ (⟦Gs⟧ ∘F extendH)
        ⟦Gs[H]⟧≃⟦Gs⟧∘extend = SetSemVec-extendFunCtx-≃ ⊢Gs ⊢H 
        --
        TF : Functor SetEnvCat ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
        TF = TEnv {k} {Γ} {F} {φ} {αs} ⊢F
        --
        fixT∘FEnv : Functor SetEnvCat [Sets^ k ,Sets]
        fixT∘FEnv = (fixH ∘F TF) ∘F ForgetFVEnv 
        -- 
        fixT-distrib-※ : ((fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
                      ≃ ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
        fixT-distrib-※ = ※-distrib [Sets^ k ,Sets] (Sets^ k) fixT∘FEnv ⟦Gs⟧ extendH

        fixT-extend-≃ :  fixT∘FEnv
                    ≃ fixT∘FEnv ∘F extendH
        fixT-extend-≃ = 
          begin≃
            (fixH  ∘F TF) ∘F ForgetFVEnv
            ≃˘⟨ (fixH  ∘F TF) ≃ˡ (ForgetFVEnv∘extendEnvFVar≃ForgetFVEnv {Γ} {Φ} {H} α ⊢H) ⟩ --  (fixH  ∘F (TEnv ⊢F)) ≃ˡ (NI.sym ...Forget...)
            (fixH  ∘F TF) ∘F (ForgetFVEnv ∘F extendH)
            ≃˘⟨ NI.associator extendH ForgetFVEnv (fixH  ∘F TF) ⟩
            ((fixH  ∘F TF) ∘F ForgetFVEnv) ∘F extendH
            ≃∎

    in 
      -- takes 2-3 seconds to type-check 
       begin≃ 
             -- ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs)))
                (fixT∘FEnv ※ ⟦Gs[H]⟧)
            ≃⟨  (NI.refl {C = SetEnvCat} {D = [Sets^ k ,Sets]} {x = fixT∘FEnv}) ※ⁿⁱ   ⟦Gs[H]⟧≃⟦Gs⟧∘extend   ⟩ 
             -- (fixT∘FEnv ※ (⟦Gs⟧ ∘F extendH))
                (fixT∘FEnv ※ (⟦Gs⟧ ∘F extendH))
            ≃⟨  fixT-extend-≃  ※ⁿⁱ (NI.refl {C = SetEnvCat} {D = Sets^ k} {x = ⟦Gs⟧ ∘F extendH})   ⟩ 
              -- (((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv) ∘F extendH ※ SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs ∘F extendEnvFVar α ⊢H)
                ((fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
            ≃⟨  fixT-distrib-※  ⟩ 
             -- ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs) ∘F extendEnvFVar α ⊢H
                ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
            ≃∎



  -- eval : Bifunctor (Functors C D) C D 
  -- eval : Functor (Product (Functors C D) C) D 

  eval-≃ : ∀ {ao al ae bo bl be co cl ce ddo dl de : Level} {A : Category ao al ae} {B : Category bo bl be} {C : Category co cl ce} {D : Category ddo dl de}
           → (F : Functor A (Product (Functors C D) C)) 
           → (G : Functor B (Product (Functors C D) C))
           → (H : Functor A B) 
           → F ≃ (G ∘F H) → eval ∘F F ≃ (eval ∘F G) ∘F H 
  eval-≃ F G H η = 
      begin≃ 
            eval ∘F F
            ≃⟨ eval ≃ˡ η ⟩ 
            eval ∘F (G ∘F H)
            ≃˘⟨ NI.associator H G eval ⟩ 
            (eval ∘F G) ∘F H
           ≃∎ 


  μ-SetSem-extendFunCtx-≃ : ∀ {φ : FVar k}
                              {αs : Vec (FVar 0) k} 
                              → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ ⊢ F)
                              {Gs : Vec TypeExpr k} 
                              → (⊢Gs : foreach (_≀_⊢_ Γ (Φ ,, α)) Gs)
                              → (⊢H : Γ ≀ Φ ⊢ H) 
                              → -- SetSem (fo-subst-preserves-typing (μ φ [λ αs , F ] Gs) H (μ-I F ⊢F Gs ⊢Gs) ⊢H)
                              (eval {C = Sets^ k} {D = Sets} ∘F ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs))))
                              ≃ ((eval {C = Sets^ k} {D = Sets} ∘F ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs)) ∘F extendEnvFVar α ⊢H)
                              -- SetSem (μ-I F ⊢F Gs ⊢Gs) ∘F extendEnvFVar α ⊢H
  μ-SetSem-extendFunCtx-≃ {k} {Γ = Γ} {F} {Φ = Φ} {α} {H = H} {φ} {αs} ⊢F {Gs} ⊢Gs ⊢H = 
    -- STOPPED HERE... this is still type-checking slowly. Everything else is fine, so this is the bottle-neck. maybe eval needs implicit args? 
    -- 
    -- adding implicit arguments to eval worked.. takes about 3-5 seconds now 
    let 
        ⟦Gs⟧ = SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs
        ⟦Gs[H]⟧ = SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs))
        extendH = extendEnvFVar α ⊢H

        --
        TF : Functor SetEnvCat ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
        TF = TEnv {k} {Γ} {F} {φ} {αs} ⊢F
        --
        fixT∘FEnv : Functor SetEnvCat [Sets^ k ,Sets]
        fixT∘FEnv = (fixH ∘F TF) ∘F ForgetFVEnv 
     in 
                -- F = (fixT∘FEnv ※ ⟦Gs[H]⟧) : Functor SetEnvCat (Product ([Sets^ k ,Sets]) (Sets^ k))
                -- G = (fixT∘FEnv ※ ⟦Gs⟧)    : Functor SetEnvCat (Product ([Sets^ k ,Sets]) (Sets^ k))
                -- H = extendH               : Functor SetEnvCat SetEnvCat
      eval-≃ {A = SetEnvCat} {B = SetEnvCat} {C = Sets^ k} {D = Sets}  (fixT∘FEnv ※ ⟦Gs[H]⟧)  (fixT∘FEnv ※ ⟦Gs⟧) extendH  (μ-SetSem-extendFunCtx-≃2 {k} {Γ = Γ} {F} {Φ = Φ} {α} {H = H} {φ} {αs} ⊢F {Gs} ⊢Gs ⊢H)


  {-
    eval-≃ {A = SetEnvCat} {B = SetEnvCat} {C = Sets^ k} {D = Sets}  (fixT∘FEnv ※ ⟦Gs[H]⟧)  (fixT∘FEnv ※ ⟦Gs⟧) extendH  
           (μ-SetSem-extendFunCtx-≃2 {k} {Γ = Γ} {F} {Φ = Φ} {α} {H = H} {φ} {αs} ⊢F {Gs} ⊢Gs ⊢H)
           -}



{-
    let 
        ⟦Gs⟧ = SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs
        ⟦Gs[H]⟧ = SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs))
        extendH = extendEnvFVar α ⊢H

        ⟦Gs[H]⟧≃⟦Gs⟧∘extend : ⟦Gs[H]⟧ ≃ (⟦Gs⟧ ∘F extendH)
        ⟦Gs[H]⟧≃⟦Gs⟧∘extend = SetSemVec-extendFunCtx-≃ ⊢Gs ⊢H 
        --
        TF : Functor SetEnvCat ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
        TF = TEnv {k} {Γ} {F} {φ} {αs} ⊢F
        --
        fixT∘FEnv : Functor SetEnvCat [Sets^ k ,Sets]
        fixT∘FEnv = (fixH ∘F TF) ∘F ForgetFVEnv 
       in begin≃ 
              -- (eval ∘F ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs)))) 

            eval ∘F (fixT∘FEnv ※ ⟦Gs[H]⟧)
            ≃⟨ {!   !} ⟩ 
            eval ∘F ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
            ≃⟨ {!   !} ⟩ 
            -- (eval ∘F (fixT∘FEnv ※ ⟦Gs⟧)) ∘F extendH
            {!((eval ∘F ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs)) ∘F extendEnvFVar α ⊢H)!} -- ((eval ∘F ((fixH ∘F (TEnv {k} {Γ} {F} {φ} {αs} ⊢F)) ∘F ForgetFVEnv ※ SetSemVec {k} {Γ} {Φ ,, α} {Gs} ⊢Gs)) ∘F extendEnvFVar α ⊢H)           
            ≃∎

      --  begin≃ 
      --           (eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs))))
      --       ≃⟨ {!   !} ⟩ 
      --           ((eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec ⊢Gs)) ∘F extendEnvFVar α ⊢H)
      --       ≃∎



  -- foreach-preserves-subst : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {α : FVar 0}
  {-
    let 
        ⟦Gs⟧ = SetSemVec ⊢Gs
        ⟦Gs[H]⟧ = SetSemVec (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs))
        ⟦Gs[H]⟧≃⟦Gs⟧∘extend = SetSemVec-extendFunCtx-≃ ⊢Gs ⊢H 
        extendH = extendEnvFVar α ⊢H
        --
        TF : Functor SetEnvCat ([[ [Sets^ n ,Sets] , [Sets^ n ,Sets] ]])
        TF = TEnv ⊢F 
        --
        fixT∘FEnv : Functor SetEnvCat [Sets^ n ,Sets]
        fixT∘FEnv = (fixH ∘F TF) ∘F ForgetFVEnv 
        -- 
        fixT-extend-※ : ((fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
                      ≃ ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
        fixT-extend-※ = ※-distrib [Sets^ n ,Sets] (Sets^ n) fixT∘FEnv ⟦Gs⟧ extendH

        fixT-extend-≃ :  fixT∘FEnv
                    ≃ fixT∘FEnv ∘F extendH
        fixT-extend-≃ = 
          begin≃
            (fixH  ∘F TF) ∘F ForgetFVEnv
            ≃˘⟨ (fixH  ∘F TF) ≃ˡ (ForgetFVEnv∘extendEnvFVar≃ForgetFVEnv α ⊢H) ⟩ --  (fixH  ∘F (TEnv ⊢F)) ≃ˡ (NI.sym ...Forget...)
            (fixH  ∘F TF) ∘F (ForgetFVEnv ∘F extendH)
            ≃˘⟨ NI.associator extendH ForgetFVEnv (fixH  ∘F TF) ⟩
            ((fixH  ∘F TF) ∘F ForgetFVEnv) ∘F extendH
            ≃∎

        ※-extend-≃ : (fixT∘FEnv ※ ⟦Gs[H]⟧)
                -- ≃ (fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH)
                ≃ ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
        ※-extend-≃ =  
          begin≃
            (fixT∘FEnv ※ ⟦Gs[H]⟧)
            ≃⟨ NI.refl ※ⁿⁱ ⟦Gs[H]⟧≃⟦Gs⟧∘extend ⟩ -- NI.refl ※ⁿⁱ ..Gs..
            (fixT∘FEnv ※ (⟦Gs⟧ ∘F extendH))
            ≃⟨ fixT-extend-≃ ※ⁿⁱ NI.refl ⟩ -- .. ※ⁿⁱ  NI.refl
            ((fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
            ≃⟨ fixT-extend-※ ⟩ -- distrib 
            ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
            ≃∎

        -- 
        -- still very slow... maybe need implicit args 
        in 
        -}


-- begin≃
-- (eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec (replaceVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs))))
        -- ≃⟨ ? ⟩ 
        -- ((eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec ⊢Gs)) ∘F extendEnvFVar α ⊢H)
        -- ≃∎

          -- --   SetSem (fo-subst-preserves-typing (μ φ [λ αs , F ] Gs) H (μ-I F ⊢F Gs ⊢Gs) ⊢H)
          -- -- ≃⟨ NI-≡ {! μ-SetSem-extend-≡ ⊢F ⊢Gs ⊢H  !} ⟩ 
          --   eval ∘F (fixT∘FEnv ※ ⟦Gs[H]⟧)
          -- ≃⟨ {!   !} ⟩ 
          -- -- ≃⟨ eval ≃ˡ ※-extend-≃ ⟩ 
          --   eval ∘F ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
          -- -- ≃˘⟨ NI.associator extendH  (fixT∘FEnv ※ ⟦Gs⟧) eval ⟩ 
          -- ≃˘⟨ {!!} ⟩ 
          --   (eval ∘F (fixT∘FEnv ※ ⟦Gs⟧)) ∘F extendH
          -- -- ≃⟨ {! NI.refl    !} ⟩ 
          -- --   SetSem (μ-I F ⊢F Gs ⊢Gs) ∘F extendEnvFVar α ⊢H
          -- ≃∎



-}

  SetSem-extendFunCtx-≃ : ∀ (⊢F : Γ ≀ (Φ ,, α) ⊢ F)
                        → (⊢H : Γ ≀ Φ ⊢ H)
                        → SetSem {Γ} {Φ} {F [ α := H ] } (fo-subst-preserves-typing {Γ} {Φ} {α} F H ⊢F ⊢H) 
                        ≃ (SetSem {Γ} {Φ ,, α} {F} ⊢F) ∘F extendEnvFVar {Γ} {Φ} {H} α ⊢H
  SetSem-extendFunCtx-≃ {α = α} 𝟘-I ⊢H = ConstF-∘-≃ Sets (extendEnvFVar α ⊢H)
  SetSem-extendFunCtx-≃ {α = α} 𝟙-I ⊢H = ConstF-∘-≃ Sets (extendEnvFVar α ⊢H)
  SetSem-extendFunCtx-≃ {α = α} (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) ⊢H = {!  
        begin≃
          eval ∘F (VarSem-TC φ ※ SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs)))
        ≃⟨ ? ⟩
          (eval ∘F (VarSem-TC φ ※ SetSemVec ⊢Fs)) ∘F extendEnvFVar α ⊢H
        ≃∎     !}

  SetSem-extendFunCtx-≃ {α = α} (AppF-I Φ∋φ Fs ⊢Fs) ⊢H = {!   !}

  -- SetSum ∘F
  --     (SetSem (fo-subst-preserves-typing F H ⊢F ⊢H) ※
  --      SetSem (fo-subst-preserves-typing G H ⊢G ⊢H))
  --     ≃ (SetSum ∘F (SetSem ⊢F ※ SetSem ⊢G)) ∘F extendEnvFVar α ⊢H


  -- TODO combine sum, product cases 
  SetSem-extendFunCtx-≃ {α = α} {H = H} (+-I {F = F} {G = G} ⊢F ⊢G) ⊢H = 
    let ⟦F⟧ = SetSem ⊢F
        ⟦F[H]⟧ = SetSem (fo-subst-preserves-typing F H ⊢F ⊢H)
        ⟦G⟧ = SetSem ⊢G
        ⟦G[H]⟧ = SetSem (fo-subst-preserves-typing G H ⊢G ⊢H)
        extendH = extendEnvFVar α ⊢H

        ⟦F[H]⟧≃⟦F⟧∘extend = SetSem-extendFunCtx-≃ ⊢F ⊢H
        ⟦G[H]⟧≃⟦G⟧∘extend = SetSem-extendFunCtx-≃ ⊢G ⊢H
      in 
        begin≃ 
          SetSum ∘F (⟦F[H]⟧ ※ ⟦G[H]⟧)
        ≃⟨ SetSum ≃ˡ (⟦F[H]⟧≃⟦F⟧∘extend ※ⁿⁱ ⟦G[H]⟧≃⟦G⟧∘extend) ⟩
          SetSum ∘F ((⟦F⟧ ∘F extendH) ※ (⟦G⟧ ∘F extendH))
        ≃⟨ SetSum ≃ˡ (※-distrib Sets Sets ⟦F⟧ ⟦G⟧ extendH) ⟩
          SetSum ∘F ((⟦F⟧ ※ ⟦G⟧) ∘F extendH)
       ≃˘⟨ NI.associator extendH (⟦F⟧ ※ ⟦G⟧) SetSum ⟩
          (SetSum ∘F (⟦F⟧ ※ ⟦G⟧)) ∘F extendH
        ≃∎

  SetSem-extendFunCtx-≃ {α = α} {H = H} (×-I {F = F} {G = G} ⊢F ⊢G) ⊢H = 
    let ⟦F⟧ = SetSem ⊢F
        ⟦F[H]⟧ = SetSem (fo-subst-preserves-typing F H ⊢F ⊢H)
        ⟦G⟧ = SetSem ⊢G
        ⟦G[H]⟧ = SetSem (fo-subst-preserves-typing G H ⊢G ⊢H)
        extendH = extendEnvFVar α ⊢H

        ⟦F[H]⟧≃⟦F⟧∘extend = SetSem-extendFunCtx-≃ ⊢F ⊢H
        ⟦G[H]⟧≃⟦G⟧∘extend = SetSem-extendFunCtx-≃ ⊢G ⊢H
      in 
        begin≃ 
          SetProd ∘F (⟦F[H]⟧ ※ ⟦G[H]⟧)
        ≃⟨ SetProd ≃ˡ (⟦F[H]⟧≃⟦F⟧∘extend ※ⁿⁱ ⟦G[H]⟧≃⟦G⟧∘extend) ⟩
          SetProd ∘F ((⟦F⟧ ∘F extendH) ※ (⟦G⟧ ∘F extendH))
        ≃⟨ SetProd ≃ˡ (※-distrib Sets Sets ⟦F⟧ ⟦G⟧ extendH) ⟩
          SetProd ∘F ((⟦F⟧ ※ ⟦G⟧) ∘F extendH)
        ≃˘⟨ NI.associator extendH (⟦F⟧ ※ ⟦G⟧) SetProd ⟩
          (SetProd ∘F (⟦F⟧ ※ ⟦G⟧)) ∘F extendH
        ≃∎

  -- could use more general lemma that says precomposing NatSem with any functor of environments doesn't change 
  SetSem-extendFunCtx-≃ {α = α} (Nat-I ⊢F ⊢G) ⊢H = {!   !}

  -- STOPPED HERE 
  -- helper function μ-SetSem-extend... type checks in a reasonable amount of time, but this does not..
  -- -- still slow after giving all implicit arguments in the type of this function 
  SetSem-extendFunCtx-≃ {Γ} {Φ} {α} {H = H} (μ-I {k = k} {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) ⊢H = {!!}
  -- μ-SetSem-extendFunCtx-≃ {k} {Γ = Γ} {F} {Φ = Φ} {α} {H = H} {φ} {αs} ⊢F {Gs} ⊢Gs ⊢H 
  -- μ-SetSem-extendFunCtx-≃ {k} {Γ = Γ} {F} {Φ = Φ} {α} {H = ?} {φ} {αs} ⊢F {Gs} ⊢Gs ⊢H 




        {-
    let 
        ⟦Gs⟧ = SetSemVec ⊢Gs
        ⟦Gs[H]⟧ = SetSemVec (replaceVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs))
        ⟦Gs[H]⟧≃⟦Gs⟧∘extend = SetSemVec-extendFunCtx-≃ ⊢Gs ⊢H 
        extendH = extendEnvFVar α ⊢H
        --
        TF : Functor SetEnvCat ([[ [Sets^ n ,Sets] , [Sets^ n ,Sets] ]])
        TF = TEnv ⊢F 
        --
        fixT∘FEnv : Functor SetEnvCat [Sets^ n ,Sets]
        fixT∘FEnv = (fixH ∘F TF) ∘F ForgetFVEnv 
        -- 
        fixT-extend-※ : ((fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
                      ≃ ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
        fixT-extend-※ = ※-distrib [Sets^ n ,Sets] (Sets^ n) fixT∘FEnv ⟦Gs⟧ extendH

        fixT-extend-≃ :  fixT∘FEnv
                    ≃ fixT∘FEnv ∘F extendH
        fixT-extend-≃ = 
          begin≃
            (fixH  ∘F TF) ∘F ForgetFVEnv
            ≃⟨ (fixH  ∘F TF) ≃ˡ (NI.sym (ForgetFVEnv∘extendEnvFVar≃ForgetFVEnv α ⊢H)) ⟩ --  (fixH  ∘F (TEnv ⊢F)) ≃ˡ (NI.sym ...Forget...)
            (fixH  ∘F TF) ∘F (ForgetFVEnv ∘F extendH)
            ≃˘⟨ NI.associator extendH ForgetFVEnv (fixH  ∘F TF) ⟩
            ((fixH  ∘F TF) ∘F ForgetFVEnv) ∘F extendH
            ≃∎

        ※-extend-≃ : (fixT∘FEnv ※ ⟦Gs[H]⟧)
                -- ≃ (fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH)
                ≃ ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
        ※-extend-≃ = 
          begin≃
            (fixT∘FEnv ※ ⟦Gs[H]⟧)
            ≃⟨ NI.refl ※ⁿⁱ ⟦Gs[H]⟧≃⟦Gs⟧∘extend ⟩ -- NI.refl ※ⁿⁱ ..Gs..
            (fixT∘FEnv ※ (⟦Gs⟧ ∘F extendH))
            ≃⟨ fixT-extend-≃ ※ⁿⁱ NI.refl ⟩ -- .. ※ⁿⁱ  NI.refl
            ((fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
            ≃⟨ fixT-extend-※ ⟩ -- distrib 
            ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
            ≃∎

      in -- {!   !}
        begin≃
        (eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec (replaceVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs))))
        ≃⟨ ? ⟩ 
        ((eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec ⊢Gs)) ∘F extendEnvFVar α ⊢H)
        ≃∎
         -}

        -- begin≃
        --   eval ∘F (fixT∘FEnv ※ ⟦Gs[H]⟧)
        -- ≃⟨ ? ⟩ 
        -- (eval ∘F (fixT∘FEnv ※ ⟦Gs⟧)) ∘F extendH
        -- ≃∎

        -- begin≃
        --   eval ∘F (fixT∘FEnv ※ ⟦Gs[H]⟧)
        -- ≃⟨ eval ≃ˡ ※-extend-≃ ⟩ 
        --   eval ∘F ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
        -- ≃⟨ NI.sym-associator extendH  (fixT∘FEnv ※ ⟦Gs⟧) eval ⟩ 
        -- (eval ∘F (fixT∘FEnv ※ ⟦Gs⟧)) ∘F extendH
        -- ≃∎


    --   begin≃
    --     eval ∘F (fixT∘FEnv ※ ⟦Gs[H]⟧)
    --   ≃⟨ ? ⟩ -- recursive proof for Gs 
    --     eval ∘F (fixT∘FEnv ※ (⟦Gs⟧ ∘F extendH))
    --   ≃⟨ ? ⟩ -- associate (fixH  ∘F (TEnv ⊢F)) ∘F ForgetFVEnv
    --          -- to        fixH ∘F ((TEnv ⊢F) ∘F ForgetFVEnv)
    --  -- below is just a synonym for 
    --  -- fixH  ∘F ((TEnv ⊢F) ∘F ForgetFVEnv)
    --     -- eval ∘F (fix∘TFEnv ※ (⟦Gs⟧ ∘F extendH))
    --     eval ∘F (fixH  ∘F ((TEnv ⊢F) ∘F ForgetFVEnv)            ※ (⟦Gs⟧ ∘F extendH))
    --   ≃⟨ ? ⟩ -- then we precompose ((TEnv ⊢F) ∘F ForgetFVEnv) with extendH 
    --     eval ∘F (fixH  ∘F ((TEnv ⊢F ∘F ForgetFVEnv) ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
    --   ≃⟨ ? ⟩ -- then associate 
    --          -- fixH ∘ (G ∘ extendH) ≃ (fixH ∘ G) ∘ extendH
    --     eval ∘F ((fixH ∘F ((TEnv ⊢F ∘F ForgetFVEnv)) ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
    --     -- eval ∘F ((fix∘TFEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
    --   ≃⟨ ? ⟩ 
    --  -- eval ∘F ((fixH ∘F (TEnv ⊢F ∘F ForgetFVEnv)) ∘F extendH  ※ (⟦Gs⟧ ∘F extendH))
    --     eval ∘F ((fixT∘FEnv ∘F extendH) ※ (⟦Gs⟧ ∘F extendH))
    --   ≃⟨ ? ⟩ -- F ∘ H ※ G ∘ H  ≃ (F ※ G) ∘F H
    --     eval ∘F ((fixT∘FEnv ※ ⟦Gs⟧) ∘F extendH)
    --   ≃⟨ ? ⟩ -- F ∘ H ※ G ∘ H  ≃ (F ※ G) ∘F H
    --    (eval ∘F (fixT∘FEnv ※ ⟦Gs⟧)) ∘F extendH
    --   ≃∎




-- what is 

-- (fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ∘F extendEnvFVar α ⊢H

-- eval ∘F
--       ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※
--        SetSemVec
--        (replaceVec-preserves H Gs ⊢H
--         (foreach-preserves-subst H Gs ⊢H ⊢Gs)))
--       ≃
--       (eval ∘F ((fixH ∘F TEnv ⊢F) ∘F ForgetFVEnv ※ SetSemVec ⊢Gs)) ∘F
--       extendEnvFVar α ⊢H






          -- → TEnv ⊢F ∘F ForgetFVEnv
          -- ≃ (TEnv ⊢F ∘F ForgetFVEnv) ∘F extendEnvFVar α ⊢H 
--   -- TEnv∘FEnv-extendFunCtx-≃ {α = α} ⊢F ⊢H = begin≃

        -- need proof that TEnv ⊢F ∘F extendH ≃ TEnv ⊢F 

        -- eval 

      -- in {!   !}
      -- begin≃
      --   eval ∘F (fixT ※ ⟦Gs[H]⟧)
      -- ≃⟨ ? ⟩
      --   eval ∘F (fixT ※ (⟦Gs⟧ ∘F extendH))
      -- ≃⟨ ? ⟩
      --  (eval ∘F (fixT ※ ⟦Gs⟧)) ∘F extendH
      -- ≃∎

-- eval ∘F ((fixH ∘F TEnv ⊢F) ※ ⟦Gs[H]⟧)
-- -- eval ≃ˡ (NI.refl ※ⁿⁱ ....)
-- eval ∘F ((fixH ∘F TEnv ⊢F) ※ (⟦Gs[H]⟧ ∘F extendH))
-- -- .. need proof that TEnv ⊢F ∘F extendH ≃ TEnv 
-- eval ∘F ((fixH ∘F TEnv ⊢F ∘F extendH) ※ (⟦Gs[H]⟧ ∘F extendH))
-- -- eval ≃ˡ ※-distrib
-- eval ∘F ((fixH ∘F TEnv ⊢F ※ ⟦Gs[H]⟧) ∘F extendH)
-- -- assoc 
-- (eval ∘F ((fixH ∘F TEnv ⊢F ※ ⟦Gs[H]⟧)) ∘F extendH



-- goal : 
-- eval ∘F
--       (fixH ∘F TEnv ⊢F ※
--        SetSemVec
--        (replaceVec-preserves H Gs ⊢H
--         (foreach-preserves-subst H Gs ⊢H ⊢Gs)))
--       ≃ (eval ∘F (fixH ∘F TEnv ⊢F ※ SetSemVec ⊢Gs)) ∘F extendEnvFVar α ⊢H






{-

  -- [[F [ α := H ] ]] ρ  ≡   [[F]] ρ [ α := [[H]] ]
  -- but for vectors of F 
  SetSemVec-extendFunCtx : ∀ {Fs : Vec TypeExpr k} (⊢Fs : foreach (λ F → Γ ≀ (Φ ,, α) ⊢ F) Fs)
                          → (⊢H : Γ ≀ Φ ⊢ H)
                          → SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs))
                          ≡ SetSemVec ⊢Fs ∘F extendEnvFVar α ⊢H
  SetSemVec-extendFunCtx {Fs = []} ⊢Fs ⊢H = ≡.refl
  SetSemVec-extendFunCtx {k = suc n} {α = α} {Fs = F ∷ Fs} (⊢F , ⊢Fs) ⊢H 
      rewrite SetSem-extendFunCtx ⊢F ⊢H | (SetSemVec-extendFunCtx ⊢Fs ⊢H) = {!     !}

-- Cons ∘F ((F ∘F extendH) ※ (Fs ∘F extendH))
-- ≡  (by ※-distr )
-- Cons ∘F ((F ※ Fs) ∘F extendH)
-- ≡  (by assoc)
-- (Cons ∘F (F ※ Fs)) ∘F extendH


  -- rewrite (SetSemVec-extendFunCtx ⊢Fs ⊢H) = 
    -- let --
    --     C : Functor (Product Sets (Sets^ n)) (Sets^ (suc n))
    --     C = Sets^cons n
    --     --
    --     ⟦F⟧ : Functor SetEnvCat Sets
    --     ⟦F⟧ = SetSem ⊢F
    --     --
    --     ⟦Fs⟧ : Functor SetEnvCat (Sets^ n) 
    --     ⟦Fs⟧ = SetSemVec ⊢Fs
    --     --
    --     extendH : Functor SetEnvCat SetEnvCat
    --     extendH = extendSetEnv-α α ∘F (idF ※ SetSem ⊢H) 
    --   in begin
    --     {! C ∘F ((⟦F⟧ ∘F extendH) ※ (⟦Fs⟧ ∘F extendH))   !}
    --   ≡⟨ {!   !} ⟩
    --     {! C ∘F ((⟦F⟧ ※ ⟦Fs⟧) ∘F extendH)  !}
    --   ≡⟨ {!   !} ⟩
    --     {! (C ∘F (⟦F⟧ ※ ⟦Fs⟧)) ∘F extendH  !}
    --   ∎ 


-- Sets^cons n 
--     ∘F (SetSem (fo-subst-preserves-typing F H ⊢F ⊢H) 
--             ※
--        SetSemVec ⊢Fs ∘F extendEnvFVar α ⊢H)
--       ≡
--       (Sets^cons n ∘F (SetSem ⊢F ※ SetSemVec ⊢Fs)) 
--           ∘F extendSetEnv α ⊢H)

-- Cons ∘F ((F ∘F extendH) ※ (Fs ∘F extendH))
-- ≡  (by ※-distr )
-- Cons ∘F ((F ※ Fs) ∘F extendH)
-- ≡  (by assoc)
-- (Cons ∘F (F ※ Fs))
--   ∘F extendH
-- 
-- 
-- 
-- if we want to prove this without resorting to natural isos, then 
-- we need a proof that 
-- ((F ∘F extendH) ※ (Fs ∘F extendH))
-- ≡ ((F ※ Fs) ∘F extendH)
-- 
-- and also associativity ... 







  SetSem-extendFunCtx : ∀ (⊢F : Γ ≀ (Φ ,, α) ⊢ F)
                        → (⊢H : Γ ≀ Φ ⊢ H)
                        → SetSem (fo-subst-preserves-typing F H ⊢F ⊢H) 
                        ≡ SetSem ⊢F ∘F extendEnvFVar α ⊢H
  SetSem-extendFunCtx 𝟘-I ⊢H = ≡.refl
  SetSem-extendFunCtx 𝟙-I ⊢H = ≡.refl

-- Goal
-- eval ∘F (VarSem-TC φ ※ SetSemVec ⊢Fs)
--             ∘F extendSetEnv-α α ∘F (idF ※ SetSem ⊢H)
--       ≡
--  eval ∘F (VarSem-TC φ ※ SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs)))

--  wts 
--   (VarSem-TC φ ※ SetSemVec ⊢Fs) ∘F (extendSetEnv-α α ∘F (idF ※ SetSem ⊢H))
-- ≡ (VarSem-TC φ ※ SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs)))

--   (VarSem-TC φ ※ SetSemVec ⊢Fs) ∘F (extendSetEnv-α α ∘F (idF ※ SetSem ⊢H))
--   ≅
--   (VarSem-TC φ ∘F (extendSetEnv-α α ∘F (idF ※ SetSem ⊢H))) 
--       ※ (SetSemVec ⊢Fs ∘F (extendSetEnv-α α ∘F (idF ※ SetSem ⊢H))) 


  SetSem-extendFunCtx (AppT-I Γ∋φ Fs ⊢Fs) ⊢H = {!   !}


  SetSem-extendFunCtx (AppF-I Φ∋φ Fs ⊢Fs) ⊢H = {!   !}
  SetSem-extendFunCtx (+-I ⊢F ⊢G) ⊢H = {!   !}
  SetSem-extendFunCtx (×-I ⊢F ⊢G) ⊢H = {!   !}
  SetSem-extendFunCtx (Nat-I ⊢F ⊢G) ⊢H = {!   !}
  SetSem-extendFunCtx (μ-I F ⊢F Gs ⊢Gs) ⊢H = {!   !} 

  -}


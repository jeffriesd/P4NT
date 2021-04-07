

open import NestedTypeSyntax 
open _≀_⊢_ -- import names of data constructors 
open TypeExpr
open FVar
open _∋_ 

open import Categories.Category using (Category)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import NestedSetSemantics 
open AbT
open VarSem-TC-properties
open VarSem-FV-properties

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import HFixFunctorLib using (fixH)
open import NatTypeSemProperties

open import Agda.Builtin.Unit

open ≡.≡-Reasoning

open import Data.Vec using (Vec ; _∷_ ;  []) 
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Data.Product hiding (curry) renaming (_×_ to _×'_)
open import Utils
open CatUtil

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


-- TODO  3/31
-- - prove VarSemT ≃ VarSemTC ∘ extendEnvFVar 
-- - need to use the fact that φ≢α (in arity or in Id) to deduce that VarSem-FV φ ≃ VarSem-FV φ ∘F extendEnvFVar α 
-- 
-- - prove SetSem ⊢H ≃ (eval ∘F  (VarSem-FV (α ^F 0) ※ SetSemVec ⊢Fs)) ∘F extendH 




private 
  variable 
    k : ℕ
    Γ : TCCtx
    Φ : FunCtx 
    F H : TypeExpr
    α : FVar 0

mutual 

  -- [[F [ α := H ] ]] ρ  ≡   [[F]] ρ [ α := [[H]] ]
  -- but for vectors of F 
  SetSemVec-extendFunCtx-≃ : ∀ {H : TypeExpr} {Fs : Vec TypeExpr k} (⊢Fs : foreach (λ F → Γ ≀ (Φ ,, α) ⊢ F) Fs)
                          → (⊢H : Γ ≀ Φ ⊢ H)
                          → SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs))
                          ≃ SetSemVec ⊢Fs ∘F extendEnvFVar α ⊢H
  SetSemVec-extendFunCtx-≃ {α = α} {Fs = []} ⊢Fs ⊢H = ConstF-∘-≃  (Sets^ 0) (extendEnvFVar α ⊢H) 
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




-- - This works and is used, just commenting out while working on other functions 

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



  -- μ-sem-lem : ∀ {φ : FVar k} {αs : Vec (FVar 0) k} 
  --             → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ ⊢ F)
  --             {Gs : Vec TypeExpr k} 
  --             → (⊢Gs : foreach (_≀_⊢_ Γ (Φ ,, α)) Gs)
  --             → (⊢H : Γ ≀ Φ ⊢ H) 
  --             → SetSem (fo-subst-preserves-typing (μ φ [λ αs , F ] Gs) H (μ-I F ⊢F Gs ⊢Gs) ⊢H)
  --             ≡ eval {C = Sets^ k} {D = Sets} ∘F ((fixH ∘F curry.F₀ (curry.F₀ (SetSem ⊢F ∘F extendSetEnv-ρ×As-inline αs ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ)))) ∘F ForgetFVEnv ※ SetSemVec (replaceVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs)))
  -- μ-sem-lem ⊢F ⊢Gs ⊢H = {!   !} 



  SetSem-extendFunCtx-≃ : ∀ (⊢F : Γ ≀ (Φ ,, α) ⊢ F)
                        → (⊢H : Γ ≀ Φ ⊢ H)
                        → SetSem {Γ} {Φ} {F [ α := H ] } (fo-subst-preserves-typing {Γ} {Φ} {α} F H ⊢F ⊢H) 
                        ≃ (SetSem {Γ} {Φ ,, α} {F} ⊢F) ∘F extendEnvFVar {Γ} {Φ} {H} α ⊢H
  SetSem-extendFunCtx-≃ {α = α} 𝟘-I ⊢H = ConstF-∘-≃ Sets (extendEnvFVar α ⊢H)
  SetSem-extendFunCtx-≃ {α = α} 𝟙-I ⊢H = ConstF-∘-≃ Sets (extendEnvFVar α ⊢H)
  SetSem-extendFunCtx-≃ {Γ} {Φ} {α = α} {H = H} (AppT-I {k = k} {φ = φ} Γ∋φ Fs ⊢Fs) ⊢H = 
    let ⟦Fs[H]⟧ = SetSemVec {k} {Γ} {Φ} {replaceVec Fs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Fs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Fs ⊢H ⊢Fs))
        ⟦Fs⟧    = SetSemVec {k} {Γ} {Φ ,, α} {Fs} ⊢Fs
        extendH = extendEnvFVar {Γ} {Φ} {H} α ⊢H

        ⟦Fs[H]⟧≃⟦Fs⟧∘extend : ⟦Fs[H]⟧ ≃ (⟦Fs⟧ ∘F extendH)
        ⟦Fs[H]⟧≃⟦Fs⟧∘extend = SetSemVec-extendFunCtx-≃ ⊢Fs ⊢H 

        VarSem-proof : (VarSem-TC φ ※ ⟦Fs[H]⟧) ≃ (VarSem-TC φ ※ ⟦Fs⟧) ∘F extendH
        VarSem-proof =
          begin≃
                ( VarSem-TC φ ※ ⟦Fs[H]⟧ )
                ≃⟨   (NI.refl { x = VarSem-TC φ})  ※ⁿⁱ ⟦Fs[H]⟧≃⟦Fs⟧∘extend       ⟩
                ( VarSem-TC φ ※ ⟦Fs⟧ ∘F extendH )
                -- VarSem-TC-extend-≃ : VarSem-TC φ
                --                      ≃ VarSem-TC φ ∘F extendEnvFVar α ⊢H 
                ≃⟨   VarSem-TC-extend-≃ α ⊢H φ  ※ⁿⁱ (NI.refl {x = (⟦Fs⟧ ∘F extendH)})     ⟩
                ( VarSem-TC φ ∘F extendH ※ ⟦Fs⟧ ∘F extendH )
                ≃⟨  ※-distrib [Sets^ k ,Sets] (Sets^ k) (VarSem-TC φ) ⟦Fs⟧ extendH   ⟩
                (VarSem-TC φ ※ ⟦Fs⟧) ∘F extendH
               ≃∎    

        -- ※-distrib : {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level} {A : Category o₁ ℓ₁ e₁} {B : Category o₂ ℓ₂ e₂}
        --   → (F : Functor B C) → (G : Functor B D) → (H : Functor A B)
        --   → ((F ∘F H) ※ (G ∘F H)) ≃ ((F ※ G) ∘F H)

     in    eval-≃ (VarSem-TC {k} φ ※ ⟦Fs[H]⟧ ) (VarSem-TC {k} φ ※ ⟦Fs⟧ ) (extendH) VarSem-proof        

        -- begin≃
        --   eval ∘F (VarSem-TC {k} φ ※ SetSemVec {k} {Γ} {Φ} {replaceVec Fs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Fs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Fs ⊢H ⊢Fs)))
        -- ≃⟨ {!!} ⟩ 
        --   (eval ∘F (VarSem-TC {k} φ ※ SetSemVec {k} {Γ} {Φ ,, α} {Fs} ⊢Fs)) ∘F extendEnvFVar {Γ} {Φ} {H} α ⊢H
        -- ≃∎     


  -- F = VarSem-TC \dotstar SetSemVec (replaceVec-preserves H Fs ⊢H (foreach-preserves-subst H Fs ⊢H ⊢Fs))
  -- G = VarSem-TC \dotstar SetSemVec ⊢Fs
  -- H = extendEnvFVar α ⊢H 

  -- eval-≃ : ∀ {ao al ae bo bl be co cl ce ddo dl de : Level} {A : Category ao al ae} {B : Category bo bl be} {C : Category co cl ce} {D : Category ddo dl de}
  --          → (F : Functor A (Product (Functors C D) C)) 
  --          → (G : Functor B (Product (Functors C D) C))
  --          → (H : Functor A B) 
  --          → F ≃ (G ∘F H) → eval ∘F F ≃ (eval ∘F G) ∘F H 


-- SetSemVec {k} {Γ} {Φ} {replaceVec Gs α H} (replaceVec-preserves {k} {Γ} {Φ} {α} H Gs ⊢H (foreach-preserves-subst {k} {Γ} {Φ} {α} H Gs ⊢H ⊢Gs))

-- AppF goal : 
--     SetSem (fo-subst-preserves-typing AppF φ [ Fs ] H (AppF-I Φ∋φ Fs ⊢Fs) ⊢H)
--     ≃ SetSem (AppF-I Φ∋φ Fs ⊢Fs) ∘F extendEnvFVar α ⊢H

  SetSem-extendFunCtx-≃ {Γ} {Φ} {α = α ^F zero} {H = H} (AppF-I {k = zero} {φ = φ ^F zero} Φ∋φ [] tt) ⊢H with φ ≟ α 
  -- WTS 
  -- SetSem ⊢H ≃ 
  -- (eval ∘F (VarSem-FV (α ^F 0) ※ const [])) 
  --   ∘F extendEnvFVar (α ^F 0) ⊢H 

  -- VarSem-FV-subst-α-≃ : SetSem ⊢H 
  --                     ≃ (eval ∘F (VarSem-FV α ※ ConstF [])) ∘F extendEnvFVar α ⊢H 

  ... | yes ≡.refl = VarSem-FV-subst-α-≃ {k = zero} {Γ} {Φ} {H} α ⊢H φ    -- this takes a while to type-check, maybe make it abstract 
  ... | no ¬φ≡α = 
    let ⟦Fs[H]⟧ = SetSemVec {zero} {Γ} {Φ} {replaceVec [] (α ^F 0) H} (replaceVec-preserves {zero} {Γ} {Φ} {α ^F 0} H [] ⊢H (foreach-preserves-subst {zero} {Γ} {Φ} {α ^F 0} H [] ⊢H tt))
        ⟦Fs⟧    = SetSemVec {zero} {Γ} {Φ ,, (α ^F 0)} {[]} tt
        extendH = extendEnvFVar {Γ} {Φ} {H} (α ^F 0) ⊢H

        ⟦Fs[H]⟧≃⟦Fs⟧∘extend : ⟦Fs[H]⟧ ≃ (⟦Fs⟧ ∘F extendH)
        ⟦Fs[H]⟧≃⟦Fs⟧∘extend = SetSemVec-extendFunCtx-≃ {α = α ^F 0} tt ⊢H 

        -- TODO generalize this to use the same thing in this case and next case 
        VarSem-FV-proof : (VarSem-FV (φ ^F zero) ※ ⟦Fs[H]⟧) ≃ (VarSem-FV (φ ^F zero) ※ ⟦Fs⟧) ∘F extendH
        VarSem-FV-proof =
          begin≃
                ( VarSem-FV (φ ^F zero) ※ ⟦Fs[H]⟧ )
                ≃⟨   (NI.refl { x = VarSem-FV (φ ^F zero)})  ※ⁿⁱ ⟦Fs[H]⟧≃⟦Fs⟧∘extend       ⟩
                ( VarSem-FV (φ ^F zero) ※ ⟦Fs⟧ ∘F extendH )
                -- VarSem-FV-extend-≃ : VarSem-FV φ
                --                      ≃ VarSem-FV φ ∘F extendEnvFVar α ⊢H 
                -- ≃⟨   VarSem-FV-extend-≃ α ⊢H φ  ※ⁿⁱ (NI.refl {x = (⟦Fs⟧ ∘F extendH)})     ⟩
                ≃⟨ VarSem-FV-extend-diffId-≃ {k = zero} {Γ} {Φ} {H} α ⊢H φ ¬φ≡α ※ⁿⁱ (NI.refl {x = (⟦Fs⟧ ∘F extendH)})     ⟩
                ( VarSem-FV (φ ^F zero) ∘F extendH ※ ⟦Fs⟧ ∘F extendH )
                ≃⟨  ※-distrib [Sets^ (zero) ,Sets] (Sets^ (zero)) (VarSem-FV (φ ^F zero)) ⟦Fs⟧ extendH   ⟩
                (VarSem-FV (φ ^F zero) ※ ⟦Fs⟧) ∘F extendH
               ≃∎    

    in   eval-≃ (VarSem-FV {zero} (φ ^F (zero)) ※ ⟦Fs[H]⟧) (VarSem-FV {zero} (φ ^F (zero))  ※ ⟦Fs⟧) extendH VarSem-FV-proof     
    -- eval-≃ (VarSem-FV {zero} (φ ^F (zero)) ※ ⟦Fs[H]⟧) (VarSem-FV {zero} (φ ^F (zero))  ※ ⟦Fs⟧) extendH VarSem-FV-proof 


  SetSem-extendFunCtx-≃ {Γ} {Φ} {α = α ^F zero} {H = H} (AppF-I {k = suc k} {φ = φ ^F suc k} Φ∋φ (F ∷ Fs) (⊢F , ⊢Fs)) ⊢H = 
    let ⟦Fs[H]⟧ = SetSemVec {suc k} {Γ} {Φ} {replaceVec (F ∷ Fs) (α ^F 0) H} (replaceVec-preserves {suc k} {Γ} {Φ} {α ^F 0} H (F ∷ Fs) ⊢H (foreach-preserves-subst {suc k} {Γ} {Φ} {α ^F 0} H (F ∷ Fs) ⊢H (⊢F , ⊢Fs)))
        ⟦Fs⟧    = SetSemVec {suc k} {Γ} {Φ ,, (α ^F 0)} {F ∷ Fs} (⊢F , ⊢Fs)
        extendH = extendEnvFVar {Γ} {Φ} {H} (α ^F 0) ⊢H

        ⟦Fs[H]⟧≃⟦Fs⟧∘extend : ⟦Fs[H]⟧ ≃ (⟦Fs⟧ ∘F extendH)
        ⟦Fs[H]⟧≃⟦Fs⟧∘extend = SetSemVec-extendFunCtx-≃ (⊢F , ⊢Fs) ⊢H 

        VarSem-FV-proof : (VarSem-FV (φ ^F suc k) ※ ⟦Fs[H]⟧) ≃ (VarSem-FV (φ ^F suc k) ※ ⟦Fs⟧) ∘F extendH
        VarSem-FV-proof =
          begin≃
                ( VarSem-FV (φ ^F suc k) ※ ⟦Fs[H]⟧ )
                ≃⟨   (NI.refl { x = VarSem-FV (φ ^F suc k)})  ※ⁿⁱ ⟦Fs[H]⟧≃⟦Fs⟧∘extend       ⟩
                ( VarSem-FV (φ ^F suc k) ※ ⟦Fs⟧ ∘F extendH )
                -- VarSem-FV-extend-≃ : VarSem-FV φ
                --                      ≃ VarSem-FV φ ∘F extendEnvFVar α ⊢H 
                ≃⟨   VarSem-FV-extend-≃ α ⊢H φ  ※ⁿⁱ (NI.refl {x = (⟦Fs⟧ ∘F extendH)})     ⟩
                ( VarSem-FV (φ ^F suc k) ∘F extendH ※ ⟦Fs⟧ ∘F extendH )
                ≃⟨  ※-distrib [Sets^ (suc k) ,Sets] (Sets^ (suc k)) (VarSem-FV (φ ^F suc k)) ⟦Fs⟧ extendH   ⟩
                (VarSem-FV (φ ^F suc k) ※ ⟦Fs⟧) ∘F extendH
               ≃∎    

    in eval-≃ (VarSem-FV {suc k} (φ ^F (suc k)) ※ ⟦Fs[H]⟧) (VarSem-FV {suc k} (φ ^F (suc k))  ※ ⟦Fs⟧) extendH VarSem-FV-proof 


  -- fo-subst-preserves-typing {α = α ^F 0} AppF (φ ^F 0) [ [] ] H (AppF-I Φ,α∋φ [] ⊤) ⊢H with φ ≟ α
  -- ... | yes refl = ⊢H
  -- ... | no ¬φ≡α = AppF-I (diffIdFun (≢-sym ¬φ≡α) Φ,α∋φ) [] Data.Unit.tt
  -- fo-subst-preserves-typing {α = α ^F 0} AppF φ ^F suc k [ G ∷ Gs ] H (AppF-I Φ,α∋φ .(G ∷ Gs) (⊢G , ⊢Gs)) ⊢H = 
  --   AppF-I (diffArityFun (λ()) Φ,α∋φ) ((G [ (α ^F 0) := H ]) ∷ replaceVec Gs (α ^F 0) H)
  --           ((fo-subst-preserves-typing G H ⊢G ⊢H) , (replaceVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs)))



  -- SetSem-extendFunCtx-≃ {Γ} {Φ} {α = α ^F j} {H = H} (AppF-I {k = k} {φ = φ ^F k} Φ∋φ Fs ⊢Fs) ⊢H with eqNat k j | φ ≟ α 
  -- ... | yes ≡.refl | yes ≡.refl = {!   !}
  -- -- next two cases coincide 
  -- -- -- need to use the fact that φ≢α (in arity or in Id) to deduce that VarSem-FV φ ≃ VarSem-FV φ ∘F extendEnvFVar α 
  -- ... | yes ≡.refl | no φ≢α   = {!   !}
  -- ... | no k≢j   | _ = {!   !}
 
 --  {! SetSem
 --    (fo-subst-preserves-typing AppF φ [ Fs ] H (AppF-I Φ∋φ Fs ⊢Fs) ⊢H)
 --    ≃ SetSem (AppF-I Φ∋φ Fs ⊢Fs) ∘F extendEnvFVar α ⊢H  !}

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
        ≃⟨ SetSum ≃ˡ compose-distrib-≃ {F = ⟦F[H]⟧}  {F' = ⟦F⟧} {G = ⟦G[H]⟧} {G' = ⟦G⟧} {H = extendH} ⟦F[H]⟧≃⟦F⟧∘extend ⟦G[H]⟧≃⟦G⟧∘extend  ⟩
        -- ≃⟨ SetSum ≃ˡ {! compose-distrib-≃ {F = ⟦F[H]⟧} {G = ⟦G[H]⟧} {F' = ⟦F⟧} {G' = ⟦G⟧} {H = extendH} ⟦F[H]⟧≃⟦F⟧∘extend ⟦G[H]⟧≃⟦G⟧∘extend  !}  ⟩
        -- ≃⟨ SetSum ≃ˡ (⟦F[H]⟧≃⟦F⟧∘extend ※ⁿⁱ ⟦G[H]⟧≃⟦G⟧∘extend) ⟩
        --   SetSum ∘F ((⟦F⟧ ∘F extendH) ※ (⟦G⟧ ∘F extendH))
        -- ≃⟨ SetSum ≃ˡ (※-distrib Sets Sets ⟦F⟧ ⟦G⟧ extendH) ⟩
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
        ≃⟨ SetProd ≃ˡ compose-distrib-≃ {F = ⟦F[H]⟧}  {F' = ⟦F⟧} {G = ⟦G[H]⟧} {G' = ⟦G⟧} {H = extendH} ⟦F[H]⟧≃⟦F⟧∘extend ⟦G[H]⟧≃⟦G⟧∘extend  ⟩
        -- ≃⟨ SetProd ≃ˡ (⟦F[H]⟧≃⟦F⟧∘extend ※ⁿⁱ ⟦G[H]⟧≃⟦G⟧∘extend) ⟩
        --   SetProd ∘F ((⟦F⟧ ∘F extendH) ※ (⟦G⟧ ∘F extendH))
        -- ≃⟨ SetProd ≃ˡ (※-distrib Sets Sets ⟦F⟧ ⟦G⟧ extendH) ⟩
          SetProd ∘F ((⟦F⟧ ※ ⟦G⟧) ∘F extendH)
        ≃˘⟨ NI.associator extendH (⟦F⟧ ※ ⟦G⟧) SetProd ⟩
          (SetProd ∘F (⟦F⟧ ※ ⟦G⟧)) ∘F extendH
        ≃∎





        -- okay, Sum and product cases also have the form of 
        -- 
        -- 
        -- (F ※ G) 
        -- (F' ∘F E) ※ (G' ∘F E)
        -- (F' ※ G') ∘F E 
        -- 
        -- where we have proofs of F ≃ F' ∘F E 

  SetSem-extendFunCtx-≃ {α = α} (Nat-I {αs = αs} ⊢F ⊢G) ⊢H = NatTypeSem-∘-≃ ⊢H {β = α} {αs = αs} {⟦F⟧ = SetSem ⊢F} {⟦G⟧ = SetSem ⊢G}



  -- STOPPED HERE 
  -- helper function μ-SetSem-extend... type checks in a reasonable amount of time, but this does not..
  -- -- still slow after giving all implicit arguments in the type of this function 
  -- 
  -- -- solution: had to make TEnv abstract 
  SetSem-extendFunCtx-≃ {Γ} {Φ} {α} {H = H} (μ-I {k = k} {φ = φ} {αs = αs} F ⊢F Gs ⊢Gs) ⊢H = μ-SetSem-extendFunCtx-≃ {k} {Γ = Γ} {F} {Φ = Φ} {α} {H = H} {φ} {αs} ⊢F {Gs} ⊢Gs ⊢H

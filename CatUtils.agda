

module CatUtils where 


open import Data.Product using (_,_)
open import Categories.Category 
open import Categories.Functor renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.NaturalIsomorphism as NI 
open import Categories.NaturalTransformation renaming (id to idnat) 
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) renaming (_ⓘˡ_ to _≃ˡ_)
import Categories.Morphism as Mor

open import Level 
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_) 
open import Function renaming (id to idf ; _∘_ to _∘'_) 
open import Categories.Category.Product
open import Categories.Category.Product.Properties using (※-distrib)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)


module ⁂-properties
        {oa la ea ob lb eb oc lc ec : Level}
        {oa' la' ea'  oc' lc' ec' : Level}
        {A  : Category oa la ea}
        {A' : Category oa' la' ea'}
        {B  : Category ob lb eb}
        -- {B' : Category ob' lb' eb'}
        {C  : Category oc lc ec}
        {C' : Category oc' lc' ec'}
  where 

    private module C = Category C
    private module C' = Category C' 

    private module MRC = MR C
    private module MRC' = MR C' 
    -- import Categories.Morphism.Reasoning C as MR
    -- import Categories.Morphism.Reasoning C' as MR'

    -- take arguments in order they appear on the LHS 
    ⁂-distrib : ∀ {ob' lb' eb' : Level} {B' : Category ob' lb' eb'} (G : Functor B C) (F : Functor A B) (G' : Functor B' C') (F' : Functor A' B')
                → ((G ∘F F) ⁂ (G' ∘F F'))
                ≃ ((G ⁂ G') ∘F (F ⁂ F'))
    ⁂-distrib G F G' F' =
      niHelper (record { η   = λ { _ → C.id , C'.id }  
                       ; η⁻¹ = λ { _ → C.id , C'.id }  
                       ; commute = λ _ → MRC.id-comm-sym , MRC'.id-comm-sym
                       ; iso = λ _ → record { isoˡ = C.identity² , C'.identity²
                                            ; isoʳ = C.identity² , C'.identity² }}) 
  
    -- let one of the functors be an identity 
    ⁂-distribˡ : ∀ (G : Functor B C) (F : Functor A B) (F' : Functor A' C') 
                → ((G ∘F F) ⁂ F')
                ≃ ((G ⁂ idF) ∘F (F ⁂ F'))
    ⁂-distribˡ G F F' =
      niHelper (record { η   = λ _ → C.id , C'.id
                       ; η⁻¹ = λ _ → C.id , C'.id
                       ; commute = λ _ → MRC.id-comm-sym , MRC'.id-comm-sym
                       ; iso = λ _ → record { isoˡ = C.identity²  , C'.identity² ; isoʳ = C.identity² , C'.identity² }  }) 


open ⁂-properties 


-- reflexivity of isomorphism 
module _ {o l e  : Level} (C : Category o l e) where
  open Category C
  open Mor C 
  open import Relation.Binary.Definitions

  iso-id : ∀ {X : Obj} → Mor.Iso C (id {X}) (id {X})
  iso-id = record { isoˡ = identityˡ ; isoʳ = identityʳ } 

module NI-properties 
    {o l e o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'}
    where 

    private module C' = Category C'
    private module MRC' = MR C'

    NI-identityˡ : ∀ (F : Functor C C')
                → idF {C = C'} ∘F F
                ≃ F
    NI-identityˡ F = niHelper (record { η = λ X → C'.id ; η⁻¹ = λ X → C'.id ; commute = λ f → MRC'.id-comm-sym ; iso = λ X → iso-id C' }) 

    NI-identityʳ : ∀ (F : Functor C C')
                → F ∘F idF {C = C} 
                ≃ F
    NI-identityʳ F = niHelper (record { η = λ X → C'.id ; η⁻¹ = λ X → C'.id ; commute = λ f → MRC'.id-comm-sym ; iso = λ X → iso-id C'  }) 



-- reasoning combinators for NaturalIsomorphism 
module ≃-Reasoning {o l e  o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'}  where

  -- making this abstract doesn't seem to help speeding up type checking for
  -- long equational chains of ≃ 
  abstract 

        infix  3 _≃∎
        infixr 2 _≃⟨⟩_ step-≃ step-≃˘
        infix  1 begin≃_

        begin≃_ : ∀ {F G : Functor C C'} → F ≃ G → F ≃ G
        begin≃_ F≃G = F≃G

        _≃⟨⟩_ : ∀ (F {G} : Functor C C') → F ≃ G → F ≃ G
        _ ≃⟨⟩ F≃G = F≃G

        step-≃ : ∀ (F {G H} : Functor C C') → G ≃ H → F ≃ G → F ≃ H
        step-≃ F {G} {H} G≃H F≃G = NI.trans {i = F} {j = G} {k = H} F≃G G≃H 

        step-≃˘ : ∀ (F {G H} : Functor C C') → G ≃ H → G ≃ F → F ≃ H
        step-≃˘ F {G} {H} G≃H G≃F = NI.trans {i = F} {j = G} {k = H} (NI.sym G≃F) G≃H

        _≃∎ : ∀ (F : Functor C C') → F ≃ F
        _≃∎ F = NI.refl {x = F} 

        syntax step-≃  F G≃H F≃G = F ≃⟨  F≃G ⟩ G≃H
        syntax step-≃˘ F G≃H G≃F = F ≃˘⟨ G≃F ⟩ G≃H


-- need reasoning combinators for natural isomorphisms that
-- don't expand the definitions of functors when type checking 
module ≃-Reasoning-abstract {o l e  o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'}  where

  -- making this abstract doesn't seem to help speeding up type checking for
  -- long equational chains of ≃ 

  infix  3 _≃∎
  infixr 2 _≃⟨⟩_ step-≃ step-≃˘
  infix  1 begin≃_

  begin≃_ : ∀ {F G : Functor C C'} → F ≃ G → F ≃ G
  begin≃_ F≃G = F≃G

  _≃⟨⟩_ : ∀ (F {G} : Functor C C') → F ≃ G → F ≃ G
  _ ≃⟨⟩ F≃G = F≃G


  -- trans : Transitive (NaturalIsomorphism {C = C} {D = D})
  -- trans = flip _ⓘᵥ_
  open import Relation.Binary.Definitions 

  abstract
    NI-trans : Transitive (NI.NaturalIsomorphism {C = C} {D = C'}) 
    NI-trans = NI.trans

    NI-sym : Symmetric (NI.NaturalIsomorphism {C = C} {D = C'}) 
    NI-sym = NI.sym 

    NI-refl : Reflexive (NI.NaturalIsomorphism {C = C} {D = C'}) 
    NI-refl = NI.refl 


  step-≃ : ∀ (F {G H} : Functor C C') → G ≃ H → F ≃ G → F ≃ H
  step-≃ F {G} {H} G≃H F≃G = NI-trans {i = F} {j = G} {k = H} F≃G G≃H 

  step-≃˘ : ∀ (F {G H} : Functor C C') → G ≃ H → G ≃ F → F ≃ H
  step-≃˘ F {G} {H} G≃H G≃F = NI-trans {i = F} {j = G} {k = H} (NI-sym G≃F) G≃H

  _≃∎ : ∀ (F : Functor C C') → F ≃ F
  _≃∎ F = NI-refl {x = F} 

  syntax step-≃  F G≃H F≃G = F ≃⟨  F≃G ⟩ G≃H
  syntax step-≃˘ F G≃H G≃F = F ≃˘⟨ G≃F ⟩ G≃H

open ≃-Reasoning


{-
-- litmus test for type-checking natural isomorphisms
--
-- takes about 20-30s to type check (even with ≃-Reasoning-abstract) 
module test-iso 
    {o1 l1 e1 l0 e0 : Level}
    {RE SE RT SF : Category o1 l1 e1}
    {Rk : Category o1 l1 e0}
    {Sk : Category o1 l0 e0}
    (FEnv : Functor RE SE)
    (FRT : Functor RT SF)
    (FV : Functor Rk Sk)
    (RA : Functor (Product RE Rk) RE)
    (RP : Functor (Product RE RT) RE)
    (SA : Functor (Product SE Sk) SE)
    (SP : Functor (Product SE SF) SE)
    where

    idFR : Functor Rk Rk
    idFR = idF {C = Rk}

    idFS : Functor Sk Sk
    idFS = idF {C = Sk} 

    Fibred : FEnv ∘F RA ≃ SA ∘F (FEnv ⁂ FV)
            → FEnv ∘F RP ≃ SP ∘F (FEnv ⁂ FRT)
            --
            → FEnv ∘F (RA ∘F (RP ⁂ (idF {C = Rk}))) 
            ≃ (SA ∘F (SP ⁂ (idF {C = Sk}))) ∘F ((FEnv ⁂ FRT) ⁂ FV)
    Fibred αs-lem φ-lem = 
        begin≃ (FEnv ∘F (RA ∘F (RP ⁂ idFR)))
                ≃⟨ NI.sym-associator (RP ⁂ idFR) RA FEnv ⟩
                (FEnv ∘F RA) ∘F (RP ⁂ idFR)
                ≃⟨ αs-lem NI.ⓘʳ (RP ⁂ idFR)  ⟩ -- αs  lem 
                (SA ∘F (FEnv ⁂ FV)) ∘F (RP ⁂ idFR)
                ≃⟨ NI.associator  (RP ⁂ idFR) (FEnv ⁂ FV) SA ⟩
                SA ∘F ((FEnv ⁂ FV) ∘F (RP ⁂ idFR))
                ≃⟨  SA NI.ⓘˡ lem ⟩
                SA ∘F ((SP ⁂ idFS) ∘F ((FEnv ⁂ FRT) ⁂ FV))
                ≃⟨ NI.sym-associator ((FEnv ⁂ FRT) ⁂ FV) (SP ⁂ idFS) SA ⟩
                (SA ∘F (SP ⁂ idFS)) ∘F ((FEnv ⁂ FRT) ⁂ FV)
                ≃∎ 
        where
                idR-≃ : FV ∘F idFR ≃ FV
                idR-≃ = NI-properties.NI-identityʳ FV


                lem : ((FEnv ⁂ FV) ∘F (RP ⁂ idFR)) ≃ ((SP ⁂ idFS) ∘F ((FEnv ⁂ FRT) ⁂ FV))
                lem = begin≃ ((FEnv ⁂ FV) ∘F (RP ⁂ idFR))
                            ≃˘⟨  ⁂-distrib FEnv RP FV idFR   ⟩
                            ((FEnv ∘F RP) ⁂ (FV ∘F idFR))
                            ≃⟨  φ-lem ⁂ⁿⁱ idR-≃  ⟩
                            ((SP ∘F (FEnv ⁂ FRT)) ⁂ FV)
                            ≃⟨ ⁂-distribˡ SP (FEnv ⁂ FRT) FV    ⟩
                            (SP ⁂ idFS) ∘F ((FEnv ⁂ FRT) ⁂ FV)
                            ≃∎   
                        where open ≃-Reasoning-abstract {C = Product (Product RE RT) Rk} {C' = Product SE Sk}

                open ≃-Reasoning-abstract {C = Product (Product RE RT) Rk} {C' = SE}

-}





module NITest
  {o1 l1 e1
   o2 l2 e2
   o3 l3 e3
   o4 l4 e4
   o5 l5 e5
   o6 l6 e6
   o7 l7 e7
   o8 l8 e8
   o9 l9 e9
   o0 l0 e0 : Level } 
   {C1 : Category o1 l1 e1}
   {C2 : Category o2 l2 e2}
   {C3 : Category o3 l3 e3}
   {C4 : Category o4 l4 e4}
   {C5 : Category o5 l5 e5}
   {C6 : Category o6 l6 e6}
   {C7 : Category o7 l7 e7}
   {C8 : Category o8 l8 e8}
   {C9 : Category o9 l9 e9}
   {C0 : Category o0 l0 e0}
   {F1 : Functor C1 C2}
   {F2 : Functor C2 C3}
   {F3 : Functor C3 C4}
   {F4 : Functor C4 C5}
   {F5 : Functor C5 C6}
   {F6 : Functor C6 C7}
   {F7 : Functor C7 C8}
   {F8 : Functor C8 C9}
  where 

  open import Categories.Functor renaming (_∘F_ to _∘_)

  big-assoc : (F6 ∘ (F5 ∘ (F4 ∘ (F3 ∘ (F2 ∘ F1))))) ≃ (((((F6 ∘ F5) ∘ F4) ∘ F3) ∘ F2) ∘ F1)
  big-assoc = begin≃ F6 ∘ F5 ∘ F4 ∘ F3 ∘ F2 ∘ F1
                     ≃⟨ NI.sym-associator (F4 ∘ F3 ∘ F2 ∘ F1) F5 F6 ⟩
                     (F6 ∘ F5) ∘ (F4 ∘ (F3 ∘ F2 ∘ F1))
                     ≃⟨ NI.sym-associator (F3 ∘ F2 ∘ F1) F4 (F6 ∘ F5) ⟩
                     ((F6 ∘ F5) ∘ F4) ∘ (F3 ∘ F2 ∘ F1)
                     ≃⟨ NI.sym-associator (F2 ∘ F1) F3 ((F6 ∘ F5) ∘ F4) ⟩
                     (((F6 ∘ F5) ∘ F4) ∘ F3) ∘ (F2 ∘ F1)
                     ≃⟨ NI.sym-associator F1 F2 (((F6 ∘ F5) ∘ F4) ∘ F3) ⟩
                     (((((F6 ∘ F5) ∘ F4) ∘ F3) ∘ F2) ∘ F1) ≃∎  





{-
module ≃-Reasoning where

  -- _ⓘᵥ_ : {F G H : Functor C D} → G ≃ H → F ≃ G → F ≃ H

  infix  3 _≃∎
  infixr 2 _≃⟨⟩_ step-≃ step-≃˘
  infix  1 begin≃_

  begin≃_ : ∀ {o l e o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'} {F G : Functor C C'} → F ≃ G → F ≃ G
  begin≃_ F≃G = F≃G

  _≃⟨⟩_ : ∀ {o l e o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'} (F {G} : Functor C C') → F ≃ G → F ≃ G
  _ ≃⟨⟩ F≃G = F≃G

  step-≃ : ∀ {o l e o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'} (F {G H} : Functor C C') → G ≃ H → F ≃ G → F ≃ H
  step-≃ F {G} {H} G≃H F≃G = NI.trans {i = F} {j = G} {k = H} F≃G G≃H 

  step-≃˘ : ∀ {o l e o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'} (F {G H} : Functor C C') → G ≃ H → G ≃ F → F ≃ H
  step-≃˘ F {G} {H} G≃H G≃F = NI.trans {i = F} {j = G} {k = H} (NI.sym {x = G} {y = F} G≃F) G≃H

  _≃∎ : ∀ {o l e o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'} (F : Functor C C') → F ≃ F
  _≃∎ F = NI.refl {x = F} 

  syntax step-≃  F G≃H F≃G = F ≃⟨  F≃G ⟩ G≃H
  syntax step-≃˘ F G≃H G≃F = F ≃˘⟨ G≃F ⟩ G≃H

open ≃-Reasoning
-}






NI-≡ : ∀ {o l e o' l' e'} {C : Category o l e} {C' : Category o' l' e'} {F G : Functor C C'}
       → F ≡ G 
       → F ≃ G
NI-≡ ≡.refl = NI.refl

-- -- eval : Bifunctor (Functors C D) C D 
-- -- eval : Functor (Product (Functors C D) C) D 

private
    variable
        o l e o' l' e' o'' l'' e'' : Level 
        C : Category o l e 
        D : Category o' l' e' 
        E : Category o'' l'' e'' 




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

-- useful for proving set semantics respects substitution 
compose-distrib-≃ : ∀ {ao al ae bo bl be co cl ce ddo dl de : Level} 
                    {A : Category ao al ae} {B : Category bo bl be}
                    -- target of F 
                    {C : Category co cl ce} {D : Category ddo dl de}
                    -- target of G 
                    -- {CG : Category cgo cgl cge } {DG : Category dgo dgl dge }
                    → {F  : Functor A C}
                    → {F' : Functor B C}
                    → {G  : Functor A D}
                    → {G' : Functor B D}
                    → {H : Functor A B}
                    → F ≃ (F' ∘F H) 
                    → G ≃ (G' ∘F H) 
                    → (F ※ G) ≃ (F' ※ G') ∘F H
compose-distrib-≃ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} η1 η2 = 
    begin≃ 
        (F ※ G)
        ≃⟨ (η1 ※ⁿⁱ η2) ⟩
        ((F' ∘F H) ※ (G' ∘F H)) 
        ≃⟨ ※-distrib C D F' G' H  ⟩
        ((F' ※ G') ∘F H)
        ≃∎ 

-- _∘ˡ_ 
open import Categories.Category.Construction.Functors using (Functors)
precomp-F : (F : Functor D E) → Functor (Functors C D) (Functors C E)
precomp-F F = record
                    { F₀ = λ G → F ∘F G
                    ; F₁ = λ {G} {H} η →  F ∘ˡ η   
                    ; identity = Functor.identity F
                    ; homomorphism = Functor.homomorphism F
                    ; F-resp-≈ = λ f≈g  →  Functor.F-resp-≈ F f≈g
                    } 

postcomp-F : ∀ {C : Category o l e} {D : Category o' l' e'} {E : Category o'' l'' e''} (F : Functor C D) → Functor (Functors D E) (Functors C E)
postcomp-F {C = C} {D} {E} F = record
                    { F₀ = λ G → G ∘F F 
                    ; F₁ = λ {G} {H} η →  η ∘ʳ F
                    ; identity = λ {G} → E.Equiv.refl 
                    ; homomorphism = E.Equiv.refl 
                    ; F-resp-≈ = λ f≈g → f≈g 
                    } 
            where module E = Category E 


-- MuSem : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
--               {φ : FVar k} {αs Vec (FVar 0) k}
--             → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
--             → Functor SetEnvCat (Sets^ k) → Functor SetEnvCat Sets 

-- -- if 
-- MuSem-≃  : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {H : TypeExpr} {Ks : Vec TypeExpr k}
--               {φ : FVar k} {αs : Vec (FVar 0) k}
--             → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H)
--             → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
--             → MuSem ⊢H (SetSemVec ⊢Ks)
--             ≃ MuSem ⊢H (SetSemVec (F ⊢Ks))


abstract 
    μSem-≃ : ∀ {X : Category o l e} {Y : Category o' l' e'} {Z : Category o'' l'' e''} (G : Functor X Z)
            → (SemKs SemJs : Functor X Y)
            → (FV Extend : Functor X X)
            → SemKs ≃ SemJs ∘F Extend
            → FV ≃ FV ∘F Extend
            → (G ∘F FV ※ SemKs)
            ≃ (((G ∘F FV ※ SemJs)) ∘F Extend)
    μSem-≃ {X = X} {Y} {Z} G SemKs SemJs FV Extend SemKs≃SemJs∘H Forget-Extend-≃ = 
        let G-extend-≃ : G ∘F FV ≃ (G ∘F FV) ∘F Extend
            G-extend-≃ = 
                begin≃
                G ∘F FV
                ≃⟨  G ≃ˡ Forget-Extend-≃  ⟩ 
                G ∘F (FV ∘F Extend)
                ≃˘⟨ NI.associator Extend FV G ⟩
                (G ∘F FV) ∘F Extend
                ≃∎

            G-distrib-※ : (((G ∘F FV) ∘F Extend) ※ (SemJs ∘F Extend))
                            ≃ (((G ∘F FV) ※ SemJs) ∘F Extend)
            G-distrib-※ =  ※-distrib Z Y (G ∘F FV) SemJs Extend 

        in begin≃ 
                    (G ∘F FV ※ SemKs)
                ≃⟨  (NI.refl {C = X} {D = Z} {x = G ∘F FV}) ※ⁿⁱ SemKs≃SemJs∘H   ⟩ 
                    (G ∘F FV  ※ (SemJs ∘F Extend))
                ≃⟨  G-extend-≃  ※ⁿⁱ (NI.refl {C = X} {D = Y} {x = SemJs ∘F Extend})   ⟩ 
                    (((G ∘F FV) ∘F Extend) ※ (SemJs ∘F Extend))
                ≃⟨   G-distrib-※   ⟩ 
                    ((G ∘F FV ※ SemJs) ∘F Extend)
                ≃∎




module pointwise-iso {F G : Functor C D} where

  open import Categories.Category using (_[_,_])

  private
    module C = Category C
    module F = Functor F
    module G = Functor G

  import Categories.Morphism as Mor 
  open Category D
  open Mor D
  open _≅_

  -- We can construct a natural isomorphism from a pointwise isomorphism, provided that we can show naturality in one direction.
  pointwise-iso : (iso : ∀ X → F.F₀ X ≅ G.F₀ X) → (∀ {X Y} → (f : C [ X , Y ]) → from (iso Y) ∘ F.F₁ f ≈ G.F₁ f ∘ from (iso X)) → NI.NaturalIsomorphism F G
  pointwise-iso iso commute = NI.niHelper record
    { η = λ X → from (iso X)
    ; η⁻¹ = λ X → to (iso X)
    ; commute = commute
    ; iso = λ X → record
      { isoˡ = isoˡ (iso X)
      ; isoʳ = isoʳ (iso X)
      }
    }







--   import Relation.Binary.HeterogeneousEquality as Het 

--   equiv-iso : ∀ {A B : Obj} → A ≡ B → A ≅ B
--   equiv-iso ≡.refl = record { from = id ; to = id ; iso = record { isoˡ = identityˡ ; isoʳ = identityʳ } } 

--   equiv-iso-from-id : ∀ {A B : Obj} → (e : A ≡ B) → from (equiv-iso e) Het.≅  id
--   equiv-iso-from-id ≡.refl = Het.refl 

--   equiv-iso-from-left : ∀ {A B : Obj} → (e : A ≡ B) → ∀ g → from (equiv-iso e) ∘ g Het.≅ g
--   equiv-iso-from-left ≡.refl g = {!   !}

--   -- equiv-iso-from-id : ∀ {A B : Obj} → (e : A ≡ B) → from (equiv-iso e) ≡ id
--   -- equiv-iso-from-id ≡.refl = Het.refl 

--   open HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎ )
--   -- HomReasoning for D 
  
--   open Het.≅-Reasoning renaming (begin_ to begin≅_ ; _∎ to _≅∎)

--   equiv-iso-natural-Het : ∀ {H K : Functor C Sets} {X Y : Category.Obj C} (f : C [ X , Y ]) 
--                       → (equiv : ∀ X → Functor.F₀ H X ≡ Functor.F₀ K X) 
--                       → (∀ {X Y} → (f : C [ X , Y ]) →  Functor.F₁ H f Het.≅  Functor.F₁ K f)
--                       → from (equiv-iso (equiv Y)) ∘ Functor.F₁ H f Het.≅ Functor.F₁ K f ∘ from (equiv-iso (equiv X))
--   equiv-iso-natural-Het {H} {K} {X} {Y} f equiv map-equiv = 
--     let x = equiv X 
--         y = equiv Y 
--         fg = map-equiv f
--         ey = equiv-iso-from-id y
--       in begin≅ 
--       from (equiv-iso (equiv Y)) ∘ Functor.F₁ H f
--       ≅⟨ Het.cong {!   !}  {!   !} ⟩
--       id ∘ Functor.F₁ H f
--       ≅⟨ {! F.F₁ f  !} ⟩
--       Functor.F₁ H f
--       ≅⟨ map-equiv f ⟩
--       Functor.F₁ K f
--       ≅⟨ {! F.F₁ f  !} ⟩
--       Functor.F₁ K f ∘ id 
--       ≅⟨ {! F.F₁ f  !} ⟩
--       Functor.F₁ K f ∘ from (equiv-iso (equiv X))
--       ≅∎
          
--   -- from (equiv-iso (equiv Y)) ∘ F.F₁ f ≈
--   --       G.F₁ f ∘ from (equiv-iso (equiv X))


--   -- equiv-iso-natural : ∀ {X Y : Category.Obj C} (f : C [ X , Y ]) 
--   --                     → (equiv : ∀ X → F.F₀ X ≡ G.F₀ X) 
--   --                     → (∀ {X Y} → (f : C [ X , Y ]) →  F.F₁ f Het.≅  G.F₁ f)
--   --                     → from (equiv-iso (equiv Y)) ∘ F.F₁ f Het.≅ Functor.F₁ G f ∘ from (equiv-iso (equiv X))
--   -- equiv-iso-natural {X} {Y} f equiv map-equiv = 
--   --   let x = equiv X 
--   --       y = equiv Y 
--   --       fg = map-equiv f
--   --     in begin≅ 
--   --       from (equiv-iso (equiv Y)) ∘ F.F₁ f
--   --     ≅⟨ {! Het.cong (λ g → g ∘ F.F₁ f) (equiv-iso-from-id ?)  !} ⟩
--   --       id ∘ F.F₁ f
--   --     ≅⟨ {! F.F₁ f  !} ⟩
--   --       F.F₁ f
--   --     ≅⟨ {! F.F₁ f  !} ⟩
--   --       F.F₁ f
--   --       Functor.F₁ G f ∘ from (equiv-iso (equiv X))
--   --     ≅∎
          
--   -- -- from (equiv-iso (equiv Y)) ∘ F.F₁ f ≈
--   -- --       G.F₁ f ∘ from (equiv-iso (equiv X))




--   pointwise-iso-het : (equiv : ∀ X → F.F₀ X ≡ G.F₀ X) → (∀ {X Y} → (f : C [ X , Y ]) →  F.F₁ f Het.≅  G.F₁ f) → NI.NaturalIsomorphism F G
--   pointwise-iso-het equiv het-commute = 
--     let x = {!   !}
--       in 
--     pointwise-iso (λ X → equiv-iso (equiv X)) {! equiv-iso-natural   !}
--           -- λ {X} {Y} f → {!   !}
--   --         begin≈ 
--   --           from (equiv-iso (equiv Y)) ∘ F.F₁ f 
--   --         ≈⟨ {! equiv-iso-from-id  !} ⟩
--   --           G.F₁ f ∘ from (equiv-iso (equiv X))
--   --         ≈∎
          
--   -- -- from (equiv-iso (equiv Y)) ∘ F.F₁ f ≈
--   -- --       G.F₁ f ∘ from (equiv-iso (equiv X))



-- {-
--   -- useful for proving set semantics respects substitution 
--   compose-distrib-≃ : ∀ {ao al ae bo bl be co cl ce ddo dl de cgo cgl cge dgo dgl dge : Level} 
--                         {A : Category ao al ae} {B : Category bo bl be}
--                         -- target of F 
--                         {C : Category co cl ce} {D : Category ddo dl de}
--                         -- target of G 
--                         {CG : Category cgo cgl cge } {DG : Category dgo dgl dge }
--                       → (F  : Functor A (Product (Functors C D) C)) 
--                       → (F' : Functor B (Product (Functors C D) C))
--                       → (G  : Functor A (Product (Functors CG DG) CG)) 
--                       → (G' : Functor B (Product (Functors CG DG) CG))
--                       → (H : Functor A B) 
--                       → F ≃ (F' ∘F H) 
--                       → G ≃ (G' ∘F H) 
--                       → (F ※ G) ≃ (F' ※ G') ∘F H
--   compose-distrib-≃ {A = A} {B} {C} {D} {CG} {DG} F F' G G' H η1 η2 = 
--     begin≃ 
--         (F ※ G)
--       ≃⟨ (η1 ※ⁿⁱ η2) ⟩
--         ((F' ∘F H) ※ (G' ∘F H)) 
--       ≃⟨ ※-distrib (Product (Functors C D) C) (Product (Functors CG DG) CG)  F'   G'  H  ⟩
--         ((F' ※ G') ∘F H)
--       ≃∎ 



-- -}



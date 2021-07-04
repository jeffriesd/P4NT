-- {-# OPTIONS --rewriting #-}


module TermSemantics.NatTermSemantics where 

open import Agda.Builtin.Equality.Rewrite



open import Categories.Functor using (Functor ; _∘F_)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.Category using (Category)
open import Categories.Category.Product 
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Unit renaming (⊤ to ⊤') 
open import Data.Empty renaming (⊥ to ⊥') 
open import Data.Vec using (Vec ; [] ; _∷_ ; _++_)
open import Data.Sum renaming ([_,_] to [_,⊎_])
open import Data.Product renaming (_×_ to _×'_  ; map to ×'-map) 
open import Function using (const ; flip) renaming (id to idf; _∘_ to _∘'_)
open import Level renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Nullary using (_because_ ; Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (isYes)

open import SetEnvironments.EnvironmentExtension 
open import SetEnvironments.Core using (SetEnvCat ; SetEnv)
open import SetCats 
open import TypeSemantics.SetSemWeakenFunCtx using (SetSem-weakenFunCtx-NT)
open import TypeSemantics.SetSemantics 
open import Syntax.NestedTypeSyntax
open import Syntax.TermSyntax
open import SetEnvironments.Core
open import HFixFunctorLib 
open import TermSemantics.TermSetSemUtils using (ContextInterp)

open import HetEquality.HetFunctors 
open VecHetEquality
open HetFuncIdentityVec

open import Utils using (foreach ; cong-app-impl)
open ≡.≡-Reasoning


module EmptyPhiPreservesTC where 
-- a bunch of proofs that can be used to show 
--  SetSem ⊢F ≃ SetSem ⊢F ∘F ForgetFVSetEnv 
-- for ⊢F : Γ ≀ ∅ ⊢ F

    -- this might work but the Mu case seems unncessarily difficult 
    -- -- okay actually it's not that bad to propagate het identities
    -- -- up through higher order functor constructions 

    -- SetSem[Vec]-eqTC-const lemmas give 
    -- proof that SetSem ⊢F's (and SetSemVec) 
    -- action on objects (set environments) is the same 
    -- for set environments with equal tc components. 
    -- A morphism of environments is enough for this, but not required.
    -- E.g., we can't always give a morphism from ρ to ρ [ α := X ]
    -- but if α is fvar then tc ρ = tc (ρ [ α := X ])
    -- 
    -- Note this only holds for ⊢F with empty functorial context. 


    {- mutual -}
    SetSemVec-eqTC-const : ∀ {k} {Γ} {Fs : Vec TypeExpr k} → (⊢Fs : foreach (λ F → Γ ≀ ∅ ⊢ F) Fs) (ρ ρ' : SetEnv) 
                    → ρ ≡TC ρ' 
                    → Functor.F₀ (SetSemVec ⊢Fs) ρ 
                    ≡ Functor.F₀ (SetSemVec ⊢Fs) ρ' 

    SetSem-eqTC-const : ∀ {Γ} {F} → (⊢F : Γ ≀ ∅ ⊢ F) (ρ ρ' : SetEnv) 
                    -- → (λ {k} → SetEnv.tc ρ {k})  ≡ (λ {k} → SetEnv.tc ρ' {k})
                    → ρ ≡TC ρ' 
                    → Functor.F₀ (SetSem ⊢F) ρ 
                    ≡ Functor.F₀ (SetSem ⊢F) ρ' 

    SetSemVec-eqTC-const {Fs = []} ⊢Fs ρ ρ' eqTC = ≡.refl 
    SetSemVec-eqTC-const {Fs = F ∷ Fs} (⊢F , ⊢Fs) ρ ρ' eqTC = ≡.cong₂ _∷_ (SetSem-eqTC-const ⊢F ρ ρ' eqTC) (SetSemVec-eqTC-const ⊢Fs ρ ρ' eqTC) 


    SetSem-eqTC-const 𝟘-I ρ ρ' eqTC = ≡.refl
    SetSem-eqTC-const 𝟙-I ρ ρ' eqTC = ≡.refl
    SetSem-eqTC-const (AppT-I {k = k} {φ = φ} Γ∋φ Fs ⊢Fs) ρ ρ' eqTC = ≡.cong₂ Functor.F₀ (≡.cong-app (cong-app-impl eqTC) φ) (SetSemVec-eqTC-const ⊢Fs ρ ρ' eqTC)
    SetSem-eqTC-const (+-I ⊢F ⊢G) ρ ρ' eqTC = ≡.cong₂ _⊎_ (SetSem-eqTC-const ⊢F ρ ρ' eqTC) (SetSem-eqTC-const ⊢G ρ ρ' eqTC)
    SetSem-eqTC-const (×-I ⊢F ⊢G) ρ ρ' eqTC = ≡.cong₂ _×'_ (SetSem-eqTC-const ⊢F ρ ρ' eqTC) (SetSem-eqTC-const ⊢G ρ ρ' eqTC)
    -- 
    SetSem-eqTC-const (Nat-I {k = k} {αs = αs}  ⊢F ⊢G) ρ ρ' eqTC = ≡.cong (λ env → NatTypeSem αs env (⊢F) (⊢G)) (≡.cong NatEnvTC eqTC)

    --   goal : 
    --   HFixFunctor
    -- (Functor.F₀ (TSet ⊢F) Env[ SetEnv.tc ρ , trivFVSetEnv ])
    -- (Functor.F₀ (SetSemVec ⊢Gs) ρ)
    -- ≡
    -- HFixFunctor
    -- (Functor.F₀ (TSet ⊢F) Env[ SetEnv.tc ρ' , trivFVSetEnv ])
    -- (Functor.F₀ (SetSemVec ⊢Gs) ρ')
    SetSem-eqTC-const (μ-I ⊢F Gs ⊢Gs) ρ ρ' ≡.refl rewrite (SetSemVec-eqTC-const ⊢Gs ρ ρ' ≡.refl) = ≡.refl
    {-
        ≡.cong₂ HFixFunctorObj
            (≡.cong (Functor.F₀ (TSet ⊢F)) (≡.cong NatEnvTC eqTC))
            (SetSemVec-eqTC-const ⊢Gs ρ ρ' eqTC)
            -}

    {- end mutual -}


    -- a morphism of environments guarantees ρ ≡TC ρ' ,
    -- so this is a special case of SetSem-eqTC-const 
    SetSem-morph-const : ∀ {Γ} {F} → (⊢F : Γ ≀ ∅ ⊢ F) (ρ ρ' : SetEnv) 
                    → SetEnvMorph ρ ρ'
                    → Functor.F₀ (SetSem ⊢F) ρ 
                    ≡ Functor.F₀ (SetSem ⊢F) ρ' 
    SetSem-morph-const ⊢F ρ ρ' f = SetSem-eqTC-const ⊢F ρ ρ' (SetEnvMorph.eqTC f) 

    -- a morphism of environments guarantees ρ ≡TC ρ' ,
    -- so this is a special case of SetSemVec-eqTC-const
    SetSemVec-morph-const : ∀ {k} {Γ} {Fs : Vec TypeExpr k} → (⊢Fs : foreach (λ F → Γ ≀ ∅ ⊢ F) Fs) (ρ ρ' : SetEnv) 
                    → SetEnvMorph ρ ρ'
                    → Functor.F₀ (SetSemVec ⊢Fs) ρ 
                    ≡ Functor.F₀ (SetSemVec ⊢Fs) ρ' 
    SetSemVec-morph-const ⊢Fs ρ ρ' f = SetSemVec-eqTC-const ⊢Fs ρ ρ' (SetEnvMorph.eqTC f)



    Δ-eqTC-const : ∀ {Γ} → (Δ : TermCtx Γ ∅) (ρ ρ' : SetEnv)  
                    → ρ ≡TC ρ' 
                    → Functor.F₀ (ContextInterp Δ) ρ 
                    ≡ Functor.F₀ (ContextInterp Δ) ρ' 
    Δ-eqTC-const Δ∅ ρ ρ' eqTC = ≡.refl
    Δ-eqTC-const (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) ρ ρ' eqTC = ≡.cong₂ _×'_ (Δ-eqTC-const Δ ρ ρ' eqTC) (SetSem-eqTC-const ⊢F ρ ρ' eqTC) 

    Δ-morph-const : ∀ {Γ} → (Δ : TermCtx Γ ∅) (ρ ρ' : SetEnv)  
                    → (SetEnvMorph ρ ρ')
                    → Functor.F₀ (ContextInterp Δ) ρ 
                    ≡ Functor.F₀ (ContextInterp Δ) ρ' 
    Δ-morph-const Δ ρ ρ' f = Δ-eqTC-const Δ ρ ρ' (SetEnvMorph.eqTC f)

open EmptyPhiPreservesTC




module DConstNaturalIso where 

    -- trying to prove that interpretation of Δ with empty Φ is
    -- naturally isomorphic to the interpretation of Δ with extended environment,
    -- since all the environment extension functors leave the TC environment untouched
    --
    -- this natural isomorphism for interpretation of Δ follows from an analogous natural isomorphism
    -- for interpretation of ⊢F with an environment extension
    -- 
    -- we need this to define the term semantics of L , app, etc. 
    -- don't necessarily need natural iso, but it would be convenient,
    -- and it isn't much harder than defining a natural transformation 
    --
    -- proving equality on objects (environments) is easy, and we can use this equality
    -- to define a morphism between (ConstF... ) ρ and (SetSem ⊢F ∘F extend..) ρ
    -- -- maybe this is the wrong approach? maybe we should just define a function without using a proof of equality? 
    -- the difficult part is proving
    -- naturality, in which we have to prove a commuting triangle  (bc one of the functors is constant), 
    -- where the components of the natural transformation are given by equalities,
    -- and thus we need a proof that (SetSem ⊢F) f x = x.. but because the lhs has type (SetSem ⊢F) ρ'
    -- and the RHS has type (SetSem ⊢F) ρ, we can only express this as a heterogeneous equality. 

    -- The hardest part is threading the heterogeneous equalities through the MuSem construction, 
    -- but it really isnt' that bad. 

    D : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : SetEnv) (αs : Vec (FVar 0) k) → Functor (Sets^ k) Sets
    D Δ ρ αs = ContextInterp Δ ∘F extendSetEnv-αs αs (NatEnv ρ)

    open import Relation.Binary.HeterogeneousEquality using (_≅_)
    import Relation.Binary.HeterogeneousEquality as Het 

    -- to get natural iso / natural transformation from D to ConstF ... we need 
    -- 
    -- (eqFmap : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → Functor.F₁ F f x ≅ x)
    -- (eqGmap : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → Functor.F₁ G f x ≅ x)


    -- (Functor.F₁ (ContextInterp Δ)
    --  (extendfv-morph-vec αs (to0Functors Xs) (to0Functors Ys) ρ ρ idSetEnv (toConstNats fs))
    --  x
    --  ,
    --  Functor.F₁ (SetSem ⊢F)
    --  (extendfv-morph-vec αs (to0Functors Xs) (to0Functors Ys) ρ ρ idSetEnv (toConstNats fs)) fx)
    -- ≅ (x , fx)
    -- 
    -- Functor.F₁ (ContextInterp Δ) (extendfv-morph-vec αs (to0Functors Xs) (to0Functors Ys) ρ ρ idSetEnv (toConstNats fs)) x


    -- SetSem-map-id : ∀ {k} {Γ} {F} → (⊢F : Γ ≀ ∅ ⊢ F) (ρ : SetEnv) (αs : Vec (FVar 0) k) {Xs Ys : Vec Set k} 
    --             → (fs : VecMorph Xs Ys)
    --             → ∀ {x} 
    --             → Functor.F₁ (SetSem ⊢F ∘F extendSetEnv-αs αs ρ) fs x ≅ x 
    -- SetSem-map-id ⊢F ρ αs fs = {!   !} 

    Het-pair-cong : ∀ {A B C D : Set} {x : A} {y : B} {x' : C} {y' : D} → A ≡ C → B ≡ D → x ≅ x' → y ≅ y' → (x , y) ≅ (x' , y')
    Het-pair-cong ≡.refl ≡.refl _≅_.refl _≅_.refl = _≅_.refl

    Het-pair-cong-sym : ∀ {A B C D : Set} {x : A} {y : B} {x' : C} {y' : D} → C ≡ A → D ≡ B → x ≅ x' → y ≅ y' → (x , y) ≅ (x' , y')
    Het-pair-cong-sym ≡.refl ≡.refl _≅_.refl _≅_.refl = _≅_.refl

    -- TODO generalize this for other polymorphic functions 
    -- Het-inj₁-cong : ∀ {A B C : Set} {x : A} {x' : C} → A ≡ C → x ≅ x' → inj₁ {B = B} x ≅ inj₁ {B = B} x' 
    -- Het-inj₁-cong ≡.refl _≅_.refl = _≅_.refl

    Het-inj₁-cong : ∀ {A B A' B' : Set} {x : A} {x' : A'} → A ≡ A' → B ≡ B' → x ≅ x' → inj₁ {A = A} {B = B} x ≅ inj₁ {A = A'} {B = B'} x' 
    Het-inj₁-cong ≡.refl ≡.refl Het.refl = Het.refl

    Het-inj₂-cong : ∀ {A B A' B' : Set} {y : B} {y' : B'} → A ≡ A' → B ≡ B' → y ≅ y' → inj₂ {A = A} {B = B} y ≅ inj₂ {A = A'} {B = B'} y' 
    Het-inj₂-cong ≡.refl ≡.refl Het.refl = Het.refl


    Het-cong-subst-sym : ∀ {a b} {A A' : Set a} {B : A → Set b} {x : A} {y : A'}
        (f : (x : A) → B x) → (e : A' ≡ A) → x ≅ y → f x ≅ f (≡.subst idf e y)
    Het-cong-subst-sym f ≡.refl _≅_.refl = _≅_.refl 

    Het-cong-subst : ∀ {a b} {A A' : Set a} {B : A' → Set b} {x : A} {y : A'}
        (f : (x : A') → B x) → (e : A ≡ A') → x ≅ y → f (≡.subst idf e x) ≅ f y
    Het-cong-subst f ≡.refl _≅_.refl = _≅_.refl 

    -- for non-dependent functions 
    open Het.≅-Reasoning renaming (begin_ to begin≅_ ; _∎ to _≅∎)
    -- not used anywhere 
    Het-cong-fun : ∀ {a b} {A : Set a} {B : Set b} {y : A}
        (f : A → B) → (g : A → A) → g y ≅ y → f (g y) ≅ f y
    Het-cong-fun {y = y} f g e = Het.subst (λ x → f x ≅ f y) (Het.sym e) Het.refl 


    -- mutual 
    SetSem-map-id : ∀ {Γ} {F} → (⊢F : Γ ≀ ∅ ⊢ F) (ρ ρ' : SetEnv) 
                → (f : SetEnvMorph ρ ρ') 
                → ∀ {x} 
                → Functor.F₁ (SetSem ⊢F) f x ≅ x 

    -- -- can't prove intensional equality without assuming extensionality 
    -- SetSemVec-map-id : ∀ {k} {Γ} {Fs : Vec TypeExpr k} → (⊢Fs : foreach (λ F → Γ ≀ ∅ ⊢ F) Fs) (ρ ρ' : SetEnv) 
    --             → (f : SetEnvMorph ρ ρ') 
    --             → ∀ {x} 
    --             → Functor.F₁ (SetSemVec ⊢Fs) f ≅ idf 

    -- but all we really need is an assertion that each function in the vector of functions is 
    -- het-equal to identity , i.e., use 
    -- -- pointwise-het-id : ∀ {k} → {Xs Ys : Vec Set k} → (f : VecMorph Xs Ys) → Set 
    SetSemVec-map-id : ∀ {k} {Γ} {Fs : Vec TypeExpr k} → (⊢Fs : foreach (λ F → Γ ≀ ∅ ⊢ F) Fs) (ρ ρ' : SetEnv) 
                → (f : SetEnvMorph ρ ρ') 
                → pointwise-het-id Sets (Functor.F₁ (SetSemVec ⊢Fs) f)


    -- use HetFunctorialityVec for AppT and Mu cases
    -- to show that Fmap of het-id morphism gives het-id morphism 
    -- open HetFunctorialityVec
    -- open HetFunctorialityFunctors

    -- Mu case seems challenging because need to propagate heterogeneous equality conditions 
    -- through higher order functors 
    SetSem-map-id 𝟙-I ρ ρ' f = _≅_.refl
    -- goal : Functor.F₁ (SetEnv.tc ρ' φ) (Functor.F₁ (SetSemVec ⊢Fs) f) x ≅ x
    SetSem-map-id (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) ρ ρ' f {x} with SetEnvMorph.eqTC f 
    ... | ≡.refl =  let pointwise-het-⊢Fs =    SetSemVec-map-id ⊢Fs ρ ρ' f
                    in Fmap-id Sets (SetEnv.tc ρ' φ) (Functor.F₁ (SetSemVec ⊢Fs) f) pointwise-het-⊢Fs (SetSemVec-morph-const ⊢Fs ρ ρ' f)  

    -- goal : inj₁ (Functor.F₁ (SetSem ⊢F) f x) ≅ inj₁ x
    -- x : Functor.F₀ (SetSem ⊢F) ρ
    -- (Functor.F₁ (SetSem ⊢F) f x) :  Functor.F₀ (SetSem ⊢F) ρ'
    SetSem-map-id (+-I ⊢F ⊢G) ρ ρ' f {inj₁ x} =
        let Fρ  = Functor.F₀ (SetSem ⊢F) ρ
            Fρ' = Functor.F₀ (SetSem ⊢F) ρ'
            Gρ  = Functor.F₀ (SetSem ⊢G) ρ
            Gρ' = Functor.F₀ (SetSem ⊢G) ρ'

            rec : Functor.F₁ (SetSem ⊢F) f x ≅ x 
            rec = SetSem-map-id ⊢F ρ ρ' f {x}

            eqF : Fρ ≡ Fρ'
            eqF = SetSem-morph-const ⊢F ρ ρ' f 
            eqG : Gρ ≡ Gρ'
            eqG = SetSem-morph-const ⊢G ρ ρ' f 

            inj₁fx≅inj₁x : inj₁ {A = Fρ'} {B = Gρ'} (Functor.F₁ (SetSem ⊢F) f x) ≅ inj₁ {A = Fρ} {B = Gρ} x
            inj₁fx≅inj₁x = Het-inj₁-cong (≡.sym eqF) (≡.sym eqG) rec

            in inj₁fx≅inj₁x 

    SetSem-map-id (+-I ⊢F ⊢G) ρ ρ' f {inj₂ y} = 
        let Fρ  = Functor.F₀ (SetSem ⊢F) ρ
            Fρ' = Functor.F₀ (SetSem ⊢F) ρ'
            Gρ  = Functor.F₀ (SetSem ⊢G) ρ
            Gρ' = Functor.F₀ (SetSem ⊢G) ρ'

            rec : Functor.F₁ (SetSem ⊢G) f y ≅ y 
            rec = SetSem-map-id ⊢G ρ ρ' f {y}

            eqF : Fρ ≡ Fρ'
            eqF = SetSem-morph-const ⊢F ρ ρ' f 
            eqG : Gρ ≡ Gρ'
            eqG = SetSem-morph-const ⊢G ρ ρ' f 

            inj₂fy≅inj₂y : inj₂ {A = Fρ'} {B = Gρ'} (Functor.F₁ (SetSem ⊢G) f y) ≅ inj₂ {A = Fρ} {B = Gρ} y
            inj₂fy≅inj₂y = Het-inj₂-cong (≡.sym eqF) (≡.sym eqG) rec

            in inj₂fy≅inj₂y 


    SetSem-map-id (×-I ⊢F ⊢G) ρ ρ' f {fst , snd} = Het-pair-cong-sym (SetSem-morph-const ⊢F ρ ρ' f) (SetSem-morph-const ⊢G ρ ρ' f) (SetSem-map-id ⊢F ρ ρ' f) (SetSem-map-id ⊢G ρ ρ' f)
    SetSem-map-id (Nat-I {αs = αs} ⊢F ⊢G) ρ ρ' f@(record { eqTC = ≡.refl ; fv = fv }) {x} = _≅_.refl
    -- with NatEnv-eq f 
    -- ... | ≡.refl = _≅_.refl 

    -- mu case - match on SetEnvMorph.eqTC f to simplify goal, then propagate
    -- identites through the functors in MuSem 
    SetSem-map-id (μ-I ⊢F Gs ⊢Gs) ρ@(SetEnv[ tc , fv ]) ρ'@(SetEnv[ tc' , fv' ]) f {x} with SetEnvMorph.eqTC f
    SetSem-map-id (μ-I {k = k} ⊢F Gs ⊢Gs) ρ@(SetEnv[ tc , fv ]) ρ'@(SetEnv[ .tc , fv' ]) f {x} | ≡.refl = 
    -- ... | ≡.refl = {!!}
        let pointwise-het-id-Gs : pointwise-het-id (Functor.F₁ (SetSemVec ⊢Gs) f)
            pointwise-het-id-Gs = SetSemVec-map-id ⊢Gs ρ ρ' f 

            Tρ* : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
            Tρ* = Functor.F₀ (TSet ⊢F) (NatEnv ρ)

            TF-id : NaturalTransformation Tρ* Tρ*
            TF-id = Functor.F₁ (TSet ⊢F) (idSetEnv {ρ = NatEnv ρ})

            TF-id-≈ : [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]]
                Categories.Category.[
                    TF-id
                  ≈ Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] ]
                 -- type of TF-id-≈ normalizes to: 
                -- {F : Functor (Sets^ k) Sets} 
                -- {Xs : Vec Set k}
                -- {x : Functor.F₀ (Functor.F₀ (Functor.F₀ (TSet ⊢F) ρ) F) Xs}
                -- → NaturalTransformation.η
                -- (NaturalTransformation.η (Functor.F₁ (TSet ⊢F) idSetEnv) F) Xs
                -- x ≡ x
            TF-id-≈ = Functor.identity (TSet ⊢F) {A = NatEnv ρ}


            H-id-≈  : [Sets^ k ,Sets] Categories.Category.[
                        HFixFunctorLib.fixH₁ Tρ* Tρ*
                        (Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
                    ≈ Category.id [Sets^ k ,Sets] ]
                -- this ≈ normalizes to :
                -- {Xs : Vec Set k}
                -- {x : HFixObj Tρ* Xs} →
                -- HFixFunctorLib.hη Tρ* Tρ* idnat Xs x
                -- ≡ x
            H-id-≈ = Functor.identity fixH {A = Tρ*}


            H-id-2-≈  : [Sets^ k ,Sets] Categories.Category.[
                        HFixFunctorLib.fixH₁ Tρ* Tρ*
                        TF-id
                    ≈ Category.id [Sets^ k ,Sets] ]
            H-id-2-≈  = 
              SK.begin
                       fixH₁ Tρ* Tρ* TF-id    
                    SK.≈⟨ (Functor.F-resp-≈ fixH TF-id-≈ )  ⟩  
                        fixH₁ Tρ* Tρ* (Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]]) 
                    SK.≈⟨ H-id-≈   ⟩  
                        Category.id [Sets^ k ,Sets]
                        SK.∎ 

            hη : (Xs : Vec Set k) → Functor.F₀ (fixH₀ Tρ*) Xs → Functor.F₀ (fixH₀ Tρ*) Xs 
            hη = NaturalTransformation.η (fixH₁ Tρ* Tρ* TF-id)

            
            ⟦Gs⟧ : SetEnv → Vec Set k
            ⟦Gs⟧ = Functor.F₀ (SetSemVec ⊢Gs) 

            ⟦Gs⟧f : VecMorph (⟦Gs⟧ ρ)  (⟦Gs⟧ ρ')
            ⟦Gs⟧f = Functor.F₁ (SetSemVec ⊢Gs) f


            -- use proof that map of higher order functors preserves het identities 
            HFix-fmap-id : ∀ {Xs Ys : Vec Set k} → (e : Xs ≡ Ys) → (fs : VecMorph Xs Ys) → pointwise-het-id fs
                          → ∀ {x} → HFix-fmap Tρ* fs x ≅ x 
            HFix-fmap-id {Xs} {Ys} e fs pointwise-het-fs = Fmap-id (fixH₀ Tρ*) fs pointwise-het-fs e  


            ⟦Gs⟧-equiv : ⟦Gs⟧ ρ ≡ ⟦Gs⟧ ρ' 
            ⟦Gs⟧-equiv = SetSemVec-eqTC-const ⊢Gs ρ ρ' ≡.refl 
        in 
        begin≅
                hη (⟦Gs⟧ ρ') (HFix-fmap Tρ* ⟦Gs⟧f x) 
            ≅⟨ Het.≡-to-≅     H-id-2-≈  ⟩
                HFix-fmap Tρ* ⟦Gs⟧f x 
            ≅⟨ HFix-fmap-id ⟦Gs⟧-equiv ⟦Gs⟧f pointwise-het-id-Gs  ⟩
                x ≅∎

       where module Setk = Category [Sets^ k ,Sets]
             module SK = Setk.HomReasoning


    -- vectors of functions 
    SetSemVec-map-id {Fs = []} ⊢Fs ρ ρ' f = tt 
    SetSemVec-map-id {k = suc k} {Fs = F ∷ Fs} (⊢F , ⊢Fs) ρ ρ' f = (λ {x} → SetSem-map-id ⊢F ρ ρ' f) , (SetSemVec-map-id ⊢Fs ρ ρ' f)
    -- end mutual 




    ContextInterp-map-id : ∀ {Γ} → (Δ : TermCtx Γ ∅) (ρ ρ' : SetEnv) 
                → (f : SetEnvMorph ρ ρ') 
                → ∀ {x} 
                → Functor.F₁ (ContextInterp Δ) f x ≅ x  
    ContextInterp-map-id Δ∅ ρ ρ' f {x} = Het.refl
    ContextInterp-map-id {Γ} (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) ρ ρ' f {x , xs} = 
      let rec : Functor.F₁ (ContextInterp Δ) f x ≅ x
          rec = ContextInterp-map-id Δ ρ ρ' f {x}
      in Het-pair-cong (≡.sym (Δ-morph-const Δ ρ ρ' f)) (≡.sym (SetSem-morph-const ⊢F ρ ρ' f)) rec (SetSem-map-id ⊢F ρ ρ' f) 



    open import SetEnvironments.EnvironmentExtension using (extendfv-morph-vec)

    -- equality on objects
    Deq : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : SetEnv) (αs : Vec (FVar 0) k) (Xs : Vec Set k)
                → Functor.F₀ (ConstF {C = Sets^ k} {D = Sets} (Functor.F₀ (ContextInterp Δ) ρ)) Xs
                ≡ Functor.F₀ (D Δ ρ αs) Xs
    Deq Δ ρ αs Xs = Δ-eqTC-const Δ ρ ((NatEnv ρ) [ αs :fvs= to0Functors Xs ]Set) (extendfv-vec-preserves-tc (NatEnv ρ) αs (to0Functors Xs))

    -- D map is het identity 
    Dmap-id : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : SetEnv) (αs : Vec (FVar 0) k) {Xs Ys : Vec Set k} 
                → (fs : VecMorph Xs Ys)
                → ∀ {x} 
                → Functor.F₁ (D Δ ρ αs) fs x ≅ x 
    Dmap-id Δ ρ αs {Xs} {Ys} fs {x} = ContextInterp-map-id Δ ((NatEnv ρ) [ αs :fvs= to0Functors Xs ]Set ) ( ((NatEnv ρ) [ αs :fvs= to0Functors Ys ]Set ) ) (Functor.F₁ (extendSetEnv-αs αs (NatEnv ρ)) fs) 

    -- const map is het identity 
    Const-ρ-id : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : SetEnv) {Xs Ys : Vec Set k} 
                → (fs : VecMorph Xs Ys)
                → ∀ {x} 
                → Functor.F₁ (ConstF {C = Sets^ k} {D = Sets} (Functor.F₀ (ContextInterp Δ) ρ)) fs x ≅ x 
    Const-ρ-id Δ ρ {Xs} {Ys} fs {x} = _≅_.refl


    -- open import HetTest 
    module HetNat = HetNaturalIso-identity-maps


    DConst≃DExtend : ∀ {k} {Γ} → (Δ : TermCtx Γ ∅) (ρ : SetEnv) (αs : Vec (FVar 0) k) 
                → ConstF {C = Sets^ k} {D = Sets} (Functor.F₀ (ContextInterp Δ) ρ)
                ≃ D Δ ρ αs 
    DConst≃DExtend {k} {Γ} Δ ρ αs = HetNat.F≃G (Sets^ k)
                                      (ConstF {C = Sets^ k} {D = Sets} (Functor.F₀ (ContextInterp Δ) ρ))
                                      (D Δ ρ αs)
                                      (Deq Δ ρ αs) (Const-ρ-id Δ ρ) ( Dmap-id Δ ρ αs ) 

    ContextInterp-Forget-equiv : ∀ {Γ} → (Δ : TermCtx Γ ∅)
                    → (ρ : Category.Obj SetEnvCat)
                    → Functor.F₀ (ContextInterp Δ) ρ
                    ≡ Functor.F₀ (ContextInterp Δ ∘F ForgetFVSetEnv) ρ
    ContextInterp-Forget-equiv Δ ρ = Δ-morph-const Δ ρ (NatEnv ρ) (toNatEnv ρ) 


    ContextInterp-Forget-iso : ∀ {Γ} → (Δ : TermCtx Γ ∅) 
                              → ContextInterp Δ
                              ≃ ContextInterp Δ ∘F ForgetFVSetEnv
    ContextInterp-Forget-iso Δ = HetNat.F≃G SetEnvCat (ContextInterp Δ) (ContextInterp Δ ∘F ForgetFVSetEnv)
                   ( ContextInterp-Forget-equiv Δ )
                   (λ {ρ ρ'} f → ContextInterp-map-id Δ ρ ρ' f)
                   (λ {ρ ρ'} f → ContextInterp-map-id Δ (NatEnv ρ) (NatEnv ρ') (Functor.F₁ ForgetFVSetEnv f))


            


-- {-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}
-- --confluence-check #-}
open import Agda.Builtin.Equality.Rewrite




open import Categories.Category 
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
import Relation.Binary.PropositionalEquality as ≡ 
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open ≡.≡-Reasoning
open import Data.Product 

open import Syntax.NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
open import Utils using (exFalso ; cong-app-impl)
open import Categories.Object.Terminal

-------------------------------------------------------
-- Environments
-------------------------------------------------------




module RTEnvironments.Core {o l e : Level}
  {D : ℕ → Category o l e}
  {D⊤ : (k : ℕ) → Terminal (D k)}
  where 


DObj : ℕ → Set o 
DObj k = Category.Obj (D k) 

Did : ∀ (k : ℕ) → ∀ {d : DObj k} → (D k) [ d , d ]
Did k = Category.id (D k) 

-- type of Env.tc ρ (non-functorial part of environment)
EnvTC : Set _ 
EnvTC = ∀ {k : ℕ} → TCVar k → DObj k

EnvFV : Set _ 
EnvFV = ∀ {k : ℕ} → FVar  k → DObj k


record Env : Set (o ⊔ l ⊔ e) where
  constructor Env[_,_]
  eta-equality 
  field
    tc : EnvTC
    fv : EnvFV 


-- abstract 
-- environment that maps every variable to ConstF ⊤
-- -- the actual definition doesn't matter, so we can make it abstract 
-- -- -- just kidding, we need the definition for overness proofs of type semantics 
trivFVEnv : ∀ {k : ℕ} → FVar k → DObj k
-- just use initial object here 
trivFVEnv {k} _ = Terminal.⊤ (D⊤ k)

trivFVEnv-morph : ∀ {k} {φ ψ : FVar k} (fv : EnvFV)
                → (D k) [ (fv φ) ,  (trivFVEnv ψ) ]
trivFVEnv-morph {k} _ = Terminal.! (D⊤ k) 


extendfv : ∀ {k} → EnvFV → FVar k → DObj k
          → EnvFV
extendfv fv (φ ^F k) F {j} (ψ ^F j) with eqNat k j | φ ≟ ψ
... | yes ≡.refl | yes ≡.refl = F
{-# CATCHALL #-}
... | _    | _ = fv (ψ ^F j)


extendfv-lem : ∀ {k} → (fv : EnvFV) → (φ : FVar k) → (F : DObj k)
               → extendfv fv φ F φ ≡ F 
extendfv-lem fv (φ ^F k) F with eqNat k k | φ ≟ φ
... | yes ≡.refl | yes ≡.refl = ≡.refl 
... | yes ≡.refl | no φ≢φ  = exFalso (φ≢φ ≡.refl) 
... | no k≢k     | _ = exFalso (k≢k ≡.refl) 
-- NOTE doesn't pass confluence check... 
-- {-# REWRITE extendfv-lem #-}


extendfv-lem-≢ : ∀ {k} → (fv : EnvFV) 
               → (φ ψ : Id) → (F : DObj k)
               → φ ≢ ψ 
               → extendfv fv (φ ^F k) F (ψ ^F k) ≡ fv (ψ ^F k)
extendfv-lem-≢ {k} fv φ ψ F φ≢ψ with eqNat k k | φ ≟ ψ 
... | yes ≡.refl | yes φ≡ψ = exFalso (φ≢ψ φ≡ψ)
... | yes ≡.refl | no φ≢φ  = ≡.refl
... | no k≢k     | _       = ≡.refl



_[_:fv=_] : ∀ {k : ℕ} → Env → FVar k → DObj k → Env
ρ [ φ :fv= F ] = record { tc = Env.tc ρ ; fv = extendfv (Env.fv ρ) φ F } 

:fv=-cong : ∀ {k : ℕ} → (ρ ρ' : Env) → (φ : FVar k) → (F G : DObj k) 
            → ρ ≡ ρ'
            → F ≡ G 
            → ρ  [ φ :fv= F ] 
            ≡ ρ' [ φ :fv= G ] 
:fv=-cong ρ .ρ φ F .F ≡.refl ≡.refl = ≡.refl 


-- this version of recursive extension only extends the functorial part of the environment,
-- so it is easy to see the tc part is unchanged.
_[_:fvs=_] : ∀ {n k : ℕ} → Env → Vec (FVar k) n → Vec (DObj k) n → Env
ρ [ Vec.[] :fvs= Vec.[] ] = ρ
ρ [ φ  ∷ φs :fvs= F ∷ Fs ] = record { tc = Env.tc ρ ; fv = extendfv (Env.fv (ρ [ φs :fvs= Fs ])) φ F } 
-- outermost extension wil be _ [ φ1 := F1 ]


-- this version is functionally the same as :fvs= but operates on the entire environment. 
-- still, we can prove that the tc part is unchanged 
_[_:fvs='_] : ∀ {n k : ℕ} → Env → Vec (FVar k) n → Vec (DObj k) n → Env
ρ [ Vec.[] :fvs=' Vec.[] ] = ρ
ρ [ φ  ∷ φs :fvs=' F ∷ Fs ] = (ρ [ φ :fv= F ]) [ φs :fvs=' Fs ]
{-# WARNING_ON_USAGE _[_:fvs='_] "Use [_:fvs=_] instead" #-}

{-
fvs'eq : ∀ {n k : ℕ} → (ρ : Env) → (φs : Vec (FVar k) n) → (Fs : Vec (DObj k) n) 
        → ∀ {j} → Env.tc (ρ [ φs :fvs=' Fs ]) {j} ≡ Env.tc ρ {j}
fvs'eq ρ [] [] = ≡.refl
fvs'eq {suc n} {k} ρ (φ ∷ φs) (F ∷ Fs) = fvs'eq {n} {k} (ρ [ φ :fv= F ]) φs Fs 
{-# WARNING_ON_USAGE _[_:fvs='_] "Use [_:fvs=_] instead" #-}
-}


-- type of two set environments being equal on tc component 
-- since eta-expansion of implicit variables is annoying to reproduce everywhere 
_≡TC_ : ∀ (ρ ρ' : Env) → Set _
ρ ≡TC ρ' = (λ {k} → Env.tc ρ {k}) ≡  (λ {k} → Env.tc ρ' {k}) 

-- 'extensional equality, i.e., equal on a particular implicit arg 
_≡TC-ext[_]_ : Env → ℕ → Env → Set _
ρ ≡TC-ext[ k ] ρ' = (Env.tc ρ {k}) ≡  (Env.tc ρ' {k}) 

-- (intensional) equality implies extensional equality 
≡TC⇒≡TC-ext : ∀ {k} (ρ ρ' : Env) → ρ ≡TC ρ' → ρ ≡TC-ext[ k ] ρ'
≡TC⇒≡TC-ext ρ ρ' e = cong-app-impl e 


-- extending functorial part of environment preserves tc part
extendfv-preserves-tc : ∀ {k : ℕ} → (ρ : Env) → (φ : FVar k) → (F : DObj k)
                      → ρ ≡TC (ρ [ φ :fv= F ])
extendfv-preserves-tc ρ φ F = ≡.refl 
-- {-# REWRITE extendfv-preserves-tc #-}

extendfv-preserves-tc-ext : ∀ {k j : ℕ} → (ρ : Env) → (φ : FVar k) → (F : DObj k)
                      → ρ ≡TC-ext[ j ] (ρ [ φ :fv= F ])
extendfv-preserves-tc-ext ρ φ F = ≡.refl 

-- extending functorial part of environment with vector of φs/Fs preserves tc part
extendfv-vec-preserves-tc : ∀ {k n : ℕ} → (ρ : Env) → (φs : Vec (FVar k) n) → (Fs : Vec (DObj k) n)
                      → ρ ≡TC (ρ [ φs :fvs= Fs ])
extendfv-vec-preserves-tc ρ [] [] = ≡.refl
extendfv-vec-preserves-tc ρ (φ ∷ φs) (F ∷ Fs) = ≡.refl

extendfv-vec-preserves-tc-ext : ∀ {k n j : ℕ} → (ρ : Env) → (φs : Vec (FVar k) n) → (Fs : Vec (DObj k) n)
                      → ρ ≡TC-ext[ j ] (ρ [ φs :fvs= Fs ])
extendfv-vec-preserves-tc-ext ρ φs Fs = ≡TC⇒≡TC-ext ρ (ρ [ φs :fvs= Fs ]) (extendfv-vec-preserves-tc ρ φs Fs) 


record EnvMorph (ρ ρ' : Env) : Set (o ⊔ l ⊔ e) where
  constructor EnvM[_,_] 
  field
    -- need proof that ∀ {k : ℕ} {t : TCVar k} (ρ.tc t ≡ ρ'.tc t)
    -- -- but how do we know when two functors are equal?

    -- eqTC : ∀ {k : ℕ} → Env.tc ρ {k} ≡ Env.tc ρ' {k}
    -- eqTC : (λ {k} ψ → Env.tc ρ {k} ψ) ≡ (λ {k} ψ → Env.tc ρ' {k} ψ)
    -- -- use type synonym 
    eqTC : ρ ≡TC ρ'

    -- each type constructor variable is mapped to the identity
    -- natural transformation
    -- tc : ∀ {k : ℕ} {φ : TCVar k} → Functor (C)
    fv : ∀ {k : ℕ} → (φ : FVar  k) → (D k) [ (Env.fv ρ φ) , (Env.fv ρ' φ) ]

eqTC-expl : ∀ {k} {ρ ρ'} → (f : EnvMorph ρ ρ') → (Env.tc ρ {k}) ≡ (Env.tc ρ' {k})
eqTC-expl f = cong-app-impl (EnvMorph.eqTC f) 

eqTC-expl-nonmorph : ∀ {k} {ρ ρ'} → (eqTC : ρ ≡TC ρ') → (Env.tc ρ {k}) ≡ (Env.tc ρ' {k})
eqTC-expl-nonmorph eqTC = cong-app-impl eqTC 


-- just expanding the property that ρ, ρ' are equal (not just extensionally)
-- to derive extensional equality .
-- since functors are equal, we can derive identity natural transformation
eqTC-ext : ∀ {k} → {ρ ρ' : Env} 
                    → (f : EnvMorph ρ ρ') 
                    → (ψ : TCVar k)
                    → Env.tc ρ {k} ψ ≡ Env.tc ρ' {k} ψ
eqTC-ext {k} {ρ} {ρ'} record { eqTC = eqTC ; fv = fv } ψ = ≡.cong-app (cong-app-impl eqTC) ψ
-- ≡.cong-app eqTC ψ


_∘Env_ : ∀ {ρ ρ' ρ''} → EnvMorph ρ' ρ'' → EnvMorph ρ ρ' → EnvMorph ρ ρ''
g ∘Env f = record { eqTC = ≡.trans (EnvMorph.eqTC f) (EnvMorph.eqTC g)
                  ; fv   = λ {k} φ → (D k) [ (EnvMorph.fv g φ) ∘ (EnvMorph.fv f φ) ]  }



-- g φ : NaturalTransformation (ρ' φ) (ρ'' φ)
-- f φ : NaturalTransformation (ρ  φ) (ρ'  φ)
-- 
-- (g ∘ f) φ : NaturalTransformation (ρ φ) (ρ'' φ)

-- EnvMorph.fv acts as a functor (preserves composition), by definition of ∘Env 
∘Env-homomorphism : ∀ {ρ ρ' ρ''} → (g : EnvMorph ρ' ρ'') → (f : EnvMorph ρ ρ')
               → ∀ {k} (φ : FVar k)
               → (D k) [ EnvMorph.fv (g ∘Env f) φ
                    ≈ (D k) [ EnvMorph.fv g φ ∘ EnvMorph.fv f φ ]
               ] 
∘Env-homomorphism g f {k} φ = Category.Equiv.refl (D k) 


-- identity morphism for set environments
idEnv : ∀ {ρ : Env} → EnvMorph ρ ρ
idEnv = record { eqTC = ≡.refl ; fv = λ {k} _ → Did k } 

EnvCat : Category _ _ _ 
EnvCat = record
    { Obj = Env
    ; _⇒_ = EnvMorph
    -- do we need to reason about equality of EnvMorph?
    -- ; _≈_ = λ f g → {! ∀ {k : ℕ} {φ : FVar k} → EnvMorph.fv f φ ≈ EnvMorph.fv g φ  !}
    ; _≈_ = λ f g →  ∀ {k : ℕ} {φ : FVar k}  -- pointwise equal on natural transformations..
                → Category._≈_ (D k) (EnvMorph.fv f φ) (EnvMorph.fv g φ)
    ; id = idEnv
    ; _∘_ = _∘Env_
    ; assoc =  λ {A} {B} {C₁} {D₁} {f} {g} {h} {k} {φ} → Category.assoc (D k)
    ; sym-assoc = λ {A} {B} {C₁} {D₁} {f} {g} {h} {k} {φ} → Category.sym-assoc (D k) 
    ; identityˡ = λ {A} {B} {f} {k} {φ} → Category.identityˡ (D k) 
    ; identityʳ = λ {A} {B} {f} {k} {φ} → Category.identityʳ (D k) 
    ; identity² = λ {A} {k} {φ} → Category.identity² (D k) 
    ; equiv = record { refl = λ {x} {k} {φ} → Category.Equiv.refl (D k)
                     ; sym = λ p {k} {φ} → Category.Equiv.sym (D k) p
                     ; trans = λ p p' {k} → Category.Equiv.trans (D k) p p' } 
    ; ∘-resp-≈ = λ f≈h g≈i {k} → Category.∘-resp-≈ (D k) f≈h g≈i 
    }



mkIdMorph : ∀ {k} → (d d' : DObj k) → d ≡ d' → (D k) [ d , d' ]
mkIdMorph {k} d .d ≡.refl = Did k

-- given ρ ρ' with f : ρ → ρ',
-- derive identity natural transformation for a given TCVar 
-- 
-- used in functorial action of set interpretation of tc app
mkIdTCNT : ∀ {k} {ρ ρ' : Env}
           → (f : EnvMorph ρ ρ')
           → (ψ : TCVar k)
           → (D k) [ Env.tc ρ ψ ,  Env.tc ρ' ψ ] 
mkIdTCNT {k} {ρ} {ρ'} f ψ = mkIdMorph (Env.tc ρ ψ) (Env.tc ρ' ψ) (eqTC-ext f ψ) 

mkIdMorph-comp : ∀ {k} (F G H : DObj k)
                → (p : F ≡ H) → (q : F ≡ G) → (r : G ≡ H)
                → (D k) [ 
                    mkIdMorph F H p 
                    ≈ (D k) [ mkIdMorph G H r ∘ mkIdMorph F G q ]
                  ] 
mkIdMorph-comp {k} F .F .F ≡.refl ≡.refl ≡.refl = Category.Equiv.sym (D k) (Category.identity² (D k))

mkIdTCNT-comp : ∀ {k} {ρ1 ρ2 ρ3 : Env}
                → (f : EnvMorph ρ1 ρ2)
                → (g : EnvMorph ρ2 ρ3)
                → (φ : TCVar k)
                → (D k) [ 
                    mkIdTCNT (g ∘Env f) φ
                    ≈ (D k) [ mkIdTCNT g φ ∘ mkIdTCNT f φ ] 
                  ]
mkIdTCNT-comp {k} {ρ1} {ρ2} {ρ3} f g φ =
  mkIdMorph-comp (Env.tc ρ1 φ) (Env.tc ρ2 φ) (Env.tc ρ3 φ) 
                 (eqTC-ext (g ∘Env f) φ) (eqTC-ext f φ) (eqTC-ext g φ) 

mkIdMorph-eq : ∀ {k} → (F G : DObj k)
                → (p q : F ≡ G) 
                → (D k) [ mkIdMorph F G p ≈ mkIdMorph F G q ]
mkIdMorph-eq {k} F .F ≡.refl ≡.refl = Category.Equiv.refl (D k)

mkIdTCNT-eq : ∀ {k} {ρ ρ' : Env}
                → (f g : EnvMorph ρ ρ')
                → (φ : TCVar k)
                → (D k) [ mkIdTCNT f φ ≈ mkIdTCNT g φ ]
mkIdTCNT-eq {k} record { eqTC = ≡.refl ; fv = _ } record { eqTC = ≡.refl ; fv = _ } φ = Category.Equiv.refl (D k)




-- for each variable of arity k, we have a functor from category of environments
-- to category (D k) interpreting k-ary variables
--
-- D k will be either [Sets^ k ,Sets] or RTCat k 
ApplyEnv-FV : ∀ {k} (φ : FVar k) → Functor EnvCat (D k)
ApplyEnv-FV {k} φ = record
               { F₀ = λ ρ → Env.fv ρ φ
               ; F₁ = λ f → EnvMorph.fv f φ
               ; identity = Category.Equiv.refl (D k)
               ; homomorphism = Category.Equiv.refl (D k)
               ; F-resp-≈ = λ f≈g → f≈g {k} {φ}
               } 

-- we can do the same for TC variables 
ApplyEnv-TC : ∀ {k} (φ : TCVar k) → Functor EnvCat (D k)
ApplyEnv-TC {k} φ = record
               { F₀ = λ ρ → Env.tc ρ φ
               ; F₁ = λ f → mkIdTCNT f φ
               ; identity = Category.Equiv.refl (D k)
               ; homomorphism = λ {X} {Y} {Z} {f} {g} → mkIdTCNT-comp f g φ
               ; F-resp-≈ = λ {X} {Y} {f} {g} f≈g → mkIdTCNT-eq f g φ 
               } 



-- this is used in the interpretation of Nat types to 
-- ignore forget about the functorial part of the environment.
-- This makes it much easier to prove NatType F G ρ ≡ NatType F G ρ' 
-- when there is a morphism f : ρ → ρ'
NatEnv : Env → Env
NatEnv Env[ tc , fv ] = Env[ tc , trivFVEnv ]

toNatEnv : ∀ (ρ : Env) → EnvMorph ρ (NatEnv ρ)
toNatEnv ρ = record { eqTC = ≡.refl ; fv = λ ψ → trivFVEnv-morph {ψ = ψ} (Env.fv ρ) }


-- construct NatEnv from just the tc part of environment 
NatEnvTC : EnvTC → Env
NatEnvTC tc = Env[ tc , trivFVEnv ]

-- proof that NatEnv ρ ≡ NatEnv ρ' when there is a morphism ρ → ρ'
NatEnv-eq : {ρ ρ' : Env} → EnvMorph ρ ρ' → NatEnv ρ ≡ NatEnv ρ'
-- NatEnv-eq f rewrite (EnvMorph.eqTC f) = ≡.refl 
NatEnv-eq record { eqTC = ≡.refl ; fv = _ } = ≡.refl

ForgetFVEnv : Functor EnvCat EnvCat 
ForgetFVEnv = record
  { F₀ = λ ρ → NatEnv ρ 
  ; F₁ = λ f → record { eqTC = EnvMorph.eqTC f ; fv = λ {k} _ → Did k }
  ; identity = λ {ρ} {k} {φ} → Category.Equiv.refl  (D k)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} {k} {φ} → Category.Equiv.sym (D k) (Category.identity² (D k))
  ; F-resp-≈ = λ _ → λ {k} {φ} → Category.Equiv.refl (D k)
  } 


-- two environments are extensionally equal (on all functorial variables) 
_≡FV-ext_ : ∀ (ρ ρ' : Env) → Set o
ρ ≡FV-ext ρ' = ∀ {j : ℕ} (φ : FVar j) → (Env.fv ρ φ) ≡ (Env.fv ρ' φ)

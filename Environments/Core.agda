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
open import Relation.Binary.PropositionalEquality as ≡ 
open ≡.≡-Reasoning
open import Data.Product 

open import NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
open import RelCats
open import SetCats
open import Utils using (exFalso ; cong-app-impl)
open import Categories.Object.Terminal

-------------------------------------------------------
-- Environments
-------------------------------------------------------


module Environments.Core {o l e : Level} (C : Category o l e) (C⊤ : Terminal C)  where 

open VecCat C

private module C = Category C 

[C^_,C] : ℕ → Category _ _ _
[C^ k ,C] = [[ C^ k , C ]]


-- type of GenEnv.tc ρ (non-functorial part of environment)
GenEnvTC : Set _ 
GenEnvTC = ∀ {k : ℕ} → TCVar k → Functor (C^ k) C

GenEnvFV : Set _ 
GenEnvFV = ∀ {k : ℕ} → FVar  k → Functor (C^ k) C


record GenEnv : Set (o ⊔ l ⊔ e) where
  constructor Env[_,_]
  field
    tc : GenEnvTC
    fv : GenEnvFV 


abstract 
  -- environment that maps every variable to ConstF ⊤
  -- -- the actual definition doesn't matter, so we can make it abstract 
  trivFVEnv : ∀ {k : ℕ} → FVar k → Functor (C^ k) C
  -- just use initial object here 
  trivFVEnv {_} _ = ConstF (Terminal.⊤ C⊤)

  trivFVEnv-morph : ∀ {k} {φ ψ : FVar k} (fv : GenEnvFV)
                    → NaturalTransformation (fv φ) (trivFVEnv ψ)
  trivFVEnv-morph _ = ntHelper (record { η = λ Xs → IsTerminal.! (Terminal.⊤-is-terminal C⊤) ; commute = λ f → IsTerminal.!-unique₂ (Terminal.⊤-is-terminal C⊤)  }) 


extendfv : ∀ {k} → (∀ {j : ℕ} → FVar j → Functor (C^ j ) (C))
          → FVar k → Functor (C^ k ) (C)
          → (∀ {j : ℕ} → FVar j → Functor (C^ j ) (C))
extendfv fv (φ ^F k) F {j} (ψ ^F j) with eqNat k j | φ ≟ ψ
... | yes ≡.refl | yes ≡.refl = F
{-# CATCHALL #-}
... | _    | _ = fv (ψ ^F j)


extendfv-lem : ∀ {k} → (fv : ∀ {j : ℕ} → FVar j → Functor (C^ j ) (C))
               → (φ : FVar k) → (F : Functor (C^ k ) (C))
               → extendfv fv φ F φ ≡ F 
extendfv-lem fv (φ ^F k) F with eqNat k k | φ ≟ φ
... | yes ≡.refl | yes ≡.refl = ≡.refl 
... | yes ≡.refl | no φ≢φ  = exFalso (φ≢φ ≡.refl) 
... | no k≢k     | _ = exFalso (k≢k ≡.refl) 
-- NOTE doesn't pass confluence check... 
-- {-# REWRITE extendfv-lem #-}


extendfv-lem-≢ : ∀ {k} → (fv : ∀ {j : ℕ} → FVar j → Functor (C^ j ) (C))
               → (φ ψ : Id) → (F : Functor (C^ k ) (C))
               → φ ≢ ψ 
               → extendfv fv (φ ^F k) F (ψ ^F k) ≡ fv (ψ ^F k)
extendfv-lem-≢ {k} fv φ ψ F φ≢ψ with eqNat k k | φ ≟ ψ 
... | yes ≡.refl | yes φ≡ψ = exFalso (φ≢ψ φ≡ψ)
... | yes ≡.refl | no φ≢φ  = ≡.refl
... | no k≢k     | _       = ≡.refl



_[_:fv=_] : ∀ {k : ℕ} → GenEnv → FVar k → Functor (C^ k) C → GenEnv
ρ [ φ :fv= F ] = record { tc = GenEnv.tc ρ ; fv = extendfv (GenEnv.fv ρ) φ F } 

:fv=-cong : ∀ {k : ℕ} → (ρ ρ' : GenEnv) → (φ : FVar k) → (F G : Functor (C^ k) C) 
            → ρ ≡ ρ'
            → F ≡ G 
            → ρ  [ φ :fv= F ] 
            ≡ ρ' [ φ :fv= G ] 
:fv=-cong ρ .ρ φ F .F refl refl = refl 


-- this version of recursive extension only extends the functorial part of the environment,
-- so it is easy to see the tc part is unchanged.
_[_:fvs=_] : ∀ {n k : ℕ} → GenEnv → Vec (FVar k) n → Vec (Functor (C^ k ) (C)) n → GenEnv
ρ [ Vec.[] :fvs= Vec.[] ] = ρ
ρ [ φ  ∷ φs :fvs= F ∷ Fs ] = record { tc = GenEnv.tc ρ ; fv = extendfv (GenEnv.fv (ρ [ φs :fvs= Fs ])) φ F } 
-- outermost extension wil be _ [ φ1 := F1 ]


-- this version is functionally the same as :fvs= but operates on the entire environment. 
-- still, we can prove that the tc part is unchanged 
_[_:fvs='_] : ∀ {n k : ℕ} → GenEnv → Vec (FVar k) n → Vec (Functor (C^ k ) (C)) n → GenEnv
ρ [ Vec.[] :fvs=' Vec.[] ] = ρ
ρ [ φ  ∷ φs :fvs=' F ∷ Fs ] = (ρ [ φ :fv= F ]) [ φs :fvs=' Fs ]
{-# WARNING_ON_USAGE _[_:fvs='_] "Use [_:fvs=_] instead" #-}

{-
fvs'eq : ∀ {n k : ℕ} → (ρ : GenEnv) → (φs : Vec (FVar k) n) → (Fs : Vec (Functor (C^ k ) (C)) n) 
        → ∀ {j} → GenEnv.tc (ρ [ φs :fvs=' Fs ]) {j} ≡ GenEnv.tc ρ {j}
fvs'eq ρ [] [] = ≡.refl
fvs'eq {suc n} {k} ρ (φ ∷ φs) (F ∷ Fs) = fvs'eq {n} {k} (ρ [ φ :fv= F ]) φs Fs 
{-# WARNING_ON_USAGE _[_:fvs='_] "Use [_:fvs=_] instead" #-}
-}


-- type of two set environments being equal on tc component 
-- since eta-expansion of implicit variables is annoying to reproduce everywhere 
_≡TC_ : ∀ (ρ ρ' : GenEnv) → Set _
ρ ≡TC ρ' = (λ {k} → GenEnv.tc ρ {k}) ≡  (λ {k} → GenEnv.tc ρ' {k}) 

-- 'extensional' equality, i.e., equal on a particular implicit arg 
_≡TC-ext[_]_ : GenEnv → ℕ → GenEnv → Set _
ρ ≡TC-ext[ k ] ρ' = (GenEnv.tc ρ {k}) ≡  (GenEnv.tc ρ' {k}) 

-- (intensional) equality implies extensional equality 
≡TC⇒≡TC-ext : ∀ {k} (ρ ρ' : GenEnv) → ρ ≡TC ρ' → ρ ≡TC-ext[ k ] ρ'
≡TC⇒≡TC-ext ρ ρ' e = cong-app-impl e 


-- extending functorial part of environment preserves tc part
extendfv-preserves-tc : ∀ {k : ℕ} → (ρ : GenEnv) → (φ : FVar k) → (F : Functor (C^ k) C)
                      → ρ ≡TC (ρ [ φ :fv= F ])
extendfv-preserves-tc ρ φ F = refl 
-- {-# REWRITE extendfv-preserves-tc #-}

extendfv-preserves-tc-ext : ∀ {k j : ℕ} → (ρ : GenEnv) → (φ : FVar k) → (F : Functor (C^ k) C)
                      → ρ ≡TC-ext[ j ] (ρ [ φ :fv= F ])
extendfv-preserves-tc-ext ρ φ F = refl 

-- extending functorial part of environment with vector of φs/Fs preserves tc part
extendfv-vec-preserves-tc : ∀ {k n : ℕ} → (ρ : GenEnv) → (φs : Vec (FVar k) n) → (Fs : Vec (Functor (C^ k) C) n)
                      → ρ ≡TC (ρ [ φs :fvs= Fs ])
extendfv-vec-preserves-tc ρ [] [] = refl
extendfv-vec-preserves-tc ρ (φ ∷ φs) (F ∷ Fs) = refl

extendfv-vec-preserves-tc-ext : ∀ {k n j : ℕ} → (ρ : GenEnv) → (φs : Vec (FVar k) n) → (Fs : Vec (Functor (C^ k) C) n)
                      → ρ ≡TC-ext[ j ] (ρ [ φs :fvs= Fs ])
extendfv-vec-preserves-tc-ext ρ φs Fs = ≡TC⇒≡TC-ext ρ (ρ [ φs :fvs= Fs ]) (extendfv-vec-preserves-tc ρ φs Fs) 


record GenEnvMorph (ρ ρ' : GenEnv) : Set (o ⊔ l ⊔ e) where
  field
    -- need proof that ∀ {k : ℕ} {t : TCVar k} (ρ.tc t ≡ ρ'.tc t)
    -- -- but how do we know when two functors are equal?

    -- eqTC : ∀ {k : ℕ} → GenEnv.tc ρ {k} ≡ GenEnv.tc ρ' {k}
    -- eqTC : (λ {k} ψ → GenEnv.tc ρ {k} ψ) ≡ (λ {k} ψ → GenEnv.tc ρ' {k} ψ)
    -- -- use type synonym 
    eqTC : ρ ≡TC ρ'

    -- each type constructor variable is mapped to the identity
    -- natural transformation
    -- tc : ∀ {k : ℕ} {φ : TCVar k} → Functor (C)
    fv : ∀ {k : ℕ} → (φ : FVar  k) → NaturalTransformation (GenEnv.fv ρ φ) (GenEnv.fv ρ' φ)

eqTC-expl : ∀ {k} {ρ ρ'} → (f : GenEnvMorph ρ ρ') → (GenEnv.tc ρ {k}) ≡ (GenEnv.tc ρ' {k})
eqTC-expl f = cong-app-impl (GenEnvMorph.eqTC f) 

eqTC-expl-nonmorph : ∀ {k} {ρ ρ'} → (eqTC : ρ ≡TC ρ') → (GenEnv.tc ρ {k}) ≡ (GenEnv.tc ρ' {k})
eqTC-expl-nonmorph eqTC = cong-app-impl eqTC 


-- just expanding the property that ρ, ρ' are equal (not just extensionally)
-- to derive extensional equality .
-- since functors are equal, we can derive identity natural transformation
eqTC-ext : ∀ {k} → {ρ ρ' : GenEnv} 
                    → (f : GenEnvMorph ρ ρ') 
                    → (ψ : TCVar k)
                    → GenEnv.tc ρ {k} ψ ≡ GenEnv.tc ρ' {k} ψ
eqTC-ext {k} {ρ} {ρ'} record { eqTC = eqTC ; fv = fv } ψ = ≡.cong-app (cong-app-impl eqTC) ψ
-- ≡.cong-app eqTC ψ


_∘GenEnv_ : ∀ {ρ ρ' ρ''} → GenEnvMorph ρ' ρ'' → GenEnvMorph ρ ρ' → GenEnvMorph ρ ρ''
g ∘GenEnv f = record { eqTC = ≡.trans (GenEnvMorph.eqTC f) (GenEnvMorph.eqTC g)
                           ; fv   = λ {k} φ → (GenEnvMorph.fv g φ) ∘v (GenEnvMorph.fv f φ) }


-- identity morphism for set environments
idGenEnv : ∀ {ρ : GenEnv} → GenEnvMorph ρ ρ
idGenEnv = record { eqTC = ≡.refl ; fv = λ _ → idnat } 

GenEnvCat : Category _ _ _ 
GenEnvCat = record
    { Obj = GenEnv
    ; _⇒_ = GenEnvMorph
    -- do we need to reason about equality of GenEnvMorph?
    -- ; _≈_ = λ f g → {! ∀ {k : ℕ} {φ : FVar k} → GenEnvMorph.fv f φ ≈ GenEnvMorph.fv g φ  !}
    ; _≈_ = λ f g →  ∀ {k : ℕ} {φ : FVar k}  -- pointwise equal on natural transformations..
                → Category._≈_ ([C^ k ,C] ) (GenEnvMorph.fv f φ) (GenEnvMorph.fv g φ)
    ; id = idGenEnv
    ; _∘_ = _∘GenEnv_
    ; assoc =  C.assoc 
    ; sym-assoc = C.sym-assoc
    ; identityˡ = C.identityˡ 
    ; identityʳ = C.identityʳ
    ; identity² = C.identity²
    ; equiv = record { refl = C.Equiv.refl ; sym = λ p → C.Equiv.sym p ; trans = λ p r → C.Equiv.trans p r }
    ; ∘-resp-≈ = λ {ρ} {ρ'} {ρ''} {f} {h} {g} {i} f≈h g≈i {k} {φ} → Category.∘-resp-≈ [C^ k ,C] {f = GenEnvMorph.fv f φ} {GenEnvMorph.fv h φ} {GenEnvMorph.fv g φ} {GenEnvMorph.fv i φ} f≈h g≈i 
    }


-- given ρ ρ' with f : ρ → ρ',
-- derive identity natural transformation for a given TCVar 
-- 
-- used in functorial action of set interpretation of tc app
mkIdTCNT : ∀ {k} {ρ ρ' : GenEnv}
           → (f : GenEnvMorph ρ ρ')
           → (ψ : TCVar k)
           → NaturalTransformation (GenEnv.tc ρ ψ) (GenEnv.tc ρ' ψ)
mkIdTCNT {k} {ρ} {ρ'} f ψ = mkIdNatTr (GenEnv.tc ρ ψ) (GenEnv.tc ρ' ψ) (eqTC-ext f ψ) 

mkIdNatTr-comp : ∀ {k} → (F G H : Functor (C^ k) C)
                → (p : F ≡ H) → (q : F ≡ G) → (r : G ≡ H)
                → [C^ k ,C] Categories.Category.[ 
                  mkIdNatTr F H p 
                  ≈ mkIdNatTr G H r ∘v mkIdNatTr F G q ]
mkIdNatTr-comp F .F .F ≡.refl ≡.refl ≡.refl =  C.Equiv.sym C.identity²

mkIdTCNT-comp : ∀ {k} {ρ1 ρ2 ρ3 : GenEnv}
                → (f : GenEnvMorph ρ1 ρ2)
                → (g : GenEnvMorph ρ2 ρ3)
                → (φ : TCVar k)
                → [C^ k ,C] Categories.Category.[ 
                  mkIdTCNT (g ∘GenEnv f) φ
                  ≈ mkIdTCNT g φ ∘v mkIdTCNT f φ ]
mkIdTCNT-comp {k} {ρ1} {ρ2} {ρ3} f g φ =
  mkIdNatTr-comp (GenEnv.tc ρ1 φ) (GenEnv.tc ρ2 φ) (GenEnv.tc ρ3 φ) 
                 (eqTC-ext (g ∘GenEnv f) φ) (eqTC-ext f φ) (eqTC-ext g φ) 

mkIdNatTr-eq : ∀ {k} → (F G : Functor (C^ k) C)
                → (p q : F ≡ G) 
                → [C^ k ,C] Categories.Category.[ 
                      mkIdNatTr F G p ≈ mkIdNatTr F G q ]
mkIdNatTr-eq F .F ≡.refl ≡.refl = C.Equiv.refl

mkIdTCNT-eq : ∀ {k} {ρ ρ' : GenEnv}
                → (f g : GenEnvMorph ρ ρ')
                → (φ : TCVar k)
                → [C^ k ,C] Categories.Category.[ 
                    mkIdTCNT f φ ≈ mkIdTCNT g φ ]
mkIdTCNT-eq {k} record { eqTC = refl ; fv = _ } record { eqTC = refl ; fv = _ } φ {Rs} = C.Equiv.refl



-- this is used in the interpretation of Nat types to 
-- ignore forget about the functorial part of the environment.
-- This makes it much easier to prove NatType F G ρ ≡ NatType F G ρ' 
-- when there is a morphism f : ρ → ρ'
NatEnv : GenEnv → GenEnv
NatEnv Env[ tc , fv ] = Env[ tc , trivFVEnv ]

toNatEnv : ∀ (ρ : GenEnv) → GenEnvMorph ρ (NatEnv ρ)
toNatEnv ρ = record { eqTC = refl ; fv = λ φ → trivFVEnv-morph (GenEnv.fv ρ) }


-- construct NatEnv from just the tc part of environment 
NatEnvTC : GenEnvTC → GenEnv
NatEnvTC tc = Env[ tc , trivFVEnv ]

-- proof that NatEnv ρ ≡ NatEnv ρ' when there is a morphism ρ → ρ'
NatEnv-eq : {ρ ρ' : GenEnv} → GenEnvMorph ρ ρ' → NatEnv ρ ≡ NatEnv ρ'
-- NatEnv-eq f rewrite (GenEnvMorph.eqTC f) = ≡.refl 
NatEnv-eq record { eqTC = refl ; fv = _ } = refl

ForgetFVEnv : Functor GenEnvCat GenEnvCat 
ForgetFVEnv = record
  { F₀ = λ ρ → NatEnv ρ 
  ; F₁ = λ f → record { eqTC = GenEnvMorph.eqTC f ; fv = λ _ → idnat  } 
  ; identity = λ {ρ} {k} {φ} {x} → C.Equiv.refl 
  ; homomorphism = λ {X} {Y} {Z} {f} {g} {k} {φ} {x} → C.Equiv.sym  C.identity²
  ; F-resp-≈ = λ _ → λ {k} {φ} {x} → C.Equiv.refl
  } 


-- {-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}
-- --confluence-check #-}
open import Agda.Builtin.Equality.Rewrite



module SetEnvironments-preRT.Core where 

open import Categories.Category using (Category)
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

open import Syntax.NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
open import SetCats using (Sets ; Sets^ ; [Sets^_,Sets] ; ConstF ; mkIdNatTr)
open import Utils using (exFalso ; cong-app-impl)

-------------------------------------------------------
-- Environments
-------------------------------------------------------


-- type of SetEnv.tc ρ (non-functorial part of environment)
SetEnvTC : Set₁  
SetEnvTC = ∀ {k : ℕ} → TCVar k → Functor (Sets^ k) Sets

SetEnvFV : Set₁  
SetEnvFV = ∀ {k : ℕ} → FVar  k → Functor (Sets^ k) Sets


record SetEnv : Set₁  where
  constructor SetEnv[_,_]
  field
    tc : ∀ {k : ℕ} → TCVar k → Functor (Sets^ k) Sets
    fv : ∀ {k : ℕ} → FVar  k → Functor (Sets^ k) Sets


abstract 
  -- environment that maps every variable to ConstF ⊤
  -- -- the actual definition doesn't matter, so we can make it abstract 
  trivFVEnv : ∀ {k : ℕ} → FVar k → Functor (Sets^ k) Sets
  trivFVEnv {_} _ = ConstF ⊤

  trivFVEnv-morph : ∀ {k} {φ ψ : FVar k} (fv : SetEnvFV)
                    → NaturalTransformation (fv φ) (trivFVEnv ψ)
  trivFVEnv-morph _ = record { η = λ X x → Data.Unit.tt ; commute = λ f → refl ; sym-commute = λ f → refl } 

-- extendtc : ∀ {k} → (∀ {j : ℕ} → TCVar j → Functor (Sets^ j ) (Sets ))
--           → TCVar k → Functor (Sets^ k ) (Sets )
--           → (∀ {j : ℕ} → TCVar j → Functor (Sets^ j ) (Sets ))
-- extendtc t (φ ^T k) F {j} (ψ ^T j) with eqNat k j | φ ≟ ψ
-- ... | yes ≡.refl | yes ≡.refl = F
-- ... | _    | _ = t (ψ ^T j)
-- -- ... | _    | no _ = t (ψ ^T j)
-- -- ... | no _ | _    = t (ψ ^T j)

-- ENVIRONMENT EXTENSION
-- 
-- don't really need tc extension right? 
-- _[_:tc=_] : ∀ {n k : ℕ} → SetEnv → Vec (TCVar k) n → Vec (Functor (Sets^ k ) (Sets )) n → SetEnv
-- ρ [ Vec.[] :tc= Vec.[] ] = ρ
-- record { tc = tc ; fv = fv } [ (φ ^T k) ∷ φs :tc= F ∷ Fs ] = (record { tc = extendtc tc (φ ^T k) F ; fv = fv }) [ φs :tc= Fs ]


extendfv : ∀ {k} → (∀ {j : ℕ} → FVar j → Functor (Sets^ j ) (Sets ))
          → FVar k → Functor (Sets^ k ) (Sets )
          → (∀ {j : ℕ} → FVar j → Functor (Sets^ j ) (Sets ))
extendfv fv (φ ^F k) F {j} (ψ ^F j) with eqNat k j | φ ≟ ψ
... | yes ≡.refl | yes ≡.refl = F
... | _    | _ = fv (ψ ^F j)


extendfv-lem : ∀ {k} → (fv : ∀ {j : ℕ} → FVar j → Functor (Sets^ j ) (Sets ))
               → (φ : FVar k) → (F : Functor (Sets^ k ) (Sets ))
               → extendfv fv φ F φ ≡ F 
extendfv-lem fv (φ ^F k) F with eqNat k k | φ ≟ φ
... | yes ≡.refl | yes ≡.refl = ≡.refl 
... | yes ≡.refl | no φ≢φ  = exFalso (φ≢φ ≡.refl) 
... | no k≢k     | _ = exFalso (k≢k ≡.refl) 
-- NOTE doesn't pass confluence check... 
-- {-# REWRITE extendfv-lem #-}


extendfv-lem-≢ : ∀ {k} → (fv : ∀ {j : ℕ} → FVar j → Functor (Sets^ j ) (Sets ))
               → (φ ψ : Id) → (F : Functor (Sets^ k ) (Sets ))
               → φ ≢ ψ 
               → extendfv fv (φ ^F k) F (ψ ^F k) ≡ fv (ψ ^F k)
extendfv-lem-≢ {k} fv φ ψ F φ≢ψ with eqNat k k | φ ≟ ψ 
... | yes ≡.refl | yes φ≡ψ = exFalso (φ≢ψ φ≡ψ)
... | yes ≡.refl | no φ≢φ  = ≡.refl
... | no k≢k     | _       = ≡.refl



_[_:fv=_] : ∀ {k : ℕ} → SetEnv → FVar k → Functor (Sets^ k) Sets → SetEnv
ρ [ φ :fv= F ] = record { tc = SetEnv.tc ρ ; fv = extendfv (SetEnv.fv ρ) φ F } 

:fv=-cong : ∀ {k : ℕ} → (ρ ρ' : SetEnv) → (φ : FVar k) → (F G : Functor (Sets^ k) Sets) 
            → ρ ≡ ρ'
            → F ≡ G 
            → ρ  [ φ :fv= F ] 
            ≡ ρ' [ φ :fv= G ] 
:fv=-cong ρ .ρ φ F .F refl refl = refl 

-- this version of recursive extension only extends the functorial part of the environment,
-- so it is easy to see the tc part is unchanged.
_[_:fvs=_] : ∀ {n k : ℕ} → SetEnv → Vec (FVar k) n → Vec (Functor (Sets^ k ) (Sets )) n → SetEnv
ρ [ Vec.[] :fvs= Vec.[] ] = ρ
ρ [ φ  ∷ φs :fvs= F ∷ Fs ] = record { tc = SetEnv.tc ρ ; fv = extendfv (SetEnv.fv (ρ [ φs :fvs= Fs ])) φ F } 
-- outermost extension wil be _ [ φ1 := F1 ]


-- this version is functionally the same as :fvs= but operates on the entire environment. 
-- still, we can prove that the tc part is unchanged 
_[_:fvs=_]' : ∀ {n k : ℕ} → SetEnv → Vec (FVar k) n → Vec (Functor (Sets^ k ) (Sets )) n → SetEnv
ρ [ Vec.[] :fvs= Vec.[] ]' = ρ
ρ [ φ  ∷ φs :fvs= F ∷ Fs ]' = (ρ [ φ :fv= F ]) [ φs :fvs= Fs ]'
{-# WARNING_ON_USAGE _[_:fvs=_]' "Use [_:fvs=_] instead" #-}

{-
fvs'eq : ∀ {n k : ℕ} → (ρ : SetEnv) → (φs : Vec (FVar k) n) → (Fs : Vec (Functor (Sets^ k ) (Sets )) n) 
        → ∀ {j} → SetEnv.tc (ρ [ φs :fvs=' Fs ]) {j} ≡ SetEnv.tc ρ {j}
fvs'eq ρ [] [] = ≡.refl
fvs'eq {suc n} {k} ρ (φ ∷ φs) (F ∷ Fs) = fvs'eq {n} {k} (ρ [ φ :fv= F ]) φs Fs 
{-# WARNING_ON_USAGE _[_:fvs='_] "Use [_:fvs=_] instead" #-}
-}


-- type of two set environments being equal on tc component 
-- since eta-expansion of implicit variables is annoying to reproduce everywhere 
_≡TC_ : ∀ (ρ ρ' : SetEnv) → Set₁
ρ ≡TC ρ' = (λ {k} → SetEnv.tc ρ {k}) ≡  (λ {k} → SetEnv.tc ρ' {k}) 

-- 'extensional' equality, i.e., equal on a particular implicit arg 
_≡TC-ext[_]_ : SetEnv → ℕ → SetEnv → Set₁
ρ ≡TC-ext[ k ] ρ' = (SetEnv.tc ρ {k}) ≡  (SetEnv.tc ρ' {k}) 

-- (intensional) equality implies extensional equality 
≡TC⇒≡TC-ext : ∀ {k} (ρ ρ' : SetEnv) → ρ ≡TC ρ' → ρ ≡TC-ext[ k ] ρ'
≡TC⇒≡TC-ext ρ ρ' e = cong-app-impl e 


-- extending functorial part of environment preserves tc part
extendfv-preserves-tc : ∀ {k : ℕ} → (ρ : SetEnv) → (φ : FVar k) → (F : Functor (Sets^ k) Sets)
                      → ρ ≡TC (ρ [ φ :fv= F ])
extendfv-preserves-tc ρ φ F = refl 
-- {-# REWRITE extendfv-preserves-tc #-}

extendfv-preserves-tc-ext : ∀ {k j : ℕ} → (ρ : SetEnv) → (φ : FVar k) → (F : Functor (Sets^ k) Sets)
                      → ρ ≡TC-ext[ j ] (ρ [ φ :fv= F ])
extendfv-preserves-tc-ext ρ φ F = refl 

-- extending functorial part of environment with vector of φs/Fs preserves tc part
extendfv-vec-preserves-tc : ∀ {k n : ℕ} → (ρ : SetEnv) → (φs : Vec (FVar k) n) → (Fs : Vec (Functor (Sets^ k) Sets) n)
                      → ρ ≡TC (ρ [ φs :fvs= Fs ])
extendfv-vec-preserves-tc ρ [] [] = refl
extendfv-vec-preserves-tc ρ (φ ∷ φs) (F ∷ Fs) = refl

extendfv-vec-preserves-tc-ext : ∀ {k n j : ℕ} → (ρ : SetEnv) → (φs : Vec (FVar k) n) → (Fs : Vec (Functor (Sets^ k) Sets) n)
                      → ρ ≡TC-ext[ j ] (ρ [ φs :fvs= Fs ])
extendfv-vec-preserves-tc-ext ρ φs Fs = ≡TC⇒≡TC-ext ρ (ρ [ φs :fvs= Fs ]) (extendfv-vec-preserves-tc ρ φs Fs) 


record SetEnvMorph (ρ ρ' : SetEnv) : Set₁ where
  constructor SetEnvM[_,_]
  field
    eqTC : (λ {k} → SetEnv.tc ρ {k}) ≡ (λ {k} → SetEnv.tc ρ' {k})
    fv : ∀ {k : ℕ} → (φ : FVar  k)
         → NaturalTransformation (SetEnv.fv ρ φ) (SetEnv.fv ρ' φ)

-- get Set mapping (object) part of each variable in a Set environment
tcobj :  SetEnv → {k : ℕ} → TCVar k → (Vec Set k) → Set
tcobj ρ = Functor.F₀ ∘' SetEnv.tc ρ 

fvobj :  SetEnv → {k : ℕ} → FVar k → (Vec Set k) → Set
fvobj ρ = Functor.F₀ ∘' SetEnv.fv ρ 

eqTC-expl : ∀ {k} {ρ ρ'} → (f : SetEnvMorph ρ ρ') → (SetEnv.tc ρ {k}) ≡ (SetEnv.tc ρ' {k})
eqTC-expl f = cong-app-impl (SetEnvMorph.eqTC f) 

eqTC-expl-nonmorph : ∀ {k} {ρ ρ'} → (eqTC : ρ ≡TC ρ') → (SetEnv.tc ρ {k}) ≡ (SetEnv.tc ρ' {k})
eqTC-expl-nonmorph eqTC = cong-app-impl eqTC 


-- just expanding the property that ρ, ρ' are equal (not just extensionally)
-- to derive extensional equality .
-- since functors are equal, we can derive identity natural transformation
eqTC-ext : ∀ {k} → {ρ ρ' : SetEnv} 
                    → (f : SetEnvMorph ρ ρ') 
                    → (ψ : TCVar k)
                    → SetEnv.tc ρ {k} ψ ≡ SetEnv.tc ρ' {k} ψ
eqTC-ext {k} {ρ} {ρ'} record { eqTC = eqTC ; fv = fv } ψ = ≡.cong-app (cong-app-impl eqTC) ψ
-- ≡.cong-app eqTC ψ


_∘SetEnv_ : ∀ {ρ ρ' ρ''} → SetEnvMorph ρ' ρ'' → SetEnvMorph ρ ρ' → SetEnvMorph ρ ρ''
g ∘SetEnv f = record { eqTC = ≡.trans (SetEnvMorph.eqTC f) (SetEnvMorph.eqTC g)
                     ; fv   = λ {k} φ → (SetEnvMorph.fv g φ) ∘v (SetEnvMorph.fv f φ) }

-- identity morphism for set environments
idSetEnv : ∀ {ρ : SetEnv} → SetEnvMorph ρ ρ
idSetEnv = record { eqTC = ≡.refl ; fv = λ _ → idnat }

SetEnvCat : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
SetEnvCat = record
    { Obj = SetEnv
    ; _⇒_ = SetEnvMorph
    ; _≈_ = λ f g →  ∀ {k : ℕ} {φ : FVar k}  -- pointwise equal on natural transformations..
                → Category._≈_ ([Sets^ k ,Sets]) (SetEnvMorph.fv f φ) (SetEnvMorph.fv g φ)
    ; id = idSetEnv
    ; _∘_ = _∘SetEnv_
    ; assoc = ≡.refl
    ; sym-assoc = ≡.refl 
    ; identityˡ = ≡.refl 
    ; identityʳ = ≡.refl 
    ; identity² = ≡.refl 
    ; equiv = record { refl = λ {Xs} → ≡.refl ; sym = λ f≡g {Xs} → ≡.sym (f≡g {Xs})
                     ; trans = λ g≡h f≡g {Xs} → ≡.trans (g≡h {Xs}) (f≡g {Xs}) }
    -- ; ∘-resp-≈ = λ  {ρ} {ρ'} {ρ''} f≡h g≡i {k} Xs {ρφXs} → ∘-resp-≈ (λ {x} → f≡h Xs {x}) (λ {x} → g≡i Xs {x})
    ; ∘-resp-≈ = λ  {ρ} {ρ'} {ρ''} {f} {h} {g} {i} f≡h g≡i {k} {ψ} {Xs} {x} → ∘-resp-≈  {f = NaturalTransformation.η (SetEnvMorph.fv f ψ) Xs} {h = NaturalTransformation.η (SetEnvMorph.fv h ψ) Xs} {g = NaturalTransformation.η (SetEnvMorph.fv g ψ) Xs} {i = NaturalTransformation.η (SetEnvMorph.fv i ψ) Xs} 
                                                                                  (f≡h {k} {ψ} {Xs}) (g≡i {k} {ψ} {Xs})
    }
    where open Category (Sets ) using (∘-resp-≈)


-- module SEC = Category SetEnvCat
-- open SEC.HomReasoning hiding (step-≡) renaming (begin_ to begin≈_ ; _∎ to _≈∎)


-- given ρ ρ' with f : ρ → ρ',
-- derive identity natural transformation for a given TCVar 
-- 
-- used in functorial action of set interpretation of tc app
mkIdTCNT : ∀ {k} {ρ ρ' : SetEnv}
           → (f : SetEnvMorph ρ ρ')
           → (ψ : TCVar k)
           → NaturalTransformation (SetEnv.tc ρ ψ) (SetEnv.tc ρ' ψ)
mkIdTCNT {k} {ρ} {ρ'} f ψ = mkIdNatTr (SetEnv.tc ρ ψ) (SetEnv.tc ρ' ψ) (eqTC-ext f ψ) 

mkIdNatTr-comp : ∀ {k} → (F G H : Functor (Sets^ k) Sets)
                → (p : F ≡ H) → (q : F ≡ G) → (r : G ≡ H)
                → [Sets^ k ,Sets] Categories.Category.[ 
                  mkIdNatTr F H p 
                  ≈ mkIdNatTr G H r ∘v mkIdNatTr F G q ]
mkIdNatTr-comp F .F .F ≡.refl ≡.refl ≡.refl = ≡.refl 

mkIdTCNT-comp : ∀ {k} {ρ1 ρ2 ρ3 : SetEnv}
                → (f : SetEnvMorph ρ1 ρ2)
                → (g : SetEnvMorph ρ2 ρ3)
                → (φ : TCVar k)
                → [Sets^ k ,Sets] Categories.Category.[ 
                  mkIdTCNT (g ∘SetEnv f) φ
                  ≈ mkIdTCNT g φ ∘v mkIdTCNT f φ ]
mkIdTCNT-comp {k} {ρ1} {ρ2} {ρ3} f g φ =
  mkIdNatTr-comp (SetEnv.tc ρ1 φ) (SetEnv.tc ρ2 φ) (SetEnv.tc ρ3 φ) 
                 (eqTC-ext (g ∘SetEnv f) φ) (eqTC-ext f φ) (eqTC-ext g φ) 

mkIdNatTr-eq : ∀ {k} → (F G : Functor (Sets^ k) Sets)
                → (p q : F ≡ G) 
                → [Sets^ k ,Sets] Categories.Category.[ 
                      mkIdNatTr F G p ≈ mkIdNatTr F G q ]
mkIdNatTr-eq F .F ≡.refl ≡.refl = ≡.refl 

mkIdTCNT-eq : ∀ {k} {ρ ρ' : SetEnv}
                → (f g : SetEnvMorph ρ ρ')
                → (φ : TCVar k)
                → [Sets^ k ,Sets] Categories.Category.[ 
                    mkIdTCNT f φ ≈ mkIdTCNT g φ ]
mkIdTCNT-eq {k} {ρ} {ρ'} f g φ {Xs} {x} = mkIdNatTr-eq (SetEnv.tc ρ φ) (SetEnv.tc ρ' φ) (eqTC-ext f φ) (eqTC-ext g φ) 



-- this is used in the interpretation of Nat types to 
-- ignore forget about the functorial part of the environment.
-- This makes it much easier to prove NatType F G ρ ≡ NatType F G ρ' 
-- when there is a morphism f : ρ → ρ'
NatEnv : SetEnv → SetEnv
NatEnv SetEnv[ tc , fv ] = SetEnv[ tc , trivFVEnv ]

toNatEnv : ∀ (ρ : SetEnv) → SetEnvMorph ρ (NatEnv ρ)
toNatEnv ρ = record { eqTC = refl ; fv = λ φ → trivFVEnv-morph (SetEnv.fv ρ) }


-- construct NatEnv from just the tc part of environment 
NatEnvTC : SetEnvTC → SetEnv
NatEnvTC tc = SetEnv[ tc , trivFVEnv ]

-- proof that NatEnv ρ ≡ NatEnv ρ' when there is a morphism ρ → ρ'
NatEnv-eq : {ρ ρ' : SetEnv} → SetEnvMorph ρ ρ' → NatEnv ρ ≡ NatEnv ρ'
-- NatEnv-eq f rewrite (SetEnvMorph.eqTC f) = ≡.refl 
NatEnv-eq record { eqTC = refl ; fv = _ } = refl

ForgetFVEnv : Functor SetEnvCat SetEnvCat 
ForgetFVEnv = record
  { F₀ = λ ρ → NatEnv ρ 
  ; F₁ = λ f → record { eqTC = SetEnvMorph.eqTC f ; fv = λ _ → idnat  } 
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≈ = λ _ → ≡.refl
  } 



-- {-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting #-}
-- --confluence-check #-}



module SetEnvironments where 

open import Agda.Builtin.Equality.Rewrite


open import NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
-- open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (if_then_else_; true; false)

open import Categories.Category using (Category)


open import Categories.Category.Product using (Product ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_ ; assocʳ)
open import Categories.Category.Construction.Functors using (Functors; module curry ; evalF)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.Diagram.Colimit
-- open import Categories.Diagram.Cocone
-- open import Data.Nat using (ℕ)
-- open ℕ

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
-- open _≤_

open import Data.Fin using (Fin)

open import Data.List as List
open import Data.Unit using (⊤)
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Binary.PropositionalEquality as ≡ 
open ≡.≡-Reasoning
open import Data.Product hiding (assocʳ) renaming (_×_ to _×'_)
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_)
open import Data.Sum.Properties using (inj₂-injective)

open import SetCats

open import Utils



-------------------------------------------------------
-- Environments
-------------------------------------------------------


-- type of SetEnv.tc ρ (non-functorial part of environment)
SetEnvTC : Set₁  
SetEnvTC = ∀ {k : ℕ} → TCVar k → Functor (Sets^ k) Sets

SetEnvFV : Set₁  
SetEnvFV = ∀ {k : ℕ} → FVar  k → Functor (Sets^ k) Sets


record SetEnv : Set₁  where
  constructor Env[_,_]
  field
    tc : SetEnvTC
    fv : SetEnvFV 


abstract 
  -- environment that maps every variable to ConstF ⊤
  -- -- the actual definition doesn't matter, so we can make it abstract 
  trivFVEnv : ∀ {k : ℕ} → FVar k → Functor (Sets^ k) Sets
  trivFVEnv {_} _ = ConstF ⊤

  -- trivFVEnv-morph : ∀ {k} {φ ψ : FVar k} → NaturalTransformation (trivFVEnv φ) (trivFVEnv ψ)
  -- trivFVEnv-morph = record { η = λ X x → Data.Unit.tt ; commute = λ f → refl ; sym-commute = λ f → refl } 

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

-- this version of recursive extension only extends the functorial part of the environment,
-- so it is easy to see the tc part is unchanged.
_[_:fvs=_] : ∀ {n k : ℕ} → SetEnv → Vec (FVar k) n → Vec (Functor (Sets^ k ) (Sets )) n → SetEnv
ρ [ Vec.[] :fvs= Vec.[] ] = ρ
ρ [ φ  ∷ φs :fvs= F ∷ Fs ] = record { tc = SetEnv.tc ρ ; fv = extendfv (SetEnv.fv (ρ [ φs :fvs= Fs ])) φ F } 
-- outermost extension wil be _ [ φ1 := F1 ]


-- this version is functionally the same as :fvs= but operates on the entire environment. 
-- still, we can prove that the tc part is unchanged 
_[_:fvs='_] : ∀ {n k : ℕ} → SetEnv → Vec (FVar k) n → Vec (Functor (Sets^ k ) (Sets )) n → SetEnv
ρ [ Vec.[] :fvs=' Vec.[] ] = ρ
ρ [ φ  ∷ φs :fvs=' F ∷ Fs ] = (ρ [ φ :fv= F ]) [ φs :fvs=' Fs ]

fvs'eq : ∀ {n k : ℕ} → (ρ : SetEnv) → (φs : Vec (FVar k) n) → (Fs : Vec (Functor (Sets^ k ) (Sets )) n) 
        → ∀ {j} → SetEnv.tc (ρ [ φs :fvs=' Fs ]) {j} ≡ SetEnv.tc ρ {j}
fvs'eq ρ [] [] = ≡.refl
fvs'eq {suc n} {k} ρ (φ ∷ φs) (F ∷ Fs) = fvs'eq {n} {k} (ρ [ φ :fv= F ]) φs Fs 


-- -- extend environment for a vector of variables of different arities 
-- _[:fvs'=_] : ∀ {n : ℕ} → SetEnv → Vec (Σ ℕ (λ k → (FVar k) ×' Functor (Sets^ k) Sets)) n → SetEnv
-- ρ [:fvs'= Vec.[] ] = ρ
-- ρ [:fvs'= (k , (φ , F)) ∷ Fs ] = record { tc = SetEnv.tc ρ ; fv = extendfv (SetEnv.fv (ρ [:fvs'= Fs ])) φ F } 
-- -- ρ [ φ  ∷ φs :fvs= F ∷ Fs ] = (ρ [ φ :fv= F ]) [ φs :fvs= Fs ]

-- TODO try to add REWRITE rule that says 
-- extend ρ ψ F ψ = F





record SetEnvMorph (ρ ρ' : SetEnv) : Set₁ where
  field
    -- need proof that ∀ {k : ℕ} {t : TCVar k} (ρ.tc t ≡ ρ'.tc t)
    -- -- but how do we know when two functors are equal?

    -- eqTC : ∀ {k : ℕ} → SetEnv.tc ρ {k} ≡ SetEnv.tc ρ' {k}
    eqTC : (λ {k} ψ → SetEnv.tc ρ {k} ψ) ≡ (λ {k} ψ → SetEnv.tc ρ' {k} ψ)

    -- each type constructor variable is mapped to the identity
    -- natural transformation
    -- tc : ∀ {k : ℕ} {φ : TCVar k} → Functor (Sets)
    fv : ∀ {k : ℕ} → (φ : FVar  k) → NaturalTransformation (SetEnv.fv ρ φ) (SetEnv.fv ρ' φ)

-- get Set mapping (object) part of each variable in a Set environment
tcobj :  SetEnv → {k : ℕ} → TCVar k → (Vec Set k) → Set
tcobj ρ = Functor.F₀ ∘' SetEnv.tc ρ 

fvobj :  SetEnv → {k : ℕ} → FVar k → (Vec Set k) → Set
fvobj ρ = Functor.F₀ ∘' SetEnv.fv ρ 



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
idSetEnv = record { eqTC = ≡.refl ; fv = λ _ → record { η = λ X → idf ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl } }

SetEnvCat : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
SetEnvCat = record
    { Obj = SetEnv
    ; _⇒_ = SetEnvMorph
    -- do we need to reason about equality of SetEnvMorph?
    -- ; _≈_ = λ f g → {! ∀ {k : ℕ} {φ : FVar k} → SetEnvMorph.fv f φ ≈ SetEnvMorph.fv g φ  !}
    ; _≈_ = λ f g →  ∀ {k : ℕ} {φ : FVar k}  -- pointwise equal on natural transformations..
                → Category._≈_ ([Sets^ k ,Sets] ) (SetEnvMorph.fv f φ) (SetEnvMorph.fv g φ)
    ; id = idSetEnv
    ; _∘_ = _∘SetEnv_
    -- ; assoc = λ Xs → ≡.refl
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




-------------------------------------------------------
-- extend morphisms of environments 
-------------------------------------------------------

-- TODO maybe rename this to identity-rho or something? 
-- 
-- this gives rise to a functor extendSetEnv : [Sets^k ,Sets] → SetEnvCat
-- λ F → ρ [ φ :fv= F ]
extendmorph-η : ∀ {k} 
                {F G : Functor (Sets^l k lzero) (Setsl lzero)} 
              → (ρ : SetEnv)
              → (φ : FVar k)
              → NaturalTransformation F G 
              → SetEnvMorph (ρ [ φ ∷ Vec.[] :fvs= F ∷ Vec.[] ])
                            (ρ [ φ ∷ Vec.[] :fvs= G ∷ Vec.[] ])
extendmorph-η {k} {F} {G} record { tc = tc ; fv = fv } (φ ^F k) η = record { eqTC = ≡.refl ; fv = λ ψ → mapfv ψ }
  where mapfv : ∀ {j} (ψ : FVar j) 
          → NaturalTransformation (SetEnv.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ) 
                                  (SetEnv.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= G ∷ Vec.[] ]) ψ)
        mapfv (ψ ^F j) with eqNat k j | φ ≟ ψ 
        ... | yes ≡.refl | yes ≡.refl = η 
        ... | no _ | _ = idNaturalTransformation (fv (ψ ^F j))
        ... | yes ≡.refl | no _ = idNaturalTransformation (fv (ψ ^F j)) 

-- this gives rise to a functor extendSetEnvF : SetEnvCat → SetEnvCat
-- λ ρ → ρ [ φ :fv= F ]
extendmorph-idF : ∀  {k} (φ : FVar k) (F : Functor (Sets^ k) Sets)
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → SetEnvMorph (ρ  [ φ :fv= F ]) 
                            (ρ' [ φ :fv= F ]) 
extendmorph-idF {k} (φ ^F k) F ρ ρ' f = record { eqTC = SetEnvMorph.eqTC f ; fv = fvmap } 
          where fvmap : ∀ {j} (ψ : FVar j) 
                  → NaturalTransformation (SetEnv.fv (ρ  [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                                          (SetEnv.fv (ρ' [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                fvmap (ψ ^F j) with eqNat k j | φ ≟ ψ 
                ... | yes ≡.refl | yes ≡.refl = mkIdNatTr' F
                ... | no _ | _ = SetEnvMorph.fv f (ψ ^F j)
                ... | yes ≡.refl | no _ = SetEnvMorph.fv f (ψ ^F j)



extendmorph2 : ∀ {k} (φ : FVar k)
                {F G : Functor (Sets^l k lzero) (Setsl lzero)} 
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → NaturalTransformation F G 
              → SetEnvMorph (ρ  [ φ :fv= F ])
                            (ρ' [ φ :fv= G ])
extendmorph2 {k} φ {F} {G} ρ ρ' f η = extendmorph-η {k} {F} {G} ρ' φ η ∘SetEnv extendmorph-idF {k} φ F ρ ρ' f 

--------------------------------
-- Functor laws for extendSetEnv2
extendmorph2-identity : ∀ {k} (φ : FVar k) ρ
                        → (F : Category.Obj [Sets^ k ,Sets]) 
                        → ∀ {j : ℕ} {ψ : FVar j} 
                        → ([Sets^ j ,Sets] Category.≈
                         SetEnvMorph.fv
                         (extendmorph2 φ {F} {F} ρ ρ (Category.id SetEnvCat) (Category.id [Sets^ k ,Sets]))
                         ψ)
                        (SetEnvMorph.fv (Category.id SetEnvCat {ρ [ φ :fv= F ]}) ψ)
extendmorph2-identity (φ ^F k) ρ F {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl 
... | yes ≡.refl | no _ = ≡.refl 
... | no _ | _ = ≡.refl 

extendmorph2-homomorphism : ∀ {k} (φ : FVar k) {F1 F2 F3 : Category.Obj [Sets^ k ,Sets]} 
                              {ρ1 ρ2 ρ3 : SetEnv}
                              → (f : SetEnvMorph ρ1 ρ2) (η : NaturalTransformation F1 F2)
                              → (g : SetEnvMorph ρ2 ρ3) (δ : NaturalTransformation F2 F3)
                              → ∀ {j : ℕ} {ψ : FVar j} 
                              → {Xs : Vec Set j}
                              {x : Functor.F₀ (SetEnv.fv (ρ1 [ φ :fv= F1 ]) ψ) Xs} →
                            NaturalTransformation.η
                            (SetEnvMorph.fv
                              (extendmorph2 φ {F1} {F3} ρ1 ρ3 (g ∘SetEnv f) (δ ∘v η))
                             ψ)
                            Xs x
                            ≡
                            NaturalTransformation.η
                            (SetEnvMorph.fv 
                              ((extendmorph2 φ {F2} {F3} ρ2 ρ3 g δ)
                              ∘SetEnv (extendmorph2 φ {F1} {F2} ρ1 ρ2 f η))
                             ψ)
                            Xs x
extendmorph2-homomorphism (φ ^F k) f η g δ {j} {ψ ^F j}  with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | yes ≡.refl | no _ = ≡.refl
... | no _ | _ = ≡.refl

extendmorph2-resp : ∀ {k} (φ : FVar k) {ρ ρ' : SetEnv} 
                      {f g : SetEnvMorph ρ ρ'}
                      {F G : Functor (Sets^ k) Sets}
                      {η δ : NaturalTransformation F G}
                      (f≈g : (SetEnvCat Category.≈ f) g)
                      (η≈δ : ([Sets^ k ,Sets] Category.≈ η) δ) 
                      → ∀ {j : ℕ} {ψ : FVar j} 
                      → ([Sets^ j ,Sets] Category.≈
                        SetEnvMorph.fv (extendmorph2 φ {F} {G} ρ ρ' f η) ψ)
                        (SetEnvMorph.fv (extendmorph2 φ  {F} {G} ρ ρ' g δ) ψ)
extendmorph2-resp (φ ^F k) f≈g η≈δ {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = η≈δ 
... | yes ≡.refl | no _ = f≈g 
... | no _ | _ = f≈g 


-- λ ρ F → ρ [ φ := F ])
extendSetEnv2 : ∀ {k} → (φ : FVar k) 
              → Functor (Product SetEnvCat [Sets^ k ,Sets]) SetEnvCat
              -- → Functor SetEnvCat (Functors [Sets^ k ,Sets] SetEnvCat)
extendSetEnv2 φ = record
  { F₀ = λ (ρ , F) → ρ [ φ :fv= F ]
  ; F₁ = λ { {ρ , F} {ρ' , G} (f , η) → extendmorph2 φ  {F} {G} ρ ρ' f η }
  ; identity = λ { {ρ , F} → extendmorph2-identity φ ρ F }
  ; homomorphism = λ { {ρ1 , F1} {ρ2 , F2} {ρ3 , F3} {f , η} {g , δ} {Xs} → extendmorph2-homomorphism φ f η g δ } 
  ; F-resp-≈ = λ { (f≈g , η≈δ) {j} {ψ} → extendmorph2-resp φ f≈g η≈δ }
  }



-- used to define 'semantic substitution' and prove that syntactic substitution
-- interacts nicely with semantic substitution 
extendSetEnv-α : ∀ (α : FVar 0) 
                → Functor (Product SetEnvCat Sets) SetEnvCat
extendSetEnv-α α = extendSetEnv2 α ∘F (idF ⁂ Sets→0Functors) 


module extendSetEnv-ρ×As-noinline where 

  -- environment extension functor used to define extendTEnv used in TEnv. 
  -- this version is defined recursively on αs in terms of other environment extension functors 
  -- and functor combinators. this means it is a bit harder to see that this functor doesn't 
  -- alter the tc part of environment, which is useful for some proofs 
  -- 
  -- so instead, we use an equivalent functor extendSetEnv-ρ×As whose action on objects, etc. is given directly 

  -- λ ρ As → ρ [ αs := As ]
  -- 
  -- we can define this inductively in terms of extendSetEnv2 and functor operations 
  extendSetEnv-ρ×As-noinline : ∀ {k} → (αs : Vec (FVar 0) k) 
                  → Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
  extendSetEnv-ρ×As-noinline [] = πˡ 
  extendSetEnv-ρ×As-noinline {suc k} (α ∷ αs) = 
        let r : Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
            r = extendSetEnv-ρ×As-noinline αs 
            -- 
            extend-α : Functor (Product SetEnvCat [Sets^ 0 ,Sets]) SetEnvCat
            extend-α = extendSetEnv2 α
            -- change [Sets^0 , Sets] to Sets in extend-α
            extend-α-Sets : Functor (Product SetEnvCat Sets) SetEnvCat
            extend-α-Sets = extendSetEnv2 α ∘F (idF ⁂ Sets→0Functors)
            -- 
            decswap : Functor (Sets^ (suc k)) (Product (Sets^ k) Sets)
            decswap = Swap ∘F Sets^decompose k
            -- 
            decompose : Functor (Product SetEnvCat (Sets^ (suc k))) (Product (Product SetEnvCat (Sets^ k)) Sets)
            decompose = assocʳ SetEnvCat (Sets^ k) Sets ∘F (idF ⁂ decswap)
            -- 
            extend-αs : Functor (Product SetEnvCat (Sets^ (suc k))) (Product SetEnvCat Sets)
            extend-αs = (r ⁂ idF) ∘F decompose 

          in extend-α-Sets ∘F extend-αs 


  -- uses non-inlined version of (extendSetEnv-ρ×As αs)
  extendTEnv : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
              → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) SetEnvCat
  extendTEnv φ αs = (extendSetEnv-ρ×As-noinline αs) ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ) 


  -- testextend : ∀ {k} → (αs : Vec (FVar 0) k) → SetEnv → Vec Set k → SetEnv
  -- testextend αs ρ As = Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As) 

  -- testextend2 : (αs : Vec (FVar 0) 3) → SetEnv → Vec Set 3 → SetEnv
  -- testextend2 (a1 ∷ a2 ∷ a3 ∷ Vec.[]) ρ (A1 ∷ A2 ∷ A3 ∷ Vec.[]) = {!  ρ [ (a1 ∷ a2 ∷ a3 ∷ Vec.[]) :fvs= (ConstF A1 ∷ ConstF A2 ∷ ConstF A3 ∷ Vec.[]) ]  !} 

  -- testextend (a1 ∷ a2 ∷ a3 ∷ Vec.[]) ρ (A1 ∷ A2 ∷ A3 ∷ Vec.[])
  -- gives 
  -- ((ρ [ a3 :fv= ConstF A3 ]) [ a2 :fv= ConstF A2 ]) [ a1 :fv= ConstF A1 ]
  -- 
  -- which corresponds to the recursive definition of :fvs= 

  -- extendmorph2-vec : ∀ {k} {αs : Vec (FVar 0) k} (ρ ρ' : SetEnv) (f : SetEnvMorph ρ ρ')                    
  --                       (As Bs : Vec Set k) (gs : VecFSpace As Bs) 
  --                      → SetEnvMorph (ρ  [ αs :fvs= to0Functors As ])
  --                                    (ρ' [ αs :fvs= to0Functors Bs ])
  -- extendmorph2-vec : ∀ {k} {αs : Vec (FVar 0) k} (ρ ρ' : SetEnv) (f : SetEnvMorph ρ ρ')                    



extendmorph2-vec : ∀ {k n } (φs : Vec (FVar k) n)
                (Fs Gs : Vec (Functor (Sets^ k) Sets) n)
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → foreach2 (NaturalTransformation) Fs Gs
              → SetEnvMorph (ρ  [ φs :fvs= Fs ])
                            (ρ' [ φs :fvs= Gs ])
extendmorph2-vec {k} {zero} [] [] [] ρ ρ' f (lift Data.Unit.tt) = f
extendmorph2-vec {k} {suc n} (φ ∷ φs) (F ∷ Fs) (G ∷ Gs) ρ ρ' f (η , ηs) = 
      record { eqTC = SetEnvMorph.eqTC f 
             ; fv = SetEnvMorph.fv 
                        (extendmorph2 {k} φ (ρ [ φs :fvs= Fs ]) (ρ' [ φs :fvs= Gs ]) 
                            (extendmorph2-vec {k} {n} φs Fs Gs ρ ρ' f ηs) η) }


extendmorph2-vec-identity : ∀ {k} (αs : Vec (FVar 0) k) ρ
                              (As : Vec Set k)
                              → SetEnvCat Categories.Category.[ 
                                  extendmorph2-vec αs (to0Functors As) (to0Functors As) ρ ρ (Category.id SetEnvCat) (toConstNats (Category.id (Sets^ k)))
                                ≈ Category.id SetEnvCat {ρ [ αs :fvs= to0Functors As ]} ] 
extendmorph2-vec-identity {.0} [] ρ [] = ≡.refl 
-- extendmorph2-vec-identity {.0} {[]} ρ [] {j} {φ} {Xs} {x} = ≡.refl
extendmorph2-vec-identity {suc k} (α ∷ αs) ρ (A ∷ As) = 
  let id0 = Category.id [Sets^ 0 ,Sets]
      idAs = Category.id (Sets^ k)
      ρAs = ρ [ αs :fvs= vmap ConstF As ]
      -- 
      e2id : SetEnvCat Categories.Category.[
            extendmorph2 α ρAs ρAs idSetEnv id0
            ≈ Category.id SetEnvCat ]
      e2id = extendmorph2-identity (α ) ρAs (ConstF A) 
      -- 
      e2vec-id : SetEnvCat Categories.Category.[
            extendmorph2-vec αs (to0Functors As) (to0Functors As) ρ ρ idSetEnv (toConstNats idAs)
            ≈ Category.id SetEnvCat ]
      e2vec-id = extendmorph2-vec-identity αs ρ As 

    in begin≈
      extendmorph2 {0} α ρAs ρAs (extendmorph2-vec αs (to0Functors As) (to0Functors As) ρ ρ (idSetEnv {ρ}) (toConstNats (makeIdTuple As))) (ConstNat (idf {A = A}))
    ≈⟨ extendmorph2-resp α e2vec-id ≡.refl ⟩
    extendmorph2 α ρAs ρAs (idSetEnv {ρAs}) (id0 {ConstF A})
    ≈⟨ e2id ⟩ 
      idSetEnv 
    ≈∎
    where module SEC = Category SetEnvCat
          open SEC.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)




extendmorph2-vec-resp : ∀ {k} (αs : Vec (FVar 0) k) (ρ ρ' : SetEnv)
                          (f g : SetEnvMorph ρ ρ')
                          (As Bs : Vec Set k)
                          (hs is : VecFSpace As Bs)
                          (f≈g : (SetEnvCat Category.≈ f) g)
                          (hs≈is : (Sets^ k Category.≈ hs) is) 
                          → SetEnvCat Categories.Category.[
                            extendmorph2-vec {0} {k} αs (to0Functors As) (to0Functors Bs) ρ ρ' f (toConstNats hs)
                            ≈ extendmorph2-vec {0} {k} αs (to0Functors As) (to0Functors Bs) ρ ρ' g (toConstNats is)
                          ] 
                          
extendmorph2-vec-resp {0} [] ρ ρ' f g [] [] fnil fnil f≈g (lift Data.Unit.tt) {j} {φ} {Xs} {x} = f≈g
extendmorph2-vec-resp {suc k} (α ∷ αs) ρ ρ' f g (A ∷ As) (B ∷ Bs) (fcons h hs) (fcons i is) f≈g (h≈i , hs≈is) = 
  let ρAs = ρ [ αs :fvs= vmap ConstF As ]
      ρ'Bs = ρ' [ αs :fvs= vmap ConstF Bs ]
      As0 = to0Functors As
      Bs0 = to0Functors Bs
      -- 
      e2-vec-f-hs≈e2-vec-g-is  : SetEnvCat Categories.Category.[
              extendmorph2-vec αs As0 Bs0 ρ ρ' f (toConstNats hs)
              ≈ extendmorph2-vec αs As0 Bs0 ρ ρ' g (toConstNats is) ]
      e2-vec-f-hs≈e2-vec-g-is = extendmorph2-vec-resp αs ρ ρ' f g As Bs hs is f≈g hs≈is
      --
    in begin≈
      extendmorph2 α ρAs ρ'Bs (extendmorph2-vec αs As0 Bs0 ρ ρ' f (toConstNats hs)) (ConstNat h)
    ≈⟨ extendmorph2-resp α e2-vec-f-hs≈e2-vec-g-is h≈i ⟩
      extendmorph2 α ρAs ρ'Bs (extendmorph2-vec αs As0 Bs0 ρ ρ' g (toConstNats is)) (ConstNat i)
    ≈∎ 
    where module SEC = Category SetEnvCat
          open SEC.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)

extendmorph2-vec-homomorphism : ∀ {k} (αs : Vec (FVar 0) k) (ρ1 ρ2 ρ3 : SetEnv)
                                  (f : SetEnvMorph ρ1 ρ2) (g : SetEnvMorph ρ2 ρ3) 
                                  (As Bs Cs : Vec Set k)
                                  (hs : VecFSpace As Bs)
                                  (is : VecFSpace Bs Cs)
                                  → SetEnvCat Categories.Category.[ 
                                  extendmorph2-vec αs (to0Functors As) (to0Functors Cs) ρ1 ρ3 (g ∘SetEnv f) (toConstNats (is ∘Vec hs))
                                  ≈ 
                                  extendmorph2-vec αs (to0Functors Bs) (to0Functors Cs) ρ2 ρ3 g (toConstNats is)
                                  ∘SetEnv
                                  extendmorph2-vec αs (to0Functors As) (to0Functors Bs) ρ1 ρ2 f (toConstNats hs)
                                  ]
extendmorph2-vec-homomorphism [] ρ1 ρ2 ρ3 f g [] [] [] fnil fnil = ≡.refl
extendmorph2-vec-homomorphism (α ∷ αs) ρ1 ρ2 ρ3 f g (A ∷ As) (B ∷ Bs) (C ∷ Cs) (fcons h hs) (fcons i is) = 
  let As0 = to0Functors As
      Bs0 = to0Functors Bs
      Cs0 = to0Functors Cs
      ρ1As = ρ1 [ αs :fvs= As0 ]
      ρ2Bs = ρ2 [ αs :fvs= Bs0 ]
      ρ3Cs = ρ3 [ αs :fvs= Cs0 ]
      -- 
      e2-vec-hom : SetEnvCat Categories.Category.[
          extendmorph2-vec αs As0 Cs0 ρ1 ρ3 (g ∘SetEnv f) (toConstNats (is ∘Vec hs))
          ≈ extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)
            ∘SetEnv extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs) ]
      e2-vec-hom = extendmorph2-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is 
      -- 
  in begin≈
      extendmorph2 α ρ1As ρ3Cs  
        (extendmorph2-vec αs As0 Cs0 ρ1 ρ3 (g ∘SetEnv f) (toConstNats (is ∘Vec hs)))
        (ConstNat (i ∘' h))
    ≈⟨ extendmorph2-resp α e2-vec-hom ≡.refl ⟩ 
      extendmorph2 α ρ1As ρ3Cs  
        (extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)
            ∘SetEnv extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs))
        (ConstNat i ∘v ConstNat h)
    ≈⟨ extendmorph2-homomorphism α (extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs)) (ConstNat h) 
                                   (extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)) (ConstNat i) ⟩ 
      (extendmorph2 α ρ2Bs ρ3Cs (extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)) (ConstNat i))
      ∘SetEnv 
      (extendmorph2 α ρ1As ρ2Bs (extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs)) (ConstNat h))
    ≈∎ 
    where module SEC = Category SetEnvCat
          open SEC.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)


-- inline definition for faster type-checking of TEnv, etc. 
-- 
-- -- it's also easier to prove that this version doesn't alter the non-functorial part of environment 
-- 
-- -- previously called extendSetEnv-ρ×As-inline 
extendSetEnv-ρ×As : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
extendSetEnv-ρ×As αs = record
  { F₀ = λ { (ρ , As) → ρ [ αs :fvs= to0Functors As ] } 
  ; F₁ = λ { {ρ , As} {ρ' , Bs} (f , gs) → extendmorph2-vec αs (to0Functors As) (to0Functors Bs) ρ ρ' f (toConstNats gs) }
  ; identity = λ { {ρ , As} {j} {φ} {Xs} {x} → extendmorph2-vec-identity αs ρ As {j} {φ} {Xs} {x} }
  ; homomorphism = λ { {ρ1 , As} {ρ2 , Bs} {ρ3 , Cs} {f , hs} {g , is} → extendmorph2-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is }
  ; F-resp-≈ = λ { {ρ , As} {ρ' , Bs} {f , hs} {g , ks} (f≈g , hs≈ks) → extendmorph2-vec-resp αs ρ ρ' f g As Bs hs ks f≈g hs≈ks }
  } 



rename extendSetEnv-ρ×As to extendSetEnv-ρ×As-noinline and 
rename extendSetEnv-ρ×As-inline to extendSetEnv-ρ×As. use the latter version 
everywhere because it's easier to prove tc env is unaffected

extendSetEnv-ρ×As-inline-tc-lem : ∀ {k} → (αs : Vec (FVar 0) k) (ρ : SetEnv) (Xs : Vec Set k)
                → (λ {j} → SetEnv.tc (Functor.F₀ (extendSetEnv-ρ×As {k} αs) (ρ , Xs)) {j})
                ≡ SetEnv.tc ρ 
extendSetEnv-ρ×As-inline-tc-lem [] ρ [] = refl
extendSetEnv-ρ×As-inline-tc-lem (α ∷ αs) ρ (X ∷ Xs) = refl  

-- need this to define semantics of natural transformations 
extendSetEnv-αs : ∀ {k} → (αs : Vec (FVar 0) k) → SetEnv
                → Functor (Sets^ k) SetEnvCat
extendSetEnv-αs αs ρ = Functor.F₀ (curry.F₀ (extendSetEnv-ρ×As αs)) ρ 

-- test1 :  (αs : Vec (FVar 0) 3) → SetEnv → (Vec Set 3) → Set
-- test1 (a1 ∷ a2 ∷ as) ρ (A1 ∷ A2 ∷ As)= {! Functor.F₀ (extendSetEnv-αs (a1 ∷ a2 ∷ as) ρ) (A1 ∷ A2 ∷ As)  !}





extendTEnv2 : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
            → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) SetEnvCat
extendTEnv2 φ αs = (extendSetEnv-ρ×As αs) ∘F ((extendSetEnv2 φ ∘F πˡ) ※ πʳ)


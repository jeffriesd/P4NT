module EnvironmentsInnerRecCleanup where 



open import NestedSyntax6NoStrings using (TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
-- open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (isYes)
open import Data.Bool using (if_then_else_; true; false)

open import Categories.Category using (Category)

--   πˡ : Functor (Product C D) C
--   πʳ : Functor (Product C D) D
-- -- product of functors sharing the same domain
-- infixr 2 _※_
-- _※_ : ∀ (F : Functor C D₁) → (G : Functor C D₂) → Functor C (Product D₁ D₂)
-- -- testreferencemark




open import Categories.Category.Product using (Product ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_ ; assocʳ)
open import Categories.Category.Construction.Functors using (Functors; module curry ; evalF)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.Diagram.Colimit
-- open import Categories.Diagram.Cocone
open import Data.Nat using (ℕ ; _≤_ )
open ℕ
open _≤_

open import Data.Fin using (Fin)

open import Data.List as List
open import Data.Unit using (⊤)
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning
open import Data.Product hiding (assocʳ) renaming (_×_ to _×'_)
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_)
open import Data.Sum.Properties using (inj₂-injective)

open import SetCatslzero

open import Utils



-------------------------------------------------------
-- Environments
-------------------------------------------------------

record SetEnv : Set₁  where
  field
    tc : ∀ {k : ℕ} → TCVar k → Functor (Sets^ k ) (Sets )
    fv : ∀ {k : ℕ} → FVar  k → Functor (Sets^ k ) (Sets )


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

    eqTC : ∀ {k : ℕ} → SetEnv.tc ρ {k} ≡ SetEnv.tc ρ' {k}

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
tcEq-SetEnvMorph : ∀ {k} → {ρ ρ' : SetEnv} 
                    → (f : SetEnvMorph ρ ρ') 
                    → (ψ : TCVar k)
                    → SetEnv.tc ρ ψ ≡ SetEnv.tc ρ' ψ
-- tcEq-SetEnvMorph {k} f ψ = ≡.cong-app (SetEnvMorph.eqTC f) ψ 
tcEq-SetEnvMorph record { eqTC = eqTC ; fv = fv } ψ = ≡.cong-app eqTC ψ


_∘SetEnv_ : ∀ {ρ ρ' ρ''} → SetEnvMorph ρ' ρ'' → SetEnvMorph ρ ρ' → SetEnvMorph ρ ρ''
g ∘SetEnv f = record { eqTC = ≡.trans (SetEnvMorph.eqTC f) (SetEnvMorph.eqTC g)
                           ; fv   = λ {k} φ → (SetEnvMorph.fv g φ) ∘v (SetEnvMorph.fv f φ) }

-- given ρ ρ' with f : ρ → ρ',
-- derive identity natural transformation for a given TCVar 
mkIdTCNT : ∀ {k} {ρ ρ' : SetEnv}
           → (f : SetEnvMorph ρ ρ')
           → (ψ : TCVar k)
           → NaturalTransformation (SetEnv.tc ρ ψ) (SetEnv.tc ρ' ψ)
mkIdTCNT {k} {ρ} {ρ'} f ψ = mkIdNatTr (SetEnv.tc ρ ψ) (SetEnv.tc ρ' ψ) (≡.cong-app (SetEnvMorph.eqTC f) ψ)

mkIdTCNT-lem : ∀ {k} (F G : Functor [Sets^ k ,Sets] Sets)
          → (e1 e2 : F ≡ G)
          → mkIdNatTr F G e1
            ≡ mkIdNatTr F G e2
mkIdTCNT-lem F .F ≡.refl ≡.refl = ≡.refl 

mkIdTCNT-lem2 : ∀ {k} {ρ ρ' : SetEnv}
           → (F : Functor [Sets^ k ,Sets] Sets)
           → ∀ Xs {x}
           → NaturalTransformation.η (idNaturalTransformation F) Xs x
           ≡ x
mkIdTCNT-lem2 {k} F Xs {x} = ≡.refl 


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


module SEC = Category SetEnvCat
open SEC.HomReasoning hiding (step-≡) renaming (begin_ to begin≈_ ; _∎ to _≈∎)




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
extendmorph-idF : ∀  {k} {φ : FVar k} {F : Functor (Sets^ k) Sets}
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → SetEnvMorph (ρ  [ φ :fv= F ]) 
                            (ρ' [ φ :fv= F ]) 
extendmorph-idF {k} {φ ^F k} {F} ρ ρ' f = record { eqTC = SetEnvMorph.eqTC f ; fv = fvmap } 
          where fvmap : ∀ {j} (ψ : FVar j) 
                  → NaturalTransformation (SetEnv.fv (ρ  [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                                          (SetEnv.fv (ρ' [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                fvmap (ψ ^F j) with eqNat k j | φ ≟ ψ 
                ... | yes ≡.refl | yes ≡.refl = mkIdNatTr' F
                ... | no _ | _ = SetEnvMorph.fv f (ψ ^F j)
                ... | yes ≡.refl | no _ = SetEnvMorph.fv f (ψ ^F j)



extendmorph2 : ∀ {k} {φ : FVar k} 
                {F G : Functor (Sets^l k lzero) (Setsl lzero)} 
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → NaturalTransformation F G 
              → SetEnvMorph (ρ  [ φ :fv= F ])
                            (ρ' [ φ :fv= G ])
extendmorph2 {k} {φ} {F} {G} ρ ρ' f η = extendmorph-η {k} {F} {G} ρ' φ η ∘SetEnv extendmorph-idF {k} {φ} {F} ρ ρ' f 

--------------------------------
-- Functor laws for extendSetEnv2
extendmorph2-identity : ∀ {k} (φ : FVar k) ρ
                        → (F : Category.Obj [Sets^ k ,Sets]) 
                        → ∀ {j : ℕ} {ψ : FVar j} 
                        → ([Sets^ j ,Sets] Category.≈
                         SetEnvMorph.fv
                         (extendmorph2 {φ = φ} {F} {F} ρ ρ (Category.id SetEnvCat) (Category.id [Sets^ k ,Sets]))
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
                              (extendmorph2 {φ = φ} {F1} {F3} ρ1 ρ3 (g ∘SetEnv f) (δ ∘v η))
                             ψ)
                            Xs x
                            ≡
                            NaturalTransformation.η
                            (SetEnvMorph.fv 
                              ((extendmorph2 {φ = φ} {F2} {F3} ρ2 ρ3 g δ)
                              ∘SetEnv (extendmorph2 {φ = φ} {F1} {F2} ρ1 ρ2 f η))
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
                        SetEnvMorph.fv (extendmorph2 {φ = φ} {F} {G} ρ ρ' f η) ψ)
                        (SetEnvMorph.fv (extendmorph2 {φ = φ} {F} {G} ρ ρ' g δ) ψ)
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
  ; F₁ = λ { {ρ , F} {ρ' , G} (f , η) → extendmorph2 {φ = φ} {F} {G} ρ ρ' f η }
  ; identity = λ { {ρ , F} → extendmorph2-identity φ ρ F }
  ; homomorphism = λ { {ρ1 , F1} {ρ2 , F2} {ρ3 , F3} {f , η} {g , δ} {Xs} → extendmorph2-homomorphism φ f η g δ } 
  ; F-resp-≈ = λ { (f≈g , η≈δ) {j} {ψ} → extendmorph2-resp φ f≈g η≈δ }
  }


-- λ ρ As → ρ [ αs := As ]
-- 
-- we can define this inductively in terms of extendSetEnv2 and functor operations 
extendSetEnv-ρ×As : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
extendSetEnv-ρ×As [] = πˡ 
extendSetEnv-ρ×As {suc k} (α ∷ αs) = 
      let r : Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
          r = extendSetEnv-ρ×As αs 
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

-- testextend : ∀ {k} → (αs : Vec (FVar 0) k) → SetEnv → Vec Set k → SetEnv
-- testextend αs ρ As = Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As) 

-- testextend2 : (αs : Vec (FVar 0) 3) → SetEnv → Vec Set 3 → SetEnv
-- testextend2 (a1 ∷ a2 ∷ a3 ∷ Vec.[]) ρ (A1 ∷ A2 ∷ A3 ∷ Vec.[]) = {!  ρ [ (a1 ∷ a2 ∷ a3 ∷ Vec.[]) :fvs= (ConstF A1 ∷ ConstF A2 ∷ ConstF A3 ∷ Vec.[]) ]  !} 

-- testextend (a1 ∷ a2 ∷ a3 ∷ Vec.[]) ρ (A1 ∷ A2 ∷ A3 ∷ Vec.[])
-- gives 
-- ((ρ [ a3 :fv= ConstF A3 ]) [ a2 :fv= ConstF A2 ]) [ a1 :fv= ConstF A1 ]
-- 
-- which corresponds to the recursive definition of :fvs= 


-- need this to define semantics of natural transformations 
extendSetEnv-αs : ∀ {k} → (αs : Vec (FVar 0) k) → SetEnv
                → Functor (Sets^ k) SetEnvCat
extendSetEnv-αs αs ρ = Functor.F₀ (curry.F₀ (extendSetEnv-ρ×As αs)) ρ 

-- test1 :  (αs : Vec (FVar 0) 3) → SetEnv → (Vec Set 3) → Set
-- test1 (a1 ∷ a2 ∷ as) ρ (A1 ∷ A2 ∷ As)= {! Functor.F₀ (extendSetEnv-αs (a1 ∷ a2 ∷ as) ρ) (A1 ∷ A2 ∷ As)  !}



extendTEnv : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
            → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) SetEnvCat
extendTEnv φ αs = (extendSetEnv-ρ×As αs) ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ) 



---------------------------------------------------------------------------------

-- -- λ ρ → ρ [ φ :fv= F ]
-- -- this works but we don't really need it 
-- extendSetEnvF : ∀ {k} → (φ : FVar k) → Functor (Sets^ k) Sets
--               → Functor SetEnvCat SetEnvCat
-- extendSetEnvF φ F = record
--   { F₀ = λ ρ → ρ [ φ :fv= F ]
--   ; F₁ = λ {ρ} {ρ'} f → extendmorph-idF {φ = φ} ρ ρ' f
--   ; identity = λ {ρ} → extendSetEnvF-identity φ F ρ
--   ; homomorphism = λ {ρ1 ρ2 ρ3} {f} {g} →  extendSetEnvF-homomorphism φ F f g
--   ; F-resp-≈ = λ {ρ ρ'} {f} {g} f≈g → extendSetEnvF-resp φ F f≈g
--   } 
-- --------------------------------
-- -- Functor laws for extendSetEnvF

-- extendSetEnvF-identity : ∀ {k} (φ : FVar k)
--                          → (F : Functor (Sets^ k) Sets) 
--                          → (ρ : SetEnv) 
--                          → SetEnvCat Categories.Category.[
--                          extendmorph-idF {φ = φ} {F} ρ ρ (Category.id SetEnvCat) ≈ Category.id SetEnvCat
--                          ]
-- extendSetEnvF-identity (φ ^F k) F ρ {φ = ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
-- ... | yes ≡.refl | yes ≡.refl = ≡.refl
-- ... | yes ≡.refl | no _ = ≡.refl
-- ... | no _ | _ = ≡.refl

-- extendSetEnvF-homomorphism : ∀ {k} (φ : FVar k)
--                              → (F : Functor (Sets^ k) Sets) 
--                              → {ρ1 ρ2 ρ3 : SetEnv}
--                              → (f : SetEnvMorph ρ1 ρ2 )
--                              → (g : SetEnvMorph ρ2 ρ3 )
--                              → SetEnvCat Categories.Category.[
--                              extendmorph-idF {φ = φ} {F} ρ1 ρ3 (SetEnvCat Categories.Category.[ g ∘ f ]) ≈
--                              SetEnvCat Categories.Category.[ extendmorph-idF {φ = φ} {F} ρ2 ρ3 g ∘
--                              extendmorph-idF {φ = φ} {F} ρ1 ρ2 f ]
--                              ]
-- extendSetEnvF-homomorphism (φ ^F k) F f g {φ = ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
-- ... | yes ≡.refl | yes ≡.refl = ≡.refl
-- ... | yes ≡.refl | no _ = ≡.refl 
-- ... | no _ | _ = ≡.refl

-- extendSetEnvF-resp : ∀ {k} (φ : FVar k)
--                        (F : Functor (Sets^ k) Sets) {ρ} {ρ'}
--                        {f g : SetEnvMorph ρ ρ'}
--                        (f≈g : SetEnvCat Categories.Category.[ f ≈ g ]) 
--                        → SetEnvCat Categories.Category.[ extendmorph-idF {φ = φ} {F} ρ ρ' f ≈
--                           extendmorph-idF {φ = φ} {F} ρ ρ' g ]
-- extendSetEnvF-resp (φ ^F k) F f≈g {φ = ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
-- ... | yes ≡.refl | yes ≡.refl = ≡.refl
-- ... | yes ≡.refl | no _ = f≈g 
-- ... | no _ | _ = f≈g 
-- -- 
-- 
-- -- 
-- -- environment extension gives a functor from [Sets^k,Sets] to SetEnvCat
-- -- for a fixed φ and ρ
-- -- 
-- -- denoted in the paper as 
-- -- ρ [ φ := _ ]
-- -- or 
-- -- λ F → ρ [ φ := F ]
-- extendSetEnv : ∀ {k} → (φ : FVar k) → SetEnv
--               → Functor [Sets^ k ,Sets] SetEnvCat
-- extendSetEnv {k} φ ρ = record
--   { F₀ = λ F → ρ [ φ :fv= F ]
--   ; F₁ = λ {F} {G} η → extendmorph-η {k} {F} {G} ρ φ η 
--   ; identity = λ {F} → extendmorph-identity ρ φ F
--   ; homomorphism = λ {F} {G} {H} {η} {η'} → extendmorph-homo ρ φ η η'
--   ; F-resp-≈ = λ {F} {G} {η} {η'} η≈η' → extendmorph-resp ρ φ η≈η'
--   } 
-- --------------------------------
-- -- Functor laws for extendSetEnv

-- extendmorph-identity : ∀ {k} → (ρ : SetEnv) → (φ : FVar k)
--                    → (F : Functor (Sets^ k) Sets) 
--                    → SetEnvCat Categories.Category.[
--                         extendmorph-η {k} {F} {F} ρ φ (Category.id [Sets^ k ,Sets]) 
--                         ≈ Category.id SetEnvCat
--                      ]
-- extendmorph-identity ρ (φ ^F k) F {φ = ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
-- ... | yes ≡.refl | yes ≡.refl = ≡.refl 
-- ... | no _ | _ = ≡.refl 
-- ... | yes ≡.refl | no _ = ≡.refl 

-- extendmorph-homo : ∀ {k} (ρ : SetEnv) (φ : FVar k) 
--                      {F G H : Category.Obj [Sets^ k ,Sets]}
--                      (η : NaturalTransformation F G)
--                      (η' : NaturalTransformation G H)
--                      → SetEnvCat Categories.Category.[
--                         extendmorph-η ρ φ (η' ∘v η)
--                         ≈  extendmorph-η ρ φ η' ∘SetEnv extendmorph-η ρ φ η
--                      ]
-- extendmorph-homo ρ (φ ^F k) η η' {φ = ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
-- ... | yes ≡.refl | yes ≡.refl = ≡.refl 
-- ... | no _ | _ = ≡.refl 
-- ... | yes ≡.refl | no _ = ≡.refl 

-- extendmorph-resp : ∀ {k} (ρ : SetEnv) (φ : FVar k) 
--                      {F G : Category.Obj [Sets^ k ,Sets]}
--                      {η η' : [Sets^ k ,Sets] Categories.Category.[ F , G ]}
--                      → (η≈η' : [Sets^ k ,Sets] Categories.Category.[ η ≈ η' ])
--                      → SetEnvCat Categories.Category.[ 
--                        extendmorph-η ρ φ η ≈ extendmorph-η ρ φ η' ]
-- extendmorph-resp ρ (φ ^F k) η≈η' {φ = ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
-- ... | yes ≡.refl | yes ≡.refl = η≈η' {Xs}
-- ... | no _ | _ = ≡.refl 
-- ... | yes ≡.refl | no _ = ≡.refl 


-- unused extendmorph variants

-- extendmorph-η-vec : ∀ {k n } {φs : Vec (FVar k) n} 
--                 {Fs Gs : Vec (Functor (Sets^ k) Sets) n} 
--               → (ρ : SetEnv)
--               → foreach2 (NaturalTransformation) Fs Gs
--               → SetEnvMorph (ρ  [ φs :fvs= Fs ])
--                             (ρ  [ φs :fvs= Gs ])
-- extendmorph-η-vec {k} {zero} {[]} {[]} {[]} ρ (lift Data.Unit.tt) = Category.id SetEnvCat
-- extendmorph-η-vec {k} {suc n} {φ ∷ φs} {F ∷ Fs} {G ∷ Gs} ρ (η , ηs) = 
--     let ρηs = extendmorph-η-vec {k} {n} {φs} {Fs} {Gs} ρ ηs 
--         ρFs = ρ [ φs :fvs= Fs ]
--         ρGs = ρ [ φs :fvs= Gs ]
--         extendρηs = extendmorph2 {k} {φ} {F} {G} ρFs ρGs ρηs η 
--     in record { eqTC = ≡.refl 
--               ; fv = SetEnvMorph.fv extendρηs }


-- extendmorph2-vec : ∀ {k n } {φs : Vec (FVar k) n} 
--                 {Fs Gs : Vec (Functor (Sets^ k) Sets) n} 
--               → (ρ ρ' : SetEnv)
--               → SetEnvMorph ρ ρ'
--               → foreach2 (NaturalTransformation) Fs Gs
--               → SetEnvMorph (ρ  [ φs :fvs= Fs ])
--                             (ρ' [ φs :fvs= Gs ])
-- extendmorph2-vec {k} {zero} {[]} {[]} {[]} ρ ρ' f (lift Data.Unit.tt) = f
-- extendmorph2-vec {k} {suc n} {φ ∷ φs} {F ∷ Fs} {G ∷ Gs} ρ ρ' f (η , ηs) = 
--       record { eqTC = SetEnvMorph.eqTC f 
--              ; fv = SetEnvMorph.fv 
--                         (extendmorph2 {k} {φ} (ρ [ φs :fvs= Fs ]) (ρ' [ φs :fvs= Gs ]) 
--                             (extendmorph2-vec {k} {n} {φs} ρ ρ' f ηs) η) }

-- extendmorph2-vec' : ∀ {k n } {φs : Vec (FVar k) n} 
--                 {Fs Gs : Vec (Functor (Sets^ k) Sets) n} 
--               → (ρ ρ' : SetEnv)
--               → SetEnvMorph ρ ρ'
--               → foreach2 (NaturalTransformation) Fs Gs
--               → SetEnvMorph (ρ  [ φs :fvs=' Fs ])
--                             (ρ' [ φs :fvs=' Gs ])
-- extendmorph2-vec' {k} {zero} {[]} {[]} {[]} ρ ρ' f (lift Data.Unit.tt) = f
-- extendmorph2-vec' {k} {suc n} {φ ∷ φs} {F ∷ Fs} {G ∷ Gs} ρ ρ' f (η , ηs) = 
--     let ρF  = ρ  [ φ :fv= F ] 
--         ρ'G = ρ' [ φ :fv= G ] 
--         ρF→ρ'G = extendmorph2 {k} {φ} ρ ρ' f η
--     in extendmorph2-vec' {φs = φs} {Fs} {Gs} ρF ρ'G ρF→ρ'G ηs


-- -- extendmorphρ : ∀ {k} {αs : Vec (FVar 0) k}
-- --                 {As : Vec Set k}
-- --               → (ρ ρ' : SetEnv)
-- --               → SetEnvMorph ρ ρ'
-- --               → SetEnvMorph (ρ [ αs :fvs= to0Functors As ]) 
-- --                             (ρ' [ αs :fvs= to0Functors As ]) 
-- -- extendmorphρ {αs = Vec.[]} {Vec.[]} ρ ρ' f = f
-- -- extendmorphρ {αs = α ∷ αs} {A ∷ As} ρ ρ' f = 
-- --     let r = extendmorphρ {αs = αs} {As} ρ ρ' f
-- --         in record { eqTC = SetEnvMorph.eqTC f ; fv =  {! fvmap   !} } 
-- --         where fvmap : ∀ {n} {α} {αs : Vec (FVar 0) n} {A}
-- --                   {As : Vec Set n} {k} (φ : FVar k) →
-- --                 NaturalTransformation
-- --                 (SetEnv.fv (ρ [ α ∷ αs :fvs= to0Functors (A ∷ As) ]) φ)
-- --                 (SetEnv.fv (ρ' [ α ∷ αs :fvs= to0Functors (A ∷ As) ]) φ)
-- --               fvmap {n} {α ^F 0} {αs} {A} {As} (φ ^F 0) with α ≟ φ
-- --               ... | yes ≡.refl = mkIdNatTr' (ConstF A)
-- --               ... | no _ = SetEnvMorph.fv {!   !} (α ^F 0) 
-- --               fvmap {n} {α} {αs} {A} {As} (φ ^F suc j) = {!   !} 
              




-- -- 
-- extendmorphT-As : ∀ {k} {αs : Vec (FVar 0) k}
--                 {As Bs : Vec Set k}
--               → (ρ : SetEnv)
--               → (gs : VecFSpace As Bs)
--               → SetEnvMorph (ρ [ αs :fvs= to0Functors As ]) 
--                             (ρ [ αs :fvs= to0Functors Bs ]) 
-- extendmorphT-As {αs = []} {[]} {[]} ρ gs = Category.id SetEnvCat
-- extendmorphT-As {αs = α ∷ αs} {A ∷ As} {B ∷ Bs} ρ (fcons g gs) = 
--   let ρAs = ρ [ αs :fvs= vmap ConstF As ] 
--       ρBs = ρ [ αs :fvs= vmap ConstF Bs ] 
--       r = extendmorphT-As {_} {αs} {As} {Bs} ρ gs 
--       -- e : SetEnvMorph ((ρ [ αs :fvs= vmap ConstF As ]) [ α ∷ [] :fvs= ConstF A ∷ [] ])
--       --                 ((ρ [ αs :fvs= vmap ConstF Bs ]) [ α ∷ [] :fvs= ConstF B ∷ [] ])
--       ρgs   = extendmorph2 {0} {α} {ConstF A} {ConstF B} ρAs ρBs r (ConstNat g) 
--     in record { eqTC = ≡.refl ; fv = λ ψ → SetEnvMorph.fv ρgs ψ }


-- extendeqTC : ∀ {k n}  {φs : Vec (FVar k) n} {Fs}
--               → (ρ : SetEnv)
--               → ∀ {j} 
--               → (SetEnv.tc ρ {j})
--                   ≡ SetEnv.tc (ρ [ φs :fvs= Fs ]) {j}
-- extendeqTC {k} {.0} {Vec.[]} {Vec.[]} record { tc = tc ; fv = fv } = ≡.refl
-- extendeqTC {k} {.(suc _)} {φ ∷ φs} {F ∷ Fs} record { tc = tc ; fv = fv } = ≡.refl 



-- -- extend morphism of environments along As,Bs and id_F.
-- -- This function is used to define the map for T^H ρ 
-- extendmorphT : ∀ {k} {φ : FVar k} {αs : Vec (FVar 0) k}
--                 {F : Functor (Sets^l k lzero) (Setsl lzero)} {As Bs : Vec Set k}
--               → (ρ : SetEnv)
--               → (gs : VecFSpace As Bs)
--               → SetEnvMorph ((ρ [ αs :fvs= to0Functors As ]) [ φ ∷ Vec.[] :fvs= F ∷ Vec.[] ])
--                             ((ρ [ αs :fvs= to0Functors Bs ]) [ φ ∷ Vec.[] :fvs= F ∷ Vec.[] ])
-- extendmorphT {k} {φ} {αs} {F} {As} {Bs} ρ gs = 
--   let ρAs = (ρ [ αs :fvs= to0Functors As ])
--       ρBs = (ρ [ αs :fvs= to0Functors Bs ])
--       ρgs = extendmorphT-As {k} {αs} {As} {Bs} ρ gs
--       in extendmorph-idF {k} {φ} {F} ρAs ρBs ρgs 


-- extendmorphT-η : ∀ {k} {φ : FVar k} {αs : Vec (FVar 0) k}
--                 {F G : Functor (Sets^l k lzero) (Setsl lzero)} 
--               → (η : NaturalTransformation F G)
--                 {As Bs : Vec Set k}
--               → (ρ : SetEnv)
--               → (gs : VecFSpace As Bs)
--               → SetEnvMorph ((ρ [ αs :fvs= to0Functors As ]) [ φ ∷ Vec.[] :fvs= F ∷ Vec.[] ])
--                             ((ρ [ αs :fvs= to0Functors Bs ]) [ φ ∷ Vec.[] :fvs= G ∷ Vec.[] ])
-- extendmorphT-η {k} {φ} {αs} {F} {G} η {As} {Bs} ρ gs = 
--   let ρAs = (ρ [ αs :fvs= to0Functors As ])
--       ρBs = (ρ [ αs :fvs= to0Functors Bs ])
--       ρgs = extendmorphT-As {k} {αs} {As} {Bs} ρ gs
--       in extendmorph2 {k} {φ} ((ρ [ αs :fvs= to0Functors As ])) ((ρ [ αs :fvs= to0Functors Bs ])) ρgs η

-- -- same as extendmorphT-η but with F / As swapped 
-- extendmorphT-η-g : ∀ {k} {φ : FVar k} {αs : Vec (FVar 0) k}
--                 {F G : Functor (Sets^l k lzero) (Setsl lzero)} 
--               → (η : NaturalTransformation F G)
--                 {As Bs : Vec Set k}
--               → (ρ : SetEnv)
--               → (gs : VecFSpace As Bs)
--               → SetEnvMorph ((ρ [ φ :fv= F ]) [ αs :fvs=' to0Functors As ])
--                             ((ρ [ φ :fv= G ]) [ αs :fvs=' to0Functors Bs ])
-- extendmorphT-η-g {k} {φ} {αs} {F} {G} η {As} {Bs} ρ gs = 
--   let As⇒Bs = toConstNats gs
--       ρη = extendmorph-η ρ φ η 
--       in extendmorph2-vec' {φs = αs} (ρ [ φ :fv= F ]) (ρ [ φ :fv= G ]) ρη As⇒Bs

-- extendmorphT-f : ∀ {k} {φ : FVar k} {αs : Vec (FVar 0) k}
--                 {F : Functor (Sets^l k lzero) (Setsl lzero)} 
--                 {As : Vec Set k}
--               → (ρ ρ' : SetEnv)
--               → SetEnvMorph ρ ρ'
--               → SetEnvMorph ((ρ  [ φ :fv= F ]) [ αs :fvs=' to0Functors As ])
--                             ((ρ' [ φ :fv= F ]) [ αs :fvs=' to0Functors As ])
-- extendmorphT-f {φ = φ} {αs} {F} ρ ρ' f = 
--       let ρF  = ρ  [ φ :fv= F ]
--           ρ'F = ρ' [ φ :fv= F ] 
--           ρF→ρ'F = extendmorph-idF {φ = φ} ρ ρ' f 
--         in extendmorph-idF-vec' {φs = αs} ρF ρ'F ρF→ρ'F 



-- extendmorph-idF-vec : ∀ {k n} {φs : Vec (FVar k) n}
--                 {Fs : Vec (Functor (Sets^ k) Sets) n}
--               → (ρ ρ' : SetEnv)
--               → SetEnvMorph ρ ρ'
--               → SetEnvMorph (ρ [ φs :fvs= Fs ]) 
--                             (ρ' [ φs :fvs= Fs ]) 
-- extendmorph-idF-vec {φs = Vec.[]} {Vec.[]} ρ ρ' f = f
-- extendmorph-idF-vec {φs = φ ∷ φs} {F ∷ Fs} ρ ρ' f = 
--   let r = extendmorph-idF-vec {φs = φs} {Fs} ρ ρ' f 
--       ρFs  = ρ  [ φs :fvs= Fs ] 
--       ρ'Fs = ρ' [ φs :fvs= Fs ] 
--     in extendmorph-idF {φ = φ} {F} {! ρ !} {! ρ'Fs  !} {!   !}
--       -- record { eqTC = SetEnvMorph.eqTC f 
--       --        ; fv = SetEnvMorph.fv  (extendmorph-idF {φ = φ} {F} (ρ [ φs :fvs= Fs ]) (ρ' [ φs :fvs= Fs ]) (extendmorph-idF-vec {φs = φs} {Fs} ρ ρ' f)) }


-- extendmorph-idF-vec' : ∀ {k n} {φs : Vec (FVar k) n}
--                 {Fs : Vec (Functor (Sets^ k) Sets) n}
--               → (ρ ρ' : SetEnv)
--               → SetEnvMorph ρ ρ'
--               → SetEnvMorph (ρ  [ φs :fvs=' Fs ]) 
--                             (ρ' [ φs :fvs=' Fs ]) 
-- extendmorph-idF-vec' {φs = Vec.[]} {Vec.[]} ρ ρ' f = f
-- extendmorph-idF-vec' {φs = φ ∷ φs} {F ∷ Fs} ρ ρ' f = 
--   let ρF  = ρ  [ φ :fv= F ] 
--       ρ'F = ρ' [ φ :fv= F ] 
--     in extendmorph-idF-vec' {φs = φs} {Fs} ρF ρ'F (extendmorph-idF {φ = φ} {F} ρ ρ' f)


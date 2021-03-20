-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}



module SetCats where

open import Relation.Binary using (IsEquivalence ; Reflexive ; Transitive ; Symmetric)
-- open TypeExpr
-- open _≀_⊢_
-- open NestedSyntax6.TypeContext
-- open import NestedSyntax6

open import Categories.Category using (Category)
open import Categories.Category.Instance.One
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Product using (Product ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_) 
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
-- open import Data.Nat using (ℕ ; _≤_ )
-- open ℕ
-- open _≤_

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)

open import Data.Unit using (⊤)
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Vec using (Vec ; _∷_; replicate) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning
open import Data.Product renaming (_×_ to _×'_)
open import Data.Sum
open import Data.Sum.Properties using (inj₂-injective)

open import Utils using (foreach2 ; vhead ; vtail ; ×'-cong)
------------------------------- stdlib uses Set _ here




-------------------------------------------------------
-- Category of sets
-------------------------------------------------------

Setsl : ∀ o → Category (lsuc o) o o
Setsl o = record
  { Obj       = Set o
  ; _⇒_       = λ A B → (A → B)
  ; _≈_       = λ f g → ∀ {x} → f x ≡ g x
  ; id        = λ x → x
  ; _∘_       = λ f g x → f (g x)
  ; assoc     = ≡.refl
  ; sym-assoc = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; identity² = ≡.refl
  ; equiv     = record
    { refl  = ≡.refl
    ; sym   = λ eq → ≡.sym eq
    ; trans = λ eq₁ eq₂ → ≡.trans eq₁ eq₂
    }
  ; ∘-resp-≈  = resp
  }
  where resp : ∀ {A B C : Set o} {f h : B → C} {g i : A → B} →
                 ({x : B} → f x ≡ h x) →
                 ({x : A} → g x ≡ i x) → {x : A} → f (g x) ≡ h (i x)
        resp {h = h} f≡h g≡i {x} = ≡.trans f≡h (≡.cong h g≡i)

Sets : Category (lsuc lzero) lzero lzero
Sets = Setsl lzero


SetSum : Functor (Product Sets Sets) Sets
SetSum = record
  { F₀ = λ { (A , B)  → A ⊎ B }
  ; F₁ = λ { {A , B} (f , g)  → λ { (inj₁ x) → inj₁ (f x)
                                  ; (inj₂ y) → inj₂ (g y) } }
  ; identity = λ { {A , B} {inj₁ x} → ≡.refl
                 ; {A , B} {inj₂ y} → ≡.refl }
  ; homomorphism = λ { {A , A'} {B , B'} {C , C'} {f , f'} {g , g'} {inj₁ x} → ≡.refl
                     ; {A , A'} {B , B'} {C , C'} {f , f'} {g , g'} {inj₂ y} → ≡.refl  }
  ; F-resp-≈ = λ { (f≈h , g≈i) {inj₁ x} → ≡.cong inj₁ f≈h
                 ; (f≈h , g≈i) {inj₂ y} → ≡.cong inj₂ g≈i }
  } 



SetProd : Functor (Product Sets Sets) Sets
SetProd = record
  { F₀ = λ { (A , B)  → A ×' B }
  ; F₁ = λ { (f , g) (x , y)  → f x , g y }
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≈ = λ { (f≈h , g≈i) → ×'-cong f≈h g≈i } 
  } 

-------------------------------------------------------



-- function space between two vectors of Sets
data VecFSpace {l : Level} : ∀ {k : ℕ} → Vec (Set l) k → Vec (Set l) k → Set l where
  fnil : VecFSpace Vec.[] Vec.[]
  fcons : ∀ {k : ℕ} {As Bs : Vec (Set l) k} {A B : Set l} → (f : A → B) → VecFSpace As Bs → VecFSpace (A ∷ As) (B ∷ Bs)


  -- maybe infix version will be nice..
-- _=Vec=>_ : ∀ {l : Level} {k : ℕ} → Vec (Set l) k → Vec (Set l) k → Set l
-- As =Vec=> Bs = VecFSpace As Bs

-- pointwise equality for vector of functions (VecFSpace)
pointwise-≈ : ∀ {l} {k} {Xs Ys : Vec (Set l) k} → (gs gs' : VecFSpace Xs Ys) → Set l
pointwise-≈ fnil fnil = Lift _ ⊤
pointwise-≈ {l} (fcons g gs) (fcons g' gs') = (Setsl l Category.≈ g) g' ×' pointwise-≈ gs gs' 

-- pointwise-≈ is an equivalence relation
equiv-pointwise-≈ : ∀ {l} {k} {As Bs : Vec (Set l) k} → IsEquivalence (pointwise-≈ {l} {k} {As} {Bs})
equiv-pointwise-≈ = record { refl = λ {gs} → refl gs ; sym = λ {gs} {hs} p → sym gs hs p ; trans = λ {fs} {gs} {hs} fs≈gs gs≈hs → trans fs gs hs fs≈gs gs≈hs } 
  where refl : ∀ {l} {k} {As Bs : Vec (Set l) k} → (gs : VecFSpace As Bs) → pointwise-≈ gs gs
        refl fnil = lift Data.Unit.tt
        refl (fcons f fs) = ≡.refl , refl fs
        sym : ∀ {l} {k} {As Bs : Vec (Set l) k} → (gs hs : VecFSpace As Bs) → pointwise-≈ gs hs → pointwise-≈ hs gs
        sym fnil fnil _ = lift Data.Unit.tt
        sym (fcons g gs) (fcons h hs) (g≈h , gs≈hs) = ≡.sym g≈h , sym gs hs gs≈hs 
        trans : ∀ {l} {k} {As Bs : Vec (Set l) k} → (fs gs hs : VecFSpace As Bs) → pointwise-≈ fs gs → pointwise-≈ gs hs → pointwise-≈ fs hs
        trans fnil fnil fnil _ _ = lift Data.Unit.tt
        trans (fcons f fs) (fcons g gs) (fcons h hs) (f≈g , fs≈gs) (g≈h , gs≈hs)= (≡.trans f≈g g≈h) , (trans fs gs hs fs≈gs gs≈hs) 


-- compositinon of vectors of functions 
_∘Vec_ : ∀ {l} {k} → {As Bs Cs : Vec (Set l) k} →
                VecFSpace Bs Cs → VecFSpace As Bs → VecFSpace As Cs
fnil ∘Vec fnil = fnil
(fcons f fs) ∘Vec (fcons g gs) = fcons (f ∘' g) (fs ∘Vec gs)

composeVecs : ∀ {l} {k} → {As Bs Cs : Vec (Set l) k} →
                VecFSpace Bs Cs → VecFSpace As Bs → VecFSpace As Cs
composeVecs = _∘Vec_ 


-- -- generic pointwise equality 
-- -- -- if every morphism in fs and gs are equivalent in C, then 
-- -- -- fs and gs are equivalent in C^k
-- gen-pointwise-≈ : ∀ {k} {o l e} {C : Category o l e} → {Xs Ys : Vec (Category.Obj C) k}
--               → (fs gs : foreach2 (Category._⇒_ C) Xs Ys)
--               → Set (lsuc e)
-- gen-pointwise-≈  {C = C} {Vec.[]} {Vec.[]} (lift Data.Unit.tt) (lift Data.Unit.tt) = Lift _ ⊤
-- gen-pointwise-≈  {C = C} {X ∷ Xs} {Y ∷ Ys} (f , fs) (g , gs) = (f C.≈ g) ×' gen-pointwise-≈ {C = C} fs gs
--   where module C = Category C


makeIdTuple : ∀ {l} {k : ℕ} →  (Xs : Vec (Set l) k) → VecFSpace Xs Xs
makeIdTuple Vec.[] = fnil
makeIdTuple (X ∷ Xs) = fcons idf (makeIdTuple Xs)

-- 
Sets^l : ℕ → (l : Level) → Category (lsuc l) (l) (l)
Sets^l k l = record
  { Obj = Vec (Set l) k
  -- ; _⇒_ = λ xs ys → Vec (ArrType l) k -- VecTypes {l} k --vecfuncs l k xs ys
  ; _⇒_ = VecFSpace {l}
  -- ; _≈_ =
  ; _≈_ = λ {Xs Ys} gs gs' → pointwise-≈ gs gs'
  ; id = λ {Xs} → makeIdTuple Xs
  ; _∘_ = _∘Vec_
  ; assoc = assocVecs
  ; sym-assoc = symAssocVecs
  ; identityˡ = identityVec-l
  ; identityʳ = identityVec-r
  ; identity² = identityVec-l
  ; ∘-resp-≈ = resp
  ; equiv = equiv-pointwise-≈
  }
  where assocVecs : ∀ {l} {k} → {As Bs Cs Ds : Vec (Set l) k} {fs : VecFSpace As Bs}
                      {gs : VecFSpace Bs Cs} {hs : VecFSpace Cs Ds} →
                      pointwise-≈ (composeVecs (composeVecs hs gs) fs)  (composeVecs hs (composeVecs gs fs))
        assocVecs {l} {k = zero} {.Vec.[]} {.Vec.[]} {.Vec.[]} {.Vec.[]} {fnil} {fnil} {fnil} = lift Data.Unit.tt
        assocVecs {l} {k = suc k} {A ∷ As} {B ∷ Bs} {C ∷ Cs} {D ∷ Ds} {fcons f fs} {fcons g gs} {fcons h hs} = ≡.refl , assocVecs

        symAssocVecs : ∀ {k} {l} {A B C D : Vec (Set l) k} {fs : VecFSpace A B} {gs : VecFSpace B C} {hs : VecFSpace C D} →
               pointwise-≈ (composeVecs hs (composeVecs gs fs)) (composeVecs (composeVecs hs gs) fs)
        symAssocVecs {fs = fnil} {fnil} {fnil} = lift Data.Unit.tt
        symAssocVecs {fs = fcons f fs} {fcons g gs} {fcons h hs} = ≡.refl , symAssocVecs 


        identityVec-l : ∀ {l} {k} {As Bs : Vec (Set l) k} {fs : VecFSpace As Bs} → pointwise-≈ (composeVecs (makeIdTuple Bs) fs) fs
        identityVec-l {As = Vec.[]} {Bs = Vec.[]} {fnil} = lift Data.Unit.tt
        identityVec-l {As = A ∷ As} {Bs = B ∷ Bs} {fcons f fs} = ≡.refl , identityVec-l

        identityVec-r : ∀ {l} {k} {As Bs : Vec (Set l) k} {fs : VecFSpace As Bs} → pointwise-≈ (composeVecs fs (makeIdTuple As)) fs
        identityVec-r {As = Vec.[]} {Bs = Vec.[]} {fnil} = lift Data.Unit.tt
        identityVec-r {As = A ∷ As} {Bs = B ∷ Bs} {fcons f fs} = ≡.refl , identityVec-r

        resp : ∀ {l} {k} {A B C : Vec (Set l) k} {fs hs : VecFSpace B C} {gs is : VecFSpace A B}
               → pointwise-≈ fs hs → pointwise-≈ gs is → pointwise-≈ (composeVecs fs gs) (composeVecs hs is)
        resp {fs = fnil} {fnil} {fnil} {fnil} _ _ = lift Data.Unit.tt
        resp {l} {fs = fcons f fs} {fcons h hs} {fcons g gs} {fcons i is} (f≈h , fs≈hs) (g≈i , gs≈is) = ∘-resp-≈ {f = f} {h} {g} {i} f≈h g≈i , resp fs≈hs gs≈is 
          where open Category (Setsl l) using (∘-resp-≈)


Sets^ : ℕ → Category (lsuc lzero) lzero lzero
Sets^ k = Sets^l k lzero


Sets^head : ∀ (n : ℕ) → Functor (Sets^ (suc n)) Sets
Sets^head n = record
    { F₀ = λ Xs → vhead Xs
    ; F₁ = λ { {X ∷ Xs} {Y ∷ Ys} (fcons f fs) x → f x  }
    ; identity = λ { {X ∷ Xs} → ≡.refl  }
    ; homomorphism = λ { {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {fcons f fs} {fcons g gs} → ≡.refl }
    ; F-resp-≈ = λ { {X ∷ Xs} {Y ∷ Ys} {fcons f fs} {fcons g gs} (f≈g , fs≈gs) → f≈g } 
    } 

Sets^tail : ∀ (n : ℕ) → Functor (Sets^ (suc n)) (Sets^ n)
Sets^tail n = record
  { F₀ = λ Xs → vtail Xs
  ; F₁ = λ { {X ∷ Xs} {Y ∷ Ys} (fcons f fs) → fs  }
  ; identity = λ { {X ∷ Xs} → Functor.identity (idF {C = Sets^ n}) } 
  ; homomorphism = λ { {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {fcons f fs} {fcons g gs} → Functor.homomorphism (idF {C = Sets^ n}) }
  ; F-resp-≈ = λ { {X ∷ Xs} {Y ∷ Ys} {fcons f fs} {fcons g gs} (f≈g , fs≈gs) → fs≈gs }
 } 

Sets^cons : ∀ (n : ℕ) → Functor (Product Sets (Sets^ n)) (Sets^ (suc n))
Sets^cons n = record
  { F₀ = λ { (X , Xs) → X ∷ Xs }
  ; F₁ = λ { (f , fs) → fcons f fs }
  ; identity = λ { {A , As} → ≡.refl , Functor.identity (idF {C = Sets^ n}) }
  ; homomorphism = (λ { {A , As} {B , Bs} {C , Cs} {f , fs} {g , gs} → ≡.refl , (Functor.homomorphism (idF {C = Sets^ n})) }) 
  ; F-resp-≈ = λ { {A , As} {B , Bs} {f , fs} {g , gs} (f≈g , fs≈gs) → f≈g , fs≈gs  }
  } 

Sets^decompose : ∀ (n : ℕ) → Functor (Sets^ (suc n)) (Product Sets (Sets^ n))
Sets^decompose n = Sets^head n ※ Sets^tail n 

-------------------------------------------------------
-- Constant functor
-------------------------------------------------------
-- 
-- NOTE - these are already defined in 
-- Categories.Functor.Construction.Constant 
ConstF : ∀ {o l e} {o' l' e'} {C : Category o l e}
           {D : Category o' l' e'} (d : Category.Obj D) → Functor C D
ConstF {D = D} d = record
  { F₀ = λ _ → d
  ; F₁ = λ _ → D.id
  ; identity = λ {A} → DEq.refl
  ; homomorphism = DEq.sym D.identity²
  ; F-resp-≈ = λ _ → DEq.refl
  }
  where module D = Category D
        module DEq = Category.Equiv D

ConstNat : ∀ {o l e} {o' l' e'} {C : Category o l e}
           {D : Category o' l' e'} {d d' : Category.Obj D}
           → (Category._⇒_ D) d d'
           → NaturalTransformation (ConstF {C = C} {D} d) (ConstF {C = C} {D} d')
ConstNat {D = D} {d} {d'} f = 
    record { η = λ c → f 
           ; commute = λ g → begin≈ (f D.∘ D.id) ≈⟨ D.identityʳ ⟩ 
                                    f ≈⟨ D.Equiv.sym D.identityˡ ⟩ 
                                    (D.id D.∘ f) ≈∎ 
           ; sym-commute = λ g → begin≈ (D.id D.∘ f) ≈⟨ D.identityˡ ⟩ 
                                        f ≈⟨ D.Equiv.sym D.identityʳ ⟩ 
                                        (f D.∘ D.id) ≈∎ 
          }
      where module D = Category D 
            open D.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)


-------------------------------------------------------

-------------------------------------------------------
-- Functor category [Sets,Sets]
-------------------------------------------------------

-- ext-cong-app : ∀ {A B C : Set} → {f h : B → C} {g i : A → B}
--                → (∀ x → f x ≡ h x) → (∀ x → g x ≡ i x)
--                → (∀ x → f (g x) ≡ h (i x))
-- ext-cong-app refl x = refl



idNaturalTransformation : ∀ {o l e o' l' e'} {C : Category o l e} {D : Category o' l' e'}
                          → (F : Functor C D)
                          → NaturalTransformation F F 
idNaturalTransformation {C = C} {D} F = 
  record { η = λ X → D.id 
           -- WTS  D.id D.∘ Functor.F₁ F f D.≈ Functor.F₁ F f D.∘ D.id 
           ; commute = λ {X} {Y} f → begin≈ (D.id D.∘ Functor.F₁ F f) 
                                            ≈⟨ D.identityˡ ⟩ 
                                            Functor.F₁ F f
                                            ≈⟨ D.Equiv.sym D.identityʳ ⟩ 
                                            (Functor.F₁ F f D.∘ D.id) ≈∎
           -- WTS Functor.F₁ F f D.∘ D.id D.≈ D.id D.∘ Functor.F₁ F f
           ; sym-commute = λ {X} {Y} f → begin≈ (Functor.F₁ F f D.∘ D.id) ≈⟨ D.identityʳ ⟩ 
                                                Functor.F₁ F f ≈⟨ D.Equiv.sym D.identityˡ ⟩  
                                                (D.id D.∘ Functor.F₁ F f) ≈∎ 
           } 
  where module D = Category D
        open D.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)


-- generic functor category construction 
-- -- morphisms in the functor category (natural transformations)
-- -- are considered equivalent when they are equivalent on all components in 
-- -- the target category D. 
[[_,_]] : ∀ {o l e o' l' e'} → Category o l e → Category o' l' e' → Category (o ⊔ l ⊔ e ⊔ o' ⊔ l' ⊔ e') (o ⊔ l ⊔ l' ⊔ e') (o ⊔ e') 
[[ C , D ]] = Functors C D
-- [[ C , D ]] = record
--   { Obj = Functor C D
--   ; _⇒_ = NaturalTransformation
--   -- ; _≈_ = {!   !}
--   ; _≈_ = λ eta1 eta2 → ∀ Xs → NaturalTransformation.η eta1 Xs D.≈ NaturalTransformation.η eta2 Xs
--   ; id = λ {F} → idNaturalTransformation F
--   -- ; id = record { η = λ Xs → idf ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl }
--   ; _∘_ = _∘v_
--   ; assoc = λ Xs → D.assoc
--   ; sym-assoc = λ Xs → D.sym-assoc
--   ; identityˡ = λ Xs → D.identityˡ
--   ; identityʳ = λ Xs → D.identityʳ
--   ; identity² = λ Xs → D.identity²
--   ; equiv = record { refl = λ Xs → D.Equiv.refl 
--                    ; sym = λ η1≈η2 Xs → D.Equiv.sym (η1≈η2 Xs) 
--                    ; trans = λ η1≈η2 η2≈η3 Xs → D.Equiv.trans (η1≈η2 Xs) (η2≈η3 Xs) }
--   ; ∘-resp-≈ = λ ηf≈ηh ηg≈ηi Xs → D.∘-resp-≈ (ηf≈ηh Xs) (ηg≈ηi Xs)
--   } 
--   where module D = Category D 
--         open D.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)


[Sets,Sets]l : ∀ {o} → Category (lsuc o) (lsuc o) (lsuc o)
[Sets,Sets]l {o} = record
  { Obj = Functor (Setsl o) (Setsl o)
  ; _⇒_ = λ F G → NaturalTransformation F G
  -- natural transformations are equal if they're component-wise equal...
  ; _≈_ = λ eta1 eta2 → ∀ (X : Set o) → NaturalTransformation.η eta1 X ≈ NaturalTransformation.η eta2 X
  -- ; id = record { η = λ X → idf ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl }
  ; id = λ {F} → idNaturalTransformation F
  ; _∘_ = _∘v_
  ; assoc = λ X → ≡.refl
  ; sym-assoc = λ X → ≡.refl
  ; identityˡ = λ X → ≡.refl
  ; identityʳ = λ X → ≡.refl
  ; identity² = λ X → ≡.refl
  ; equiv = record { refl = λ X → ≡.refl ; sym = λ f≡g X → ≡.sym (f≡g X) ; trans = λ i≡j j≡k X → ≡.trans (i≡j X) (j≡k X) }
  ; ∘-resp-≈ = λ f≡h g≡i X {fx} →  ∘-resp-≈ (λ {x} → f≡h X {x}) (λ {x} → g≡i X {x} )
  }
  where open Category (Setsl o)

[Sets,Sets] : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
[Sets,Sets] = [Sets,Sets]l {lzero}

-- k-ary functor category, polymorphic in universe level 
-- TODO -- use library definition of functor category (same as this one)
[Sets^_,Sets]l : ℕ → (o : Level) → Category (lsuc o) (lsuc o) (lsuc o)
[Sets^_,Sets]l k o = record
 { Obj = Functor (Sets^l k o) (Setsl o)
 ; _⇒_ = NaturalTransformation
                                                        -- ≈ in Sets o
 ; _≈_ = λ eta1 eta2 → ∀ Xs → NaturalTransformation.η eta1 Xs ≈ NaturalTransformation.η eta2 Xs
 ; id = record { η = λ Xs → idf ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl }
 ; _∘_ = _∘v_
 ; assoc = λ Xs → ≡.refl
 ; sym-assoc = λ Xs → ≡.refl
 ; identityˡ = λ Xs → ≡.refl
 ; identityʳ = λ Xs → ≡.refl
 ; identity² = λ Xs → ≡.refl
 ; equiv = record { refl = λ Xs → ≡.refl ; sym = λ f≡g Xs → ≡.sym (f≡g Xs) ; trans = λ i≡j j≡k Xs → ≡.trans (i≡j Xs) (j≡k Xs) }
 -- need to show vertical composition (composing components of nt) commutes with composeVecs?
 ; ∘-resp-≈ = λ f≡h g≡i Xs → ∘-resp-≈ (λ {x} → f≡h Xs {x}) (λ {x} → g≡i Xs {x})
 }
 where open Category (Sets^l k o) renaming (Obj to Set^k) hiding (_≈_ ; ∘-resp-≈)
       open Category (Setsl o) using (_≈_ ; ∘-resp-≈)


[Sets^_,Sets] : ℕ →  Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
-- [Sets^_,Sets] k = [Sets^ k ,Sets]l lzero
[Sets^_,Sets] k = Functors (Sets^ k) Sets


-- -- currently not using this construction 
-- k-product of arbitrary category 
CatProd : ∀ {o l e} → ℕ → Category o l e → Category o l (lsuc e)
CatProd {o} {l} {e} k C = record
  { Obj = Vec (C.Obj) k
  ; _⇒_ = λ As Bs → foreach2 C._⇒_ As Bs
  ; _≈_ = λ fs gs → gen-pointwise-≈  fs gs
  ; id = λ {As} → gen-vec-id 
  ; _∘_ = gen-vec-compose 
  ; assoc = gen-vec-assoc
  ; sym-assoc = gen-vec-sym-assoc
  ; identityˡ = gen-vec-identityˡ
  ; identityʳ = gen-vec-identityʳ
  ; identity² = gen-vec-identity²
  ; equiv = equiv-gen-pointwise 
  ; ∘-resp-≈ = ∘-resp-≈
  } 
  where module C = Category C
        gen-pointwise-≈ : ∀ {k} {Xs Ys : Vec (C.Obj) k}
                      → (fs gs : foreach2 (Category._⇒_ C) Xs Ys)
                      → Set (lsuc e)
        gen-pointwise-≈  {0} {Vec.[]} {Vec.[]} (lift Data.Unit.tt) (lift Data.Unit.tt) = Lift _ ⊤
        gen-pointwise-≈  {suc _} {X ∷ Xs} {Y ∷ Ys} (f , fs) (g , gs) = (f C.≈ g) ×' gen-pointwise-≈ fs gs

        gen-vec-compose : ∀ {k} {Xs Ys Zs : Vec (C.Obj) k} 
                          → foreach2 (Category._⇒_ C) Ys Zs → foreach2 (Category._⇒_ C) Xs Ys 
                          → foreach2 (Category._⇒_ C) Xs Zs
        gen-vec-compose {0} {Vec.[]} {Vec.[]} {Vec.[]} (lift Data.Unit.tt) (lift Data.Unit.tt) = lift Data.Unit.tt
        gen-vec-compose {suc _} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} (f , fs) (g , gs) = (Category._∘_ C f g) , (gen-vec-compose fs gs) 

        gen-vec-id : ∀ {k} {As : Vec (C.Obj) k} → foreach2 (C._⇒_) As As
        gen-vec-id {As = Vec.[]} = lift Data.Unit.tt
        gen-vec-id {As = A ∷ As} = Category.id C , gen-vec-id 

        
        gen-vec-assoc : ∀ {k} {Xs Ys Zs Ws : Vec (C.Obj) k}
                {f : foreach2 (C._⇒_) Xs Ys} {g : foreach2 (C._⇒_) Ys Zs} {h : foreach2 (C._⇒_) Zs Ws} 
                → gen-pointwise-≈ (gen-vec-compose (gen-vec-compose h g) f) (gen-vec-compose h (gen-vec-compose g f))
        gen-vec-assoc {0} {Vec.[]} {Vec.[]} {Vec.[]} {Vec.[]} = lift Data.Unit.tt
        gen-vec-assoc {suc _} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {W ∷ Ws} = (Category.assoc C) , gen-vec-assoc 

        gen-vec-sym-assoc : ∀ {k} {Xs Ys Zs Ws : Vec (C.Obj) k}
                              {f : foreach2 (C._⇒_) Xs Ys} {g : foreach2 (C._⇒_) Ys Zs}
                              {h : foreach2 (C._⇒_) Zs Ws} 
                            → gen-pointwise-≈ (gen-vec-compose h (gen-vec-compose g f))
                                              (gen-vec-compose (gen-vec-compose h g) f)
        gen-vec-sym-assoc {0} {Vec.[]} {Vec.[]} {Vec.[]} {Vec.[]} = lift Data.Unit.tt
        gen-vec-sym-assoc {suc _} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {W ∷ Ws} = (Category.sym-assoc C) , gen-vec-sym-assoc 

        gen-vec-identityˡ : ∀ {k} {As Bs : Vec (C.Obj) k} {f : foreach2 (C._⇒_) As Bs} 
                            → gen-pointwise-≈ (gen-vec-compose gen-vec-id f) f
        gen-vec-identityˡ {0} {Vec.[]} {Vec.[]}  = lift Data.Unit.tt 
        gen-vec-identityˡ {suc _} {X ∷ Xs} {Y ∷ Ys} = C.identityˡ , gen-vec-identityˡ 

        gen-vec-identityʳ : ∀ {k} {As Bs : Vec C.Obj k} {f : foreach2 C._⇒_ As Bs} 
                            → gen-pointwise-≈ (gen-vec-compose f gen-vec-id) f
        gen-vec-identityʳ {0} {Vec.[]} {Vec.[]}  = lift Data.Unit.tt 
        gen-vec-identityʳ {suc _} {X ∷ Xs} {Y ∷ Ys} = C.identityʳ , gen-vec-identityʳ

        gen-vec-identity² : ∀ {k} {As : Vec (Category.Obj C) k} 
                            → gen-pointwise-≈ (gen-vec-compose gen-vec-id gen-vec-id) (gen-vec-id {k} {As})
        gen-vec-identity² {0} {Vec.[]}  = lift Data.Unit.tt 
        gen-vec-identity² {suc _} {Y ∷ Ys} = C.identity² , gen-vec-identity²

        ∘-resp-≈ : ∀ {k} {Xs Ys Zs : Vec (Category.Obj C) k} 
                   {f h : foreach2 (Category._⇒_ C) Ys Zs} {g i : foreach2 (Category._⇒_ C) Xs Ys} 
                   → gen-pointwise-≈ f h → gen-pointwise-≈ g i 
                   → gen-pointwise-≈ (gen-vec-compose f g) (gen-vec-compose h i)
        ∘-resp-≈ {zero} {Vec.[]} {Vec.[]} {Vec.[]} _ _ = lift Data.Unit.tt
        ∘-resp-≈ {suc k} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} (f≈h , fs≈hs) (g≈i , gs≈is) = (C.∘-resp-≈ f≈h g≈i) , (∘-resp-≈ fs≈hs gs≈is) 


        -- generic pointwise equivalence for product categories is an equivalence relation
        equiv-gen-pointwise : ∀ {k} {As Bs : Vec (C.Obj) k} 
                                → IsEquivalence (gen-pointwise-≈ {k} {As} {Bs})
        equiv-gen-pointwise = record { refl = refl ; sym = sym ; trans = trans }
              where refl : ∀ {k} {As Bs} →  Reflexive (gen-pointwise-≈ {k} {As} {Bs})
                    refl {.0} {Vec.[]} {Vec.[]} = lift Data.Unit.tt
                    refl {.(suc _)} {A ∷ As} {B ∷ Bs} = (Category.Equiv.refl C) , refl
                    sym : ∀ {k} {As Bs : Vec (C.Obj) k} → Symmetric (gen-pointwise-≈  {k} {As} {Bs})
                    sym {.0} {Vec.[]} {Vec.[]}  _ = lift Data.Unit.tt
                    sym {.(suc _)} {A ∷ As} {B ∷ Bs} (f≈g , fs≈gs) = Category.Equiv.sym C f≈g , sym fs≈gs 
                    trans : ∀ {k} {As Bs : Vec (C.Obj) k} → Transitive (gen-pointwise-≈ {k} {As} {Bs})
                    trans {.0} {Vec.[]} {Vec.[]}  _ _  = lift Data.Unit.tt
                    trans {.(suc _)} {A ∷ As} {B ∷ Bs} (f≈g , fs≈gs) (g≈h , g≈hs) = (Category.Equiv.trans C f≈g g≈h) , (trans fs≈gs g≈hs)










mkIdNatTr : ∀ {o l e} {o' l' e'} {C : Category o l e} {D : Category o' l' e'} 
          → (F G : Functor C D)
          → F ≡ G 
          → NaturalTransformation F G 
mkIdNatTr F .F ≡.refl = idNaturalTransformation F

mkIdNatTr' : ∀ {k} → (F : Functor (Sets^ k ) (Sets ))
           → NaturalTransformation F F 
mkIdNatTr' {k} F = idNaturalTransformation F 


-- product of two categories 
_×Cat_ : ∀ {o l e} {o' l' e'} 
         → (C : Category o l e) → (D : Category o' l' e')
         → Category (o ⊔ o') (l ⊔ l') (e ⊔ e')
C ×Cat D = record
  { Obj = C.Obj ×' D.Obj
  ; _⇒_ = λ { (c , d) (c' , d') → (c C.⇒ c') ×' (d D.⇒ d') }
  ; _≈_ = λ { (f , g) (f' , g') → (f C.≈ f') ×' (g D.≈ g') }
  ; id = C.id , D.id
  ; _∘_ = λ { (f , g) (f' , g') → (f C.∘ f') , (g D.∘ g') }
  ; assoc = C.assoc , D.assoc
  ; sym-assoc = C.sym-assoc , D.sym-assoc
  ; identityˡ = C.identityˡ , D.identityˡ
  ; identityʳ = C.identityʳ , D.identityʳ
  ; identity² = C.identity² , D.identity²
  ; equiv = record { refl = C.Equiv.refl , D.Equiv.refl 
                   ; sym = λ { (f≈f' , g≈g') → C.Equiv.sym f≈f' , D.Equiv.sym g≈g' } 
                   ; trans = λ { (f≈f' , g≈g') (f'≈f'' , g'≈g'') → (C.Equiv.trans f≈f' f'≈f'') , (D.Equiv.trans g≈g' g'≈g'') } }
  ; ∘-resp-≈ = λ { (f≈f' , h≈h') (g≈g' , i≈i') → (C.∘-resp-≈ f≈f' g≈g') , (D.∘-resp-≈ h≈h' i≈i') } 
  } 
  where module C = Category C
        module D = Category D


-- terminal category
TCat : Category lzero lzero lzero 
TCat = record
  { Obj = ⊤
  ; _⇒_ = λ t t' → ⊤
  ; _≈_ = λ f g → ⊤
  ; id = Data.Unit.tt
  ; _∘_ = λ _ _ → Data.Unit.tt
  ; assoc = Data.Unit.tt
  ; sym-assoc = Data.Unit.tt
  ; identityˡ = Data.Unit.tt
  ; identityʳ = Data.Unit.tt
  ; identity² = Data.Unit.tt
  ; equiv = record { refl = Data.Unit.tt
                   ; sym = λ _ → Data.Unit.tt
                   ; trans = λ _ _ → Data.Unit.tt }
  ; ∘-resp-≈ = λ _ _ → Data.Unit.tt
  } 

-- terminal category with arbitrary levels
TCatl : ∀ {o l e} → Category o l e 
TCatl = record
  { Obj = Lift _ ⊤
  ; _⇒_ = λ t t' → Lift _ ⊤
  ; _≈_ = λ f g → Lift _ ⊤
  ; id = lift Data.Unit.tt
  ; _∘_ = λ _ _ → lift Data.Unit.tt
  ; assoc = lift Data.Unit.tt
  ; sym-assoc = lift Data.Unit.tt
  ; identityˡ = lift Data.Unit.tt
  ; identityʳ = lift Data.Unit.tt
  ; identity² = lift Data.Unit.tt
  ; equiv = record { refl = lift Data.Unit.tt
                   ; sym = λ _ → lift Data.Unit.tt
                   ; trans = λ _ _ → lift Data.Unit.tt }
  ; ∘-resp-≈ = λ _ _ → lift Data.Unit.tt
  } 


-- n-ary product of categories using TCat and ×Cat 
CatProdRec : ∀ {o l e} → ℕ → Category o l e → Category o l (e ⊔ o)
CatProdRec zero C = TCatl
CatProdRec (suc n) C = C ×Cat CatProdRec n C 


-- Functor into terminal Category
!One : ∀ {o l e o' l' e'} → (C : Category o l e) → Functor C (One {o'} {l'} {e'})
!One C = record
  { F₀ = λ x → lift Data.Unit.tt
  ; F₁ = λ f → lift Data.Unit.tt
  ; identity = lift Data.Unit.tt
  ; homomorphism = lift Data.Unit.tt
  ; F-resp-≈ = λ _ → lift Data.Unit.tt
  } 


-- use library definition for n-ary products
ProdRec : ∀ {o l e} → ℕ → Category o l e → Category o l (e ⊔ o)
ProdRec zero C = One
ProdRec (suc n) C = Product C (ProdRec n C)


-- convert Sets^n into a recursively defined n-ary product of categories 
Sets^→ProdRec : ∀ n → Functor  (Sets^ n) (ProdRec n Sets)
Sets^→ProdRec zero = !One (Sets^ zero)
Sets^→ProdRec (suc n) = (idF ⁂ Sets^→ProdRec n) ∘F (Sets^decompose n) 




-- turn a vector of sets into a vector of 0-ary functors
to0Functors : ∀ {k} → Vec Set k → Vec (Functor (Sets^ zero) Sets) k
to0Functors = vmap ConstF 

toConstNats : ∀ {k} {As Bs : Vec Set k} → VecFSpace As Bs → foreach2 (NaturalTransformation) (to0Functors As) (to0Functors Bs)
toConstNats fnil = lift Data.Unit.tt
toConstNats (fcons f fs) = (ConstNat f) , toConstNats fs 

Sets→0Functors : Functor Sets ([Sets^ 0 ,Sets])
Sets→0Functors = record
  { F₀ = ConstF
  ; F₁ = ConstNat
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≈ = λ f≈g → f≈g
  } 
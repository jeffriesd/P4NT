-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}



module SetCats where

open import Relation.Binary using (IsEquivalence ; Reflexive ; Transitive ; Symmetric)
-- open TypeExpr
-- open _≀_⊢_
-- open NestedSyntax6.TypeContext
-- open import NestedSyntax6

open import Categories.Category 
open import Categories.Category.Instance.One
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.Category.Construction.Functors using (Functors ; evalF)
open import Categories.Category.Product using (Product ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_) 
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
-- open import Data.Nat using (ℕ ; _≤_ )
-- open ℕ
-- open _≤_

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)

open import Data.Unit using (⊤ ; tt) 
open import Data.Empty renaming (⊥ to ⊥')
open import Data.Vec using (Vec ; [] ; _∷_; replicate) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_ ; const to constf)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning
open import Data.Product renaming (_×_ to _×'_)
open import Data.Sum hiding ([_,_])
open import Data.Sum.Properties using (inj₂-injective)

open import Utils using (foreach2 ; vhead ; vtail ; ×'-cong ; big⊤ ; bigtt) 
------------------------------- stdlib uses Set _ here



import Categories.NaturalTransformation.NaturalIsomorphism as NI 
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
import Categories.Morphism.Reasoning as MR

private 
  variable 
    o l e o' l' e' o'' l'' e'' : Level 
    C : Category o l e
    D : Category o' l' e'

-- module C = Category C 



-------------------------------------------------------
-- Category of sets
-------------------------------------------------------

-- extensional equality of functions

_≡-ext_ : ∀ {l} {A B : Set l} → (f g : A → B) → Set l
f ≡-ext g = ∀ {x} → f x ≡ g x 


Setsl : ∀ o → Category (lsuc o) o o
Setsl o = record
  { Obj       = Set o
  ; _⇒_       = λ A B → (A → B)
  ; _≈_       = λ f g → f ≡-ext g 
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


funcprod : ∀ {A B C D : Set} → (A → B) ×' (C → D) → (A ×' C) → (B ×' D) 
funcprod (f , g) (x , y) = f x , g y 

SetProd : Functor (Product Sets Sets) Sets
SetProd = record
  { F₀ = λ { (A , B)  → A ×' B }
  ; F₁ = funcprod
  ; identity = ≡.refl
  ; homomorphism = ≡.refl
  ; F-resp-≈ = λ { (f≈h , g≈i) → ×'-cong f≈h g≈i } 
  } 

-------------------------------------------------------



-- -- Convert VecFSpace , Sets^ , etc. to use generic VecCat construction 
-- -- function space between two vectors of Sets
-- data VecFSpace {l : Level} : ∀ {k : ℕ} → Vec (Set l) k → Vec (Set l) k → Set l where
--   tt : VecFSpace Vec.[] Vec.[]
--   : , ∀ {k : ℕ} {As Bs : Vec (Set l) k} {A B : Set l} → (f : A → B) → VecFSpace As Bs → VecFSpace (A ∷ As) (B ∷ Bs)

VecFSpace : ∀ {k : ℕ} → Vec (Set) k → Vec (Set) k → Set 
VecFSpace Xs Ys = foreach2 (λ X Y → X → Y) Xs Ys 



-------------------------------------------------------
-- Constant functor
-------------------------------------------------------
-- 
-- NOTE - these are already defined in 
-- Categories.Functor.Construction.Constant 

open import Categories.Functor.Construction.Constant public renaming (const to ConstF ; constNat to ConstNat)

-- -- just renaming library version 
-- ConstF : ∀ {o l e} {o' l' e'} {C : Category o l e}
--            {D : Category o' l' e'} (d : Category.Obj D) → Functor C D
-- ConstF {D = D} d = const d
-- 
-- -- just renaming library version 
-- ConstNat : ∀ {o l e} {o' l' e'} {C : Category o l e}
--            {D : Category o' l' e'} {d d' : Category.Obj D}
--            → (Category._⇒_ D) d d'
--            → NaturalTransformation (ConstF {C = C} {D} d) (ConstF {C = C} {D} d')
-- ConstNat {D = D} {d} {d'} f = constNat f

∁onstF⇒ConstF∘G : ∀ (C : Category o l e) 
             → {C' : Category o' l' e'} {C'' : Category o'' l'' e''}
             → (G : Functor C'' C')
             → {c : Category.Obj C}
             → NaturalTransformation {C = C''} {D = C} (ConstF c) ((ConstF c) ∘F G)
∁onstF⇒ConstF∘G C G = record { η = λ X → Category.id C ; commute = λ f → MR.id-comm-sym C ; sym-commute = λ f → MR.id-comm C } 

∁onstF∘G⇒ConstF : ∀ (C : Category o l e) 
             → {C' : Category o' l' e'} {C'' : Category o'' l'' e''}
             → (G : Functor C'' C')
             → {c : Category.Obj C}
             → NaturalTransformation {C = C''} {D = C} ((ConstF c) ∘F G) (ConstF c) 
∁onstF∘G⇒ConstF C G = record { η = λ _ → Category.id C ; commute = λ f → MR.id-comm-sym C ; sym-commute = λ f → MR.id-comm C } 


-- C'' -const-> C 
-- ≃ 
-- C'' --> C' -const-> C
ConstF-∘-≃ : ∀ (C : Category o l e) 
             → {C' : Category o' l' e'} {C'' : Category o'' l'' e''}
             → (G : Functor C'' C')
             → {c : Category.Obj C}
             → _≃_ {C = C''} {D = C}  (ConstF c) ((ConstF c) ∘F G)
ConstF-∘-≃ C G = record { F⇒G = ∁onstF⇒ConstF∘G C G ; F⇐G = ∁onstF∘G⇒ConstF C G ; iso = λ X → record { isoˡ = Category.identity² C ; isoʳ = Category.identity² C } }






-------------------------------------------------------

-------------------------------------------------------
-- Functor category [Sets,Sets]
-------------------------------------------------------


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
{-# WARNING_ON_USAGE idNaturalTransformation "use idnat isntead" #-}


-- generic functor category construction 
-- -- morphisms in the functor category (natural transformations)
-- -- are considered equivalent when they are equivalent on all components in 
-- -- the target category D. 
[[_,_]] : ∀ {o l e o' l' e'} → Category o l e → Category o' l' e' → Category (o ⊔ l ⊔ e ⊔ o' ⊔ l' ⊔ e') (o ⊔ l ⊔ l' ⊔ e') (o ⊔ e') 
[[ C , D ]] = Functors C D


-- k-ary product category of C, where objects are vectors of C.Obj
module VecCat {o l e : Level} (C : Category o l e) where 

  private module C = Category C

  pointwise-Vec-≈ : ∀ {k} {Xs Ys : Vec C.Obj k} → (gs gs' : foreach2 C._⇒_ Xs Ys) → Set e
  pointwise-Vec-≈ {zero} {[]} {[]} _ _ = big⊤
  pointwise-Vec-≈ {suc k} {X ∷ Xs} {Y ∷ Ys} (g , gs) (g' , gs') = g C.≈ g' ×' pointwise-Vec-≈ gs gs'

  idVec : ∀ {k : ℕ} → (Cs : Vec C.Obj k) → foreach2 C._⇒_ Cs Cs
  idVec [] = bigtt
  idVec (c ∷ cs) = C.id , idVec cs

  composeVecs-gen : ∀ {k : ℕ} {Xs Ys Zs : Vec C.Obj k} 
                    → foreach2 C._⇒_ Ys Zs → foreach2 C._⇒_ Xs Ys 
                    → foreach2 C._⇒_ Xs Zs
  composeVecs-gen {0} {[]} {[]} {[]} _ _ = bigtt
  composeVecs-gen {suc k} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} (f , fs) (g , gs) = (f C.∘ g) , (composeVecs-gen fs gs)

  _∘Vec_ : ∀ {k : ℕ} {Xs Ys Zs : Vec C.Obj k} 
                    → foreach2 C._⇒_ Ys Zs → foreach2 C._⇒_ Xs Ys 
                    → foreach2 C._⇒_ Xs Zs
  _∘Vec_ = composeVecs-gen


  composeVecs-assoc : ∀ {k : ℕ}
                        {Xs Ys Zs Ws : Vec (Category.Obj C) k}
                        (fs : foreach2 (Category._⇒_ C) Xs Ys)
                        (gs : foreach2 (Category._⇒_ C) Ys Zs)
                        (hs : foreach2 (Category._⇒_ C) Zs Ws) →
                      pointwise-Vec-≈ (composeVecs-gen (composeVecs-gen hs gs) fs)
                      (composeVecs-gen hs (composeVecs-gen gs fs))
  composeVecs-assoc {0} {[]} {[]} {[]} {[]} _ _ _ = bigtt
  composeVecs-assoc {suc k} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {W ∷ Ws} (f , fs) (g , gs) (h , hs) = C.assoc , (composeVecs-assoc fs gs hs) 

  composeVecs-sym-assoc : ∀ {k : ℕ}
                        {Xs Ys Zs Ws : Vec (Category.Obj C) k}
                        (fs : foreach2 (Category._⇒_ C) Xs Ys)
                        (gs : foreach2 (Category._⇒_ C) Ys Zs)
                        (hs : foreach2 (Category._⇒_ C) Zs Ws) →
                      pointwise-Vec-≈ (composeVecs-gen hs (composeVecs-gen gs fs))
                      (composeVecs-gen (composeVecs-gen hs gs) fs)
  composeVecs-sym-assoc {0} {[]} {[]} {[]} {[]} bigtt bigtt bigtt = bigtt 
  composeVecs-sym-assoc {suc k} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {W ∷ Ws} (f , fs) (g , gs) (h , hs) = C.sym-assoc , (composeVecs-sym-assoc fs gs hs) 


  composeVecs-identityˡ : ∀ {k : ℕ}
                            {Xs Ys : Vec (Category.Obj C) k}
                          → (fs : foreach2 (Category._⇒_ C) Xs Ys) 
                          → pointwise-Vec-≈ (composeVecs-gen (idVec Ys) fs) fs
  composeVecs-identityˡ {0} {[]} {[]} _ = bigtt
  composeVecs-identityˡ {suc k} {X ∷ Xs} {Y ∷ Ys} (f , fs) = C.identityˡ , composeVecs-identityˡ fs 

  composeVecs-identityʳ : ∀ {k : ℕ}
                            {Xs Ys : Vec (Category.Obj C) k}
                          → (fs : foreach2 (Category._⇒_ C) Xs Ys) 
                          → pointwise-Vec-≈ (composeVecs-gen fs (idVec Xs)) fs
  composeVecs-identityʳ {0} {[]} {[]} _ = bigtt
  composeVecs-identityʳ {suc k} {X ∷ Xs} {Y ∷ Ys} (f , fs) = C.identityʳ , composeVecs-identityʳ fs 

  composeVecs-identity² : ∀ {k : ℕ}
                          → (Xs : Vec (Category.Obj C) k) 
                          → pointwise-Vec-≈ (composeVecs-gen (idVec Xs) (idVec Xs)) (idVec Xs)
  composeVecs-identity² [] = bigtt
  composeVecs-identity² (X ∷ Xs) = C.identity² , (composeVecs-identity² Xs) 

  equiv-pointwise-Vec-≈ : ∀ {k : ℕ}
                          {Xs Ys : Vec (Category.Obj C) k} 
                          → IsEquivalence (pointwise-Vec-≈ {k} {Xs} {Ys})
  equiv-pointwise-Vec-≈ = record { refl = λ {fs} → refl fs ; sym = λ {gs} {hs} gs≈hs → sym gs hs gs≈hs ; trans = λ {fs gs hs} fs≈gs gs≈hs → trans fs gs hs fs≈gs gs≈hs } 
      where refl : ∀ {k} {Xs Ys : Vec (Category.Obj C) k}
                   → (fs : foreach2 (Category._⇒_ C) Xs Ys) 
                   → pointwise-Vec-≈ fs fs
            refl {zero} {[]} {[]} fs = bigtt
            refl {suc k} {X ∷ Xs} {Y ∷ Ys} (f , fs) = C.Equiv.refl , refl fs 
            sym : ∀ {k} {Xs Ys : Vec (Category.Obj C) k} 
                  → (gs hs : foreach2 (Category._⇒_ C) Xs Ys) 
                  → (gs≈hs : pointwise-Vec-≈ gs hs) 
                  → pointwise-Vec-≈ hs gs
            sym {zero} {[]} {[]}  _ _ _ = bigtt
            sym {suc k} {X ∷ Xs} {Y ∷ Ys} (g , h) (gs , hs) (g≈h , gs≈hs) = (C.Equiv.sym g≈h) , (sym h hs gs≈hs) 
            trans : ∀ {k} {Xs Ys : Vec (Category.Obj C) k} 
                    → (fs gs hs : foreach2 (Category._⇒_ C) Xs Ys) 
                    → (fs≈gs : pointwise-Vec-≈ fs gs) 
                    → (gs≈hs : pointwise-Vec-≈ gs hs) 
                    → pointwise-Vec-≈ fs hs
            trans {zero} {[]} {[]} _ _ _ _ _ = bigtt
            trans {suc k} {X ∷ Xs} {Y ∷ Ys} (f , fs) (g , gs) (h , hs) (f≈g , fs≈gs) (g≈h , gs≈hs) = (C.Equiv.trans f≈g g≈h) , (trans fs gs hs fs≈gs gs≈hs) 

  composeVecs-resp : ∀ {k} {Xs Ys Zs : Vec (Category.Obj C) k}
                       {fs hs : foreach2 (Category._⇒_ C) Ys Zs}
                       {gs is : foreach2 (Category._⇒_ C) Xs Ys} 
                      → (fs≈hs : pointwise-Vec-≈ fs hs) 
                      → (gs≈is : pointwise-Vec-≈ gs is) 
                      → pointwise-Vec-≈ (composeVecs-gen fs gs) (composeVecs-gen hs is)
  composeVecs-resp {k} {[]} {[]} {[]} _ _ = bigtt
  composeVecs-resp {k} {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {f , fs} {h , hs} {g , gs} {i , is} (f≈h , fs≈hs) (g≈i , gs≈is)  = (C.∘-resp-≈ f≈h g≈i) , (composeVecs-resp fs≈hs gs≈is) 



  Cat^ : ℕ → Category o l e
  Cat^ k = record
    { Obj = Vec C.Obj k
    ; _⇒_ = foreach2 C._⇒_
    ; _≈_ = pointwise-Vec-≈
    ; id = λ {cs} → idVec cs
    ; _∘_ = composeVecs-gen
    ; assoc = λ {Xs} {Ys} {Zs} {Ws} {fs} {gs} {hs} → composeVecs-assoc fs gs hs
    ; sym-assoc = λ {Xs} {Ys} {Zs} {Ws} {fs} {gs} {hs} → composeVecs-sym-assoc fs gs hs
    ; identityˡ = λ {Xs} {Ys} {fs} → composeVecs-identityˡ fs
    ; identityʳ = λ {Xs} {Ys} {fs} → composeVecs-identityʳ fs
    ; identity² = λ {Xs} → composeVecs-identity² Xs
    ; equiv = λ {Xs} {Ys} → equiv-pointwise-Vec-≈
    ; ∘-resp-≈ = λ {Xs} {Ys} {Zs} {f h} {g i} f≈h g≈i → composeVecs-resp f≈h g≈i
    }

  C^ : ℕ → Category o l e
  C^ k = Cat^ k 

  C^head : ∀ (n : ℕ) → Functor (C^ (suc n)) C
  C^head n = record
      { F₀ = λ Xs → vhead Xs
      ; F₁ = λ { {X ∷ Xs} {Y ∷ Ys} (f , fs) → f }
      ; identity = λ { {X ∷ Xs} → C.Equiv.refl } 
      ; homomorphism = λ { {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {f , fs} {g , gs} → C.Equiv.refl } 
      ; F-resp-≈ = λ { {X ∷ Xs} {Y ∷ Ys} {f , fs} {g , gs} (f≈g , fs≈gs) → f≈g } 
      } 

  C^tail : ∀ (n : ℕ) → Functor (C^ (suc n)) (C^ n)
  C^tail n = record
    { F₀ = λ Xs → vtail Xs
    ; F₁ = λ { {X ∷ Xs} {Y ∷ Ys} (f , fs) → fs  }
    ; identity = λ { {X ∷ Xs} → Functor.identity (idF {C = C^ n}) } 
    ; homomorphism = λ { {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {f , fs} {g , gs} → Functor.homomorphism (idF {C = C^ n}) }
    ; F-resp-≈ = λ { {X ∷ Xs} {Y ∷ Ys} {f , fs} {g , gs} (f≈g , fs≈gs) → fs≈gs }
    } 

  C^cons : ∀ (n : ℕ) → Functor (Product C (C^ n)) (C^ (suc n))
  C^cons n = record
    { F₀ = λ { (X , Xs) → X ∷ Xs }
    ; F₁ = λ { (f , fs) → (f , fs) }
    ; identity = λ { {A , As} → C.Equiv.refl , Functor.identity (idF {C = C^ n}) }
    ; homomorphism = (λ { {A , As} {B , Bs} {C , Cs} {f , fs} {g , gs} → C.Equiv.refl  , (Functor.homomorphism (idF {C = C^ n})) }) 
    ; F-resp-≈ = λ { {A , As} {B , Bs} {f , fs} {g , gs} (f≈g , fs≈gs) → f≈g , fs≈gs  }
    } 

  C^decompose : ∀ (n : ℕ) → Functor (C^ (suc n)) (Product C (C^ n))
  C^decompose n = C^head n ※ C^tail n 

open VecCat


-- compositinon of vectors of functions 
_∘SetVec_ : ∀ {k} → {As Bs Cs : Vec (Set) k} →
                VecFSpace Bs Cs → VecFSpace As Bs → VecFSpace As Cs
_∘SetVec_ =  _∘Vec_  Sets

makeIdTuple : ∀ {k : ℕ} →  (Xs : Vec Set k) → VecFSpace Xs Xs
makeIdTuple = idVec Sets

Sets^ : ℕ → Category (lsuc lzero) lzero lzero
Sets^ k = Cat^ Sets k

Sets^head : ∀ (n : ℕ) → Functor (Sets^ (suc n)) Sets
Sets^head = C^head Sets

Sets^tail : ∀ (n : ℕ) → Functor (Sets^ (suc n)) (Sets^ n)
Sets^tail = C^tail Sets

Sets^cons : ∀ (n : ℕ) → Functor (Product Sets (Sets^ n)) (Sets^ (suc n))
Sets^cons = C^cons Sets

Sets^decompose : ∀ (n : ℕ) → Functor (Sets^ (suc n)) (Product Sets (Sets^ n))
Sets^decompose = C^decompose Sets

{-
Currently not using universe-polymorphic categories  of sets 

Sets^l : ℕ → (l : Level) → Category (lsuc l) (l) (l)
Sets^l k l = Cat^ (Setsl l) k


[Sets,Sets]l : ∀ {o} → Category (lsuc o) (lsuc o) (lsuc o)
[Sets,Sets]l {o} = Functors (Setsl o) (Setsl o)

-- k-ary functor category, polymorphic in universe level 
[Sets^_,Sets]l : ℕ → (o : Level) → Category (lsuc o) (lsuc o) (lsuc o)
[Sets^_,Sets]l k o = Functors (Sets^l k o) (Setsl o)
-}

[Sets,Sets] : Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
[Sets,Sets] = Functors Sets Sets 


[Sets^_,Sets] : ℕ →  Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
[Sets^_,Sets] k = Functors (Sets^ k) Sets



mkIdNatTr : ∀ {o l e} {o' l' e'} {C : Category o l e} {D : Category o' l' e'} 
          → (F G : Functor C D)
          → F ≡ G 
          → NaturalTransformation F G 
mkIdNatTr F .F ≡.refl = idnat 

mkIdNatTr' : ∀ {k} → (F : Functor (Sets^ k ) (Sets ))
           → NaturalTransformation F F 
mkIdNatTr' {k} F = idnat 
{-# WARNING_ON_USAGE mkIdNatTr' "use idnat instead" #-}


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
  ; id = tt
  ; _∘_ = λ _ _ → tt
  ; assoc = tt
  ; sym-assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; identity² = tt
  ; equiv = record { refl = tt
                   ; sym = λ _ → tt
                   ; trans = λ _ _ → tt }
  ; ∘-resp-≈ = λ _ _ → tt
  } 

-- terminal category with arbitrary levels
TCatl : ∀ {o l e} → Category o l e 
TCatl = record
  { Obj = big⊤
  ; _⇒_ = λ t t' → big⊤
  ; _≈_ = λ f g → big⊤
  ; id = bigtt
  ; _∘_ = λ _ _ → bigtt
  ; assoc = bigtt
  ; sym-assoc = bigtt
  ; identityˡ = bigtt
  ; identityʳ = bigtt
  ; identity² = bigtt
  ; equiv = record { refl = bigtt
                   ; sym = λ _ → bigtt
                   ; trans = λ _ _ → bigtt }
  ; ∘-resp-≈ = λ _ _ → bigtt
  } 


-- n-ary product of categories using TCat and ×Cat 
CatProdRec : ∀ {o l e} → ℕ → Category o l e → Category o l (e ⊔ o)
CatProdRec zero C = TCatl
CatProdRec (suc n) C = C ×Cat CatProdRec n C 


-- Functor into terminal Category
!One : ∀ {o l e o' l' e'} → (C : Category o l e) → Functor C (One {o'} {l'} {e'})
!One C = record
  { F₀ = λ x → lift tt
  ; F₁ = λ f → lift tt
  ; identity = lift tt
  ; homomorphism = lift tt
  ; F-resp-≈ = λ _ → lift tt
  } 


-- use library definition for n-ary products
ProdRec : ∀ {o l e} → ℕ → Category o l e → Category o l (e ⊔ o)
ProdRec zero C = One
ProdRec (suc n) C = Product C (ProdRec n C)


-- convert Sets^n into a recursively defined n-ary product of categories 
Sets^→ProdRec : ∀ n → Functor  (Sets^ n) (ProdRec n Sets)
Sets^→ProdRec zero = !One (Sets^ zero)
Sets^→ProdRec (suc n) = (idF ⁂ Sets^→ProdRec n) ∘F (Sets^decompose n) 


module 0Functors {o l e : Level} (C : Category o l e) where 
    open VecCat

    private module C = Category C 
    -- turn a vector of sets into a vector of 0-ary functors

    to0FunctorsGen : ∀ {k} → Vec (C.Obj) k → Vec (Functor (Cat^ C zero) C) k
    to0FunctorsGen = vmap ConstF 


    toConstNatsGen : ∀ {k} {As Bs : Vec C.Obj k} → ((Cat^ C k) [ As , Bs ]) → foreach2 (NaturalTransformation) (to0FunctorsGen As) (to0FunctorsGen Bs)
    toConstNatsGen {As = []} {[]} (bigtt) = bigtt
    toConstNatsGen {As = A ∷ As} {B ∷ Bs} (g , gs) = (ConstNat g) , (toConstNatsGen gs)

    C⇒0Functors : Functor C ([[ Cat^ C zero , C ]]) 
    C⇒0Functors = record
        { F₀ = ConstF
        ; F₁ = ConstNat
        ; identity =  C.Equiv.refl 
        ; homomorphism = C.Equiv.refl
        ; F-resp-≈ = λ f≈g → f≈g
        } 

    0Functors⇒C : Functor [[ Cat^ C zero , C ]] C 
    0Functors⇒C = evalF (Cat^ C zero) C []

open 0Functors 

-- 0Functors constructs for Sets 
to0Functors : ∀ {k} → Vec Set k → Vec (Functor (Sets^ zero) Sets) k
to0Functors = to0FunctorsGen Sets -- vmap ConstF 

toConstNats : ∀ {k} {As Bs : Vec Set k} → VecFSpace As Bs → foreach2 (NaturalTransformation) (to0Functors As) (to0Functors Bs)
toConstNats = toConstNatsGen Sets

Sets→0Functors : Functor Sets ([Sets^ 0 ,Sets])
Sets→0Functors = C⇒0Functors Sets

0Functors→Sets  : Functor ([Sets^ 0 ,Sets]) Sets
0Functors→Sets = 0Functors⇒C Sets

-- Sets^decompose : ∀ (n : ℕ) → Functor (Sets^ (suc n)) (Product Sets (Sets^ n))
Sets^1→Sets : Functor (Sets^ 1) Sets
Sets^1→Sets = πˡ ∘F (Sets^decompose 0) 


-- this is really a case of 
-- overlap-× : ∀ (H : Bifunctor D₁ D₂ C) (F : Functor E D₁) (G : Functor E D₂) → Functor E C
-- overlap-× H F G = H ∘F (F ※ G)
-- from https://agda.github.io/agda-categories/Categories.Functor.Bifunctor.html
_+Set_ : ∀ (F G : Functor C Sets) → Functor C Sets 
F +Set G = SetSum ∘F (F ※ G)

_×Set_ : ∀ (F G : Functor C Sets) → Functor C Sets 
F ×Set G = SetProd ∘F (F ※ G)


×Set-distr : ∀ (F G H : Functor C Sets) 
           → NaturalTransformation (F ×Set (G +Set H)) ((F ×Set G) +Set (F ×Set H))
×Set-distr F G H = record { η = λ { X (fst , inj₁ x) → inj₁ (fst , x)
                                  ; X (fst , inj₂ y) → inj₂ (fst , y) } 
                          ; commute = λ { f {fst , inj₁ x} → ≡.refl
                                        ; f {fst , inj₂ y} → ≡.refl } 
                          ; sym-commute = λ { f {fst , inj₁ x} → ≡.refl
                                            ; f {fst , inj₂ y} → ≡.refl } } 


open Utils.≃-Reasoning
open import Categories.Category.Product.Properties using (※-distrib)
×Set-compose-distr-≃  : ∀ (F G : Functor C Sets) (H : Functor D C)
                     → ((F ×Set G) ∘F H)
                     ≃ ((F ∘F H) ×Set (G ∘F H))
×Set-compose-distr-≃ F G H =
                     begin≃
                     (SetProd ∘F (F ※ G)) ∘F H
                     ≃⟨ NI.associator H (F ※ G)  SetProd ⟩
                     SetProd ∘F ((F ※ G) ∘F H)
                     ≃⟨  SetProd NI.ⓘˡ (※-distrib Sets Sets F G H)  ⟩
                     SetProd ∘F (F ∘F H ※ G ∘F H)
                     ≃∎ 

×Set-compose-distr : ∀ (F G : Functor C Sets) (H : Functor D C)
                     → NaturalTransformation ((F ×Set G) ∘F H) ((F ∘F H) ×Set (G ∘F H))
×Set-compose-distr F G H =  NI.NaturalIsomorphism.F⇒G (×Set-compose-distr-≃ F G H)  

×Set-compose-distr-sym : ∀ (F G : Functor C Sets) (H : Functor D C)
                     → NaturalTransformation ((F ∘F H) ×Set (G ∘F H)) ((F ×Set G) ∘F H) 
×Set-compose-distr-sym F G H =  NI.NaturalIsomorphism.F⇐G (×Set-compose-distr-≃ F G H)  




-- pointwise-het-id asserts that a morphism in Sets^ k is fundamentally 
-- an identity morphism between two propositionally (but not necessarily definitionally) equal types 
open import Relation.Binary.HeterogeneousEquality using (_≅_)
import Relation.Binary.HeterogeneousEquality as Het
pointwise-het-id : ∀ {k} → {Xs Ys : Vec Set k} → (f : VecFSpace Xs Ys) → Set 
pointwise-het-id {zero} {[]} {[]} bigtt = big⊤
pointwise-het-id {suc _ } {X ∷ Xs} {Y ∷ Ys} (f , fs) = (∀ {x} → f x ≅ x) ×' pointwise-het-id fs 


pointwise-het⇒pointwise-≈ : ∀ {j} {As : Vec Set j} (gs : VecFSpace As As) → pointwise-het-id gs → (Sets^ j) Categories.Category.[ gs ≈ Category.id (Sets^ j) ] 
pointwise-het⇒pointwise-≈ {zero} {[]}  bigtt bigtt = bigtt
pointwise-het⇒pointwise-≈ {suc j} {A ∷ As} (g , gs) (gx≅x , gseq) = (Het.≅-to-≡ gx≅x) , (pointwise-het⇒pointwise-≈  gs gseq) 

open ≡.≡-Reasoning

module HetFunctorialityVec {k : ℕ} {Xs Ys : Vec Set k}
   (F : Functor (Sets^ k) Sets) 
   (fs : (Sets^ k) Categories.Category.[ Xs , Ys ]) (fid : pointwise-het-id fs)
  where 
  

  private 
    idXs : VecFSpace Xs Xs
    idXs = makeIdTuple Xs



  Fmap-id : (e : Xs ≡ Ys) → ∀ {x} → Functor.F₁ F fs x ≅ x
  Fmap-id ≡.refl {x} = 
    let 
        -- feq : (Sets^ k) Categories.category
        -- feq = Het.≅-to-≡ fid 

        fs≈id : (Sets^ k) Categories.Category.[ fs ≈ idXs ]
        fs≈id = pointwise-het⇒pointwise-≈  fs fid

        Ff≈Fid : Sets Categories.Category.[ Functor.F₁ F fs ≈ Functor.F₁ F idXs ]
        Ff≈Fid {x} = Functor.F-resp-≈ F fs≈id

        Ff≈id : Sets Categories.Category.[ Functor.F₁ F idXs ≈ idf ] 
        Ff≈id {x} = Functor.identity F 

      in Het.≡-to-≅ (≡.trans Ff≈Fid Ff≈id)





-- we can generalize this to endofunctors on any category C that supports
-- 1) a notion of heterogeneous identity morphisms f : X → Y 
-- 2) a proof that, in a context where X ≡ Y, a hetereogeneous identity f : X → X 
--    is ≈ identity morphism in C
--    
-- actually this is just a special case of
-- HetFunctorialityVec for F = KH 
module HetFunctorialityFunctors {k : ℕ} {Xs Ys : Vec Set k}
   (K : Functor [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] [Sets^ k ,Sets] )
   (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
   (fs : (Sets^ k) Categories.Category.[ Xs , Ys ]) (fid : pointwise-het-id fs)
  where 
  

  idXs : VecFSpace Xs Xs 
  idXs = Category.id (Sets^ k) {A = Xs}

  KH : Functor (Sets^ k) Sets
  KH = Functor.F₀ K H 

  -- action on objects in (Sets^ k)
  KH₀ : Vec Set k → Set 
  KH₀ = Functor.F₀ KH

  -- action on morphisms in (Sets^ k)
  KH₁ : ∀ {Xs Ys : Vec Set k} → (fs : VecFSpace Xs Ys) → (KH₀ Xs) → (KH₀ Ys)
  KH₁ = Functor.F₁ KH
  

  -- NOTE it is critical to have proof of Xs ≡ Ys
  -- in addition to proof that HFixFunctor2 H Xs ≡ HFixFunctor2 H Ys.
  -- If we only have the former proof, we can't match on it because
  -- Xs fails to unify with Ys... 
  -- 
  -- actually we don't need an additional proof of KH₀ Xs ≡ KH₀ Ys 

  open HetFunctorialityVec
  HFix-fmap-het-id : ∀ (es : Xs ≡ Ys) -- (e : KH₀ Xs ≡ KH₀ Ys)
                     → ∀ {x : KH₀ Xs} → KH₁ fs x ≅ x 
  HFix-fmap-het-id e {x} = Fmap-id KH fs fid e {x}
    -- let fs≈id : Sets^ k Categories.Category.[ fs ≈ idXs ]
    --     fs≈id = pointwise-het⇒pointwise-≈ fs fid

    --     KHfs≈KHid : Sets Categories.Category.[ KH₁ fs ≈ KH₁ idXs ] 
    --     KHfs≈KHid {x} = Functor.F-resp-≈  KH fs≈id   

    --     KHid≈id : Sets Categories.Category.[ KH₁ idXs ≈ idf ]
    --     KHid≈id {x} = Functor.identity KH
    -- 
    --  in Het.≡-to-≅ (≡.trans KHfs≈KHid KHid≈id )




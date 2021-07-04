{-# OPTIONS --allow-unsolved-metas #-} 


module HetEquality.Core where


open import Relation.Binary.HeterogeneousEquality public using (_≅_)
import Relation.Binary.HeterogeneousEquality as Het 
open import Data.Vec using (Vec ; [] ; _∷_) 
open import Utils using (_≡-ext_)
open import Function renaming (_∘_ to _∘'_) 

open import Relation.Binary.PropositionalEquality using (_≡_) 
import Relation.Binary.PropositionalEquality as ≡

-- heterogeneous, extensional equality of two morphisms of different types (different domain and codomain, potentially)
_het-≈_ : ∀ {A B C D : Set} (f : A → B) (g : C → D) → Set 
_het-≈_ {A} {B} {C} {D} f g = ∀ {x : A} {y : C} → x Het.≅ y → f x Het.≅ g y 


het-≈-trans : ∀ {A1 B1 A2 B2 A3 B3 : Set} {f1 : A1 → B1} {f2 : A2 → B2} {f3 : A3 → B3} 
              → f1 het-≈ f2
              → f2 het-≈ f3
              → A1 ≡ A2 -- → B1 ≡ B2
              → f1 het-≈ f3
-- {A} {B} {C} {D} f g h = ∀ {x : A} {y : C} → x Het.≅ y → f x Het.≅ g y 
het-≈-trans {f1 = f1} {f2} {f3} p1 p2 ≡.refl {x} {y}  _≅_.refl =
  let
      step1  : f1 x ≅ f2 y 
      step1 = p1 Het.refl 
      step2 : f2 y ≅ f3 y 
      step2 = p2 Het.refl 

      f1x≅f3y : f1 x ≅ f3 y 
      f1x≅f3y = Het.trans step1 step2
    in f1x≅f3y 



het-≈-refl : ∀ {A B : Set} {f : A → B} → f het-≈ f 
het-≈-refl Het.refl = Het.refl

het-≈-comp : ∀ {A B A' B' C C' : Set} {f : A → B} {f' : A' → B'} {g : B → C} {g' : B' → C'}
             → f het-≈ f'
             → g het-≈ g'
             → (g ∘' f) het-≈ (g' ∘' f') 
het-≈-comp f≈f' g≈g' e = g≈g' (f≈f' e) 

-- het-≈-resp-∘ : ∀ {A B A' B' C C' : Set} {f : A → B} {f' : A' → B'} {g : B → C} {g' : B' → C'}
--              → g het-≈ g'
--              → 

-- heterogeneous extensional equality implies non-het extensional equality 
het-eq⇒eq : ∀ {A B : Set} {f g : A → B} → f het-≈ g → f ≡-ext g 
het-eq⇒eq p {x} = Het.≅-to-≡ (p {x} {x} Het.refl) 






open import Data.Sum as Sum
open import Data.Product as Prod 
import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function renaming (_∘_ to _∘'_) 



open import HetEquality.Core 
import Relation.Binary.PropositionalEquality as ≡ 

import Relation.Binary.HeterogeneousEquality as Het 


module HetEquality.Utils where 


-- project out individual proofs from equality proof of pairs 
Het-eq-proj₁ : ∀ {A B : Set} {x1 y1 : A} {x2 y2 : B} → (x1 , x2) Het.≅ (y1 , y2) → x1 Het.≅ y1 
Het-eq-proj₁ Het.refl = Het.refl 
Het-eq-proj₂ : ∀ {A B : Set} {x1 y1 : A} {x2 y2 : B} → (x1 , x2) Het.≅ (y1 , y2) → x2 Het.≅ y2
Het-eq-proj₂ Het.refl = Het.refl 

Het-eq-proj₁' : ∀ {A A' B B' : Set} {x1 : A} {y1 : A'} {x2 : B} {y2 : B'} → A ≡ A' → B ≡ B' → (x1 , x2) Het.≅ (y1 , y2) → x1 Het.≅ y1 
Het-eq-proj₁' ≡.refl ≡.refl Het.refl = Het.refl 

Het-eq-proj₂' : ∀ {A A' B B' : Set} {x1 : A} {y1 : A'} {x2 : B} {y2 : B'} → A ≡ A' → B ≡ B' → (x1 , x2) Het.≅ (y1 , y2) → x2 Het.≅ y2 
Het-eq-proj₂' ≡.refl ≡.refl Het.refl = Het.refl 


-- identical types 
Het-eq-inj₁ : ∀ {A B : Set} {x y : A} → inj₁ {B = B} x ≅ inj₁ {B = B} y → x ≅ y 
Het-eq-inj₁ Het.refl = Het.refl 
Het-eq-inj₂ : ∀ {A B : Set} {x y : B} → inj₂ {A = A} x ≅ inj₂ {A = A} y → x ≅ y 
Het-eq-inj₂ Het.refl = Het.refl 

-- different types + proofs of equality 
Het-eq-inj₁' : ∀ {A A' B B' : Set} {x : A} {y : A'} → A ≡ A' → B ≡ B' → inj₁ {B = B} x ≅ inj₁ {B = B'} y → x ≅ y 
Het-eq-inj₁' ≡.refl ≡.refl Het.refl = Het.refl 

Het-eq-inj₂' : ∀ {A A' B B' : Set} {x : B} {y : B'} → A ≡ A' → B ≡ B' → inj₂ {A = A} x ≅ inj₂ {A = A'} y → x ≅ y 
Het-eq-inj₂' ≡.refl ≡.refl Het.refl = Het.refl 


{-
inj₁-het-cong : ∀ {A B A' B' C : Set} {f : A → B} {g : A' → B'} {inj : ∀ {X} → X → X ⊎ C}
                → A ≡ A'
                → B ≡ B' 
                → f het-≈ g
                → (inj ∘' f) het-≈ (inj ∘' g )
inj₁-het-cong {inj = inj} ≡.refl ≡.refl f≈g e = Het.cong inj (f≈g e) 
-}


inj₁-het-cong : ∀ {A B A' B' C C' : Set} {f : A → B} {g : A' → B'} {inj : ∀ {X} → X → X ⊎ C} {inj' : ∀ {X} → X → X ⊎ C'}
                → A ≡ A'
                → B ≡ B' 
                → (∀ {X} → inj {X} het-≈ inj' {X} )
                → f het-≈ g
                → (inj ∘' f) het-≈ (inj' ∘' g )
inj₁-het-cong {inj = inj} ≡.refl ≡.refl ei f≈g e = ei (f≈g e) 


inj₁-het-cong' : ∀ {A B A' B' C C' : Set} {x : A} {x' : B} 
                 → A ≡ B 
                 → C ≡ C'
                 → x ≅ x' 
                 → inj₁ {A = A} {B = C} x ≅ inj₁ {A = B} {B = C'} x'
inj₁-het-cong' ≡.refl ≡.refl Het.refl = Het.refl


inj₂-het-cong' : ∀ {A B C C' : Set} {x : C} {x' : C'} 
                 → A ≡ B 
                 → C ≡ C'
                 → x ≅ x' 
                 → inj₂ {A = A} {B = C} x ≅ inj₂ {A = B} {B = C'} x'
inj₂-het-cong' ≡.refl ≡.refl Het.refl = Het.refl
{-
Sum-map-het-cong : ∀ {A B A' B' C C' : Set} → {f : A → C} {f' : A' → C'} {g : B → C} {g' : B' → C'}
               → A ≡ A'
               → B ≡ B' 
               → f het-≈ f'
               → g het-≈ g' 
               → Sum.[ f , g ]
               het-≈ Sum.[ f' , g' ] 
Sum-map-het-cong ≡.refl ≡.refl f≈f' g≈g' {inj₁ x} {.(inj₁ x)} Het.refl = f≈f' Het.refl
Sum-map-het-cong ≡.refl ≡.refl f≈f' g≈g' {inj₂ y} {.(inj₂ y)} Het.refl = g≈g' Het.refl
-}

Sum-map-het-cong : ∀ {A A' B B' C C' D D' : Set} → {f : A → C} {f' : A' → C'} {g : B → D} {g' : B' → D'}
               → A ≡ A'
               → B ≡ B' 
               → C ≡ C'
               → D ≡ D'
               → f het-≈ f'
               → g het-≈ g' 
               → Sum.[ inj₁ ∘' f , inj₂ ∘' g ]
               het-≈ Sum.[ inj₁ ∘' f' , inj₂ ∘' g' ] 
Sum-map-het-cong ≡.refl ≡.refl ≡.refl ≡.refl f≈f' g≈g' {inj₁ x} {inj₁ y} e = het-≈-comp {g = inj₁} {g' = inj₁} f≈f' het-≈-refl (Het-eq-inj₁ e) 
Sum-map-het-cong ≡.refl ≡.refl ≡.refl ≡.refl f≈f' g≈g' {inj₂ x} {inj₂ y} e = het-≈-comp {g = inj₂} {g' = inj₂} g≈g' het-≈-refl (Het-eq-inj₂ e)

Prod-map-het-cong : ∀ {A A' B B' C C' D D' : Set} {f : A → C} {f' : A' → C'} {g : B → D} {g' : B' → D'}
               → A ≡ A'
               → B ≡ B' 
               → C ≡ C'
               → D ≡ D' 
               → f het-≈ f'
               → g het-≈ g' 
               → Prod.map f g 
               het-≈ Prod.map f' g' 
Prod-map-het-cong ≡.refl ≡.refl ≡.refl ≡.refl f≈f' g≈g' {x1 , x2} {y1 , y2} e = Het.cong₂ _,_ (f≈f' (Het-eq-proj₁ e)) (g≈g' (Het-eq-proj₂ e)) 



pair-het : ∀ {A B A' B' : Set} {x : A} {x' : A'} {y : B} {y' : B'}
           → x ≅ y
           → x' ≅ y' 
           → (x , x') ≅ (y , y') 
pair-het Het.refl Het.refl = Het.refl


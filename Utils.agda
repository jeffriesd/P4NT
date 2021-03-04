
open import Data.Nat
open import Data.Vec
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Product renaming (_×_ to _×'_) 
open import Data.Unit




open import Data.Bool using (if_then_else_; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Data.Empty using (⊥)

module Utils where

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)


vhead : ∀ {l} {A : Set l} {n : ℕ}  → Vec A (suc n) → A 
vhead (x ∷ xs) = x

vtail : ∀ {l} {A : Set l} {n : ℕ}  → Vec A (suc n) → Vec A n
vtail (x ∷ xs) = xs


exFalso : ∀ {l} {A : Set l} → ⊥ → A
exFalso ()

exFalso' : ∀ {A B : Set} {x : A} → ¬ (x ≡ x) → B
exFalso' x≢x = exFalso (x≢x ≡.refl)

eq-elim : ∀ {l} {A B : Set l} → A ≡ B → A → B
eq-elim ≡.refl x = x

eq-elim-map1 : ∀ {l} {A B C : Set l} → A ≡ B → (B → C) → A → C
eq-elim-map1 ≡.refl f x = f x

eq-elim-map2 : ∀ {l} {A B C : Set l} → A ≡ B → (A → C) → B → C
eq-elim-map2 ≡.refl f x = f x


data emptyset (l : Level) : Set l where


-- if both parts two pairs are equal, the pairs are equal
×'-cong : ∀ {l} {A B : Set l} {x1 x2 : A} {y1 y2 : B} → x1 ≡ x2 → y1 ≡ y2 → (x1 , y1) ≡ (x2 , y2)
×'-cong ≡.refl ≡.refl = ≡.refl


-- TODO generalize universe level for foreach
foreach : ∀ {n : ℕ} {A : Set}
         → (P : A → Set)
         → Vec A n → Set
foreach _ [] = ⊤
foreach P (G ∷ Gs) = P G ×' foreach P Gs

-- TODO replace occurences of foreach with this general version 
foreachl : ∀ {l} {n : ℕ} {A : Set l}
         → (P : A → Set l)
         → Vec A n → Set l
foreachl _ [] = Lift _ ⊤
foreachl P (G ∷ Gs) = P G ×' foreachl P Gs


foreach2 : ∀ {l} {r} {n : ℕ} {A B : Set l}
         → (P : A → B → Set r)
         → Vec A n → Vec B n → Set r
foreach2 _ [] [] = Lift _ ⊤
foreach2 P (A ∷ As) (B ∷ Bs) = P A B ×' foreach2 P As Bs

foreach-toVec : ∀ {n : ℕ} {A : Set} {P : A → Set} {xs : Vec A n}
                → foreach P xs
                → Vec (Σ A P) n
foreach-toVec {xs = Vec.[]} Data.Unit.tt = Vec.[]
foreach-toVec {xs = x ∷ xs} (fst , snd) = (x , fst) ∷ foreach-toVec {xs = xs} snd

foreach-preserves : ∀ {n : ℕ} {A : Set} {P Q : A → Set}
                  → (∀ (x : A) → P x → Q x)
                  → (As : Vec A n)
                  → foreach P As
                  → foreach Q As
foreach-preserves P⇒Q [] Data.Unit.tt = Data.Unit.tt
foreach-preserves P⇒Q (x ∷ xs) (P , Ps) = (P⇒Q x P) , (foreach-preserves P⇒Q xs Ps)


-- only possible Dec witness of x ≡ x is (yes ≡.refl)
decEqId : ∀ {l} {A : Set l} → (decEq : ∀ (x y : A) → Dec (x ≡ y)) → (a : A) → (decEq a a) ≡ (yes ≡.refl)
decEqId decEq a with decEq a a
... | .true because ofʸ ≡.refl = ≡.refl
... | .false because ofⁿ a≢a = exFalso (a≢a ≡.refl) 



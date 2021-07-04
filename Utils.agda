{-# OPTIONS --rewriting  #-}
-- --confluence-check #-}

open import Agda.Builtin.Equality.Rewrite

open import Data.Vec hiding ([_]) renaming (map to vmap)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Product renaming (_×_ to _×'_) 
open import Data.Sum hiding ([_,_])
open import Agda.Builtin.Unit
-- open import Agda.Builtin.Nat

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Function renaming (id to idf ; _∘_ to _∘'_)


open import Data.Bool using (if_then_else_; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Data.Empty using (⊥)


module Utils where

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_) 

_≡-ext_ : ∀ {ℓ} {A B : Set ℓ} → (f g : A → B) → Set ℓ
f ≡-ext g = ∀ {x} → f x ≡ g x 


-- subst : ∀ {a b : Level} {A : Set a} {B : A → Set b} → {x y : A} → x ≡ y → B x → B y
-- subst ≡.refl bx = bx

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

-- for non dependent functions 
cong-both : ∀ {a b : Level} {A : Set a} {B : Set b}  {f g : A → B}
           → f ≡ g → {x y : A} → x ≡ y →  f x ≡ g y
cong-both ≡.refl ≡.refl = ≡.refl

import Relation.Binary.HeterogeneousEquality as Het
subst₂-reduce : ∀ {a b l} {A : Set a} {B : Set b} (P : A → B → Set l) → {x x' : A} → {y y' : B} → (e : x ≡ x') → (e' : y ≡ y')
                → (r : P x y)
                → ≡.subst₂ P e e' r Het.≅ r 
subst₂-reduce P ≡.refl ≡.refl r = Het.refl



-- cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
-- cong f refl = refl
cong-flip : ∀ {a b c : Level} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
           → {x y : A} → x ≡ y → {z : B} →  f x z  ≡ f y z 
cong-flip f ≡.refl = ≡.refl


-- cong-ext  : ∀ {a b : Level} {A : Set a} {B : Set b}  {f g : A → B}
--            → (∀ {x} → f x ≡ g x) →  f x ≡ g y

-- congie : ∀ {a b c : Level} {A : Set a} {B : A → Set b} {C : Set c}  {f g : ∀ {x : A} → B x → C}
--            → f ≡ g → {x y : A} → x ≡ y →  f x ≡ g y
  


cong-app-impl : ∀ {a b : Level} {A : Set a} {B : A → Set b} {f g : {x : A} → B x} →
           (λ {x} → f {x}) ≡ (λ {x} → g {x}) → {x : A} → f {x} ≡ g {x}
cong-app-impl ≡.refl {x} = ≡.refl

impl-cong-app : ∀ {a} {b} {A : Set a} {B : A → Set b} {f g : {x : A} → B x} →
           (λ {x} → f {x}) ≡ (λ {x} → g {x})  → (x : A) → f {x} ≡ g {x}
impl-cong-app ≡.refl x = ≡.refl
{-# WARNING_ON_USAGE impl-cong-app "use cong-app-impl insteaD" #-}


-- cong-bothd : ∀ {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
--            f ≡ g → (x y : A) → x ≡ y → f x ≡ g y
-- cong-bothd p x y q = ? 



-- -- already defined in PropositionalEquality
-- ≢-sym : ∀ {a} {A : Set a} {x y : A} → x ≢ y → y ≢ x 
-- ≢-sym x≢y y≡x = x≢y (≡.sym y≡x) 


-- universe polymorphic unit type, to avoid having Lift _ ⊤ and lift bigtt everywhere 
data big⊤ {l : Level} : Set l where
  bigtt : big⊤


-- if both parts two pairs are equal, the pairs are equal
×'-cong : ∀ {a b} {A : Set a} {B : Set b} {x1 x2 : A} {y1 y2 : B} → x1 ≡ x2 → y1 ≡ y2 → (x1 , y1) ≡ (x2 , y2)
×'-cong = ≡.cong₂ (_,_)
-- ×'-cong ≡.refl ≡.refl = ≡.refl
-- 
×'-distr : ∀ {l} {A B C : Set l} → A ×' (B ⊎ C) → (A ×' B) ⊎ (A ×' C)
×'-distr (a , inj₁ x ) = inj₁ (a , x) 
×'-distr (a , inj₂ y ) = inj₂ (a , y) 

module foreach-module where 

        private
            variable
                a b l r : Level
                A B C : Set l

        -- [ ] TODO use variables everywhere in this submodule 


        -- [x] TODO replace occurences of foreach with this general version 
        foreach : ∀ {n : ℕ} 
                → (P : A → Set r)
                → Vec A n → Set r
        foreach P [] = big⊤ 
        foreach P (G ∷ Gs) = P G ×' foreach P Gs

        -- should be able to define a functor for this 
        -- foreachF : ∀ {k : ℕ} → Functor (Sets^ k) Sets 

         

        {-
        foreach : ∀ {n : ℕ} {A : Set}
                → (P : A → Set)
                → Vec A n → Set
        foreach = foreach {a = lzero} {b = lzero}
        -}


        foreach2 : ∀ {l} {r} {n : ℕ} {A B : Set l}
                → (P : A → B → Set r)
                → Vec A n → Vec B n → Set r
        foreach2 P [] [] = big⊤ 
        foreach2 P (x ∷ xs) (y ∷ ys) = P x y ×' foreach2 P xs ys

        foreach2→foreach : ∀ {l} {r} {n : ℕ} {A : Set l}
                → (P : A → A → Set r)
                → (xs : Vec A n)
                → foreach2 P xs xs
                → foreach (λ x → P x x) xs
        foreach2→foreach P [] bigtt = bigtt
        foreach2→foreach P (x ∷ xs) (fst , snd) = fst , (foreach2→foreach P xs snd)





        foreach2-map-≡ : ∀ {n : ℕ} 
                → (P : B → C → Set r)
                → (f : A → B) 
                → (g : A → C) 
                → (xs : Vec A n) 
                → foreach2 P (vmap f xs) (vmap g xs)
                ≡ foreach2 (λ (x y : A) → P (f x) (g y)) xs xs
        foreach2-map-≡ P f g [] = ≡.refl
        foreach2-map-≡ P f g (x ∷ xs) = ≡.cong (_×'_ (P (f x) (g x))) (foreach2-map-≡ P f g xs)
        -- THIS WORKS -- but is it useful always? because sometimes we need to pattern match on a foreach and that requires
        -- matching on Xs... and the Xs won't get rewritten so this might not work in cases with pattern matching 
        -- {-#  REWRITE foreach2-map-≡ #-}

        foreach2≡foreach : ∀ {l} {r} {n : ℕ} {A : Set l}
                → (P : A → A → Set r)
                → (xs : Vec A n)
                → foreach2 P xs xs
                ≡ foreach (λ x → P x x) xs
        foreach2≡foreach P [] = ≡.refl
        foreach2≡foreach P (x ∷ xs) = ≡.cong (_×'_ (P x x)) (foreach2≡foreach P xs) 
        -- THIS WORKS
        -- {-# REWRITE foreach2≡foreach  #-}

        -- foreach2≡foreach' : ∀ {n : ℕ}
        --         → (P : B → C → Set r)
        --         → (xs : Vec A n)
        --         → foreach2 P xs xs
        --         ≡ foreach (λ x → P x x) xs
        -- foreach2≡foreach' P [] = ≡.refl
        -- foreach2≡foreach' P (x ∷ xs) = ≡.cong (_×'_ (P x x)) (foreach2≡foreach P xs) 


        foreach2-map : ∀ {l} {r} {n : ℕ} {A B C : Set l}
                → (P : B → C → Set r)
                → (f : A → B) 
                → (g : A → C) 
                → (xs : Vec A n) 
                → foreach2 P (vmap f xs) (vmap g xs)
                → foreach2 (λ (x y : A) → P (f x) (g y)) xs xs
        foreach2-map P f g [] Pxs = bigtt
        foreach2-map P f g (x ∷ xs) (Pfgx , Pxs) = Pfgx , foreach2-map P f g xs Pxs 

        foreach2-map-from : ∀ {l} {r} {n : ℕ} {A B C : Set l}
                → (P : B → C → Set r)
                → (f : A → B) 
                → (g : A → C) 
                → (xs : Vec A n) 
                → foreach2 (λ (x y : A) → P (f x) (g y)) xs xs
                → foreach2 P (vmap f xs) (vmap g xs)
        foreach2-map-from P f g [] Pxs = bigtt
        foreach2-map-from P f g (x ∷ xs) (Pfgx , Pxs) = Pfgx , foreach2-map-from P f g xs Pxs 



        foreach2-map₂ : ∀ {l} {r} {n : ℕ} {A A' B C : Set l}
                → (P : B → C → Set r)
                → (f : A → B) 
                → (g : A' → C) 
                → (xs : Vec A n) (ys : Vec A' n)
                → foreach2 P (vmap f xs) (vmap g ys)
                → foreach2 (λ x x' → P (f x) (g x')) xs ys
        foreach2-map₂ P f g [] [] _ = bigtt
        foreach2-map₂ P f g (x ∷ xs) (y ∷ ys) (Pxy , Ps) = (Pxy , foreach2-map₂ P f g xs ys Ps)

        foreach2-map₂-from : ∀ {l} {r} {n : ℕ} {A A' B C : Set l}
                → (P : B → C → Set r)
                → (f : A → B) 
                → (g : A' → C) 
                → (xs : Vec A n) (ys : Vec A' n)
                → foreach2 (λ x x' → P (f x) (g x')) xs ys
                → foreach2 P (vmap f xs) (vmap g ys)
        foreach2-map₂-from P f g [] [] _ = bigtt
        foreach2-map₂-from P f g (x ∷ xs) (y ∷ ys) (Pxy , Ps) = (Pxy , foreach2-map₂-from P f g xs ys Ps)



        foreach2-toVec : ∀ {l} {r} {n : ℕ} {A B : Set l} {P : A → B → Set r} {xs : Vec A n} {ys : Vec B n}
                        → foreach2 P xs ys
                        → Vec (Σ[ x ∈ A ] Σ[ y ∈ B ] P x y) n
        foreach2-toVec {xs = []} {ys = []} bigtt = []
        foreach2-toVec {xs = x ∷ xs} {ys = y ∷ ys} (pxy , ps) = (x , y , pxy) ∷ (foreach2-toVec {xs = xs} {ys = ys} ps) 

        -- note we can't prove foreach2 P xs ys for arbitrary xs and ys if we only have a vector of sigmas 
        {-
        foreach2-fromVec : ∀ {l} {r} {n : ℕ} {A B : Set l} {P : A → B → Set r} {xs : Vec A n} {ys : Vec B n}
                        → Vec (Σ[ x ∈ A ] Σ[ y ∈ B ] P x y) n
                        → foreach2 P xs ys
        foreach2-fromVec {xs = []} {ys = []} [] = bigtt
        foreach2-fromVec {xs = x ∷ xs} {ys = y ∷ ys} (( x' , y' , p) ∷ ps) = {!!} , {!!}
        -}


        -- iso here 
        foreach2-toVec-Σ : ∀ {l} {r} {n : ℕ} {A B : Set l} {P : A → B → Set r} 
                        → Σ[ xs ∈ Vec A n ] Σ[ ys ∈ Vec B n ] foreach2 P xs ys
                        → Vec (Σ[ x ∈ A ] Σ[ y ∈ B ] P x y) n
        foreach2-toVec-Σ ([] , [] , _) = []
        foreach2-toVec-Σ (x ∷ xs , y ∷ ys , (pxy , ps)) = (x , y , pxy) ∷ (foreach2-toVec-Σ (xs , ys , ps))

        foreach2-fromVec-Σ : ∀ {l} {r} {n : ℕ} {A B : Set l} {P : A → B → Set r} 
                        → Vec (Σ[ x ∈ A ] Σ[ y ∈ B ] P x y) n
                        → Σ[ xs ∈ Vec A n ] Σ[ ys ∈ Vec B n ] foreach2 P xs ys
        foreach2-fromVec-Σ [] = ([] , [] , bigtt)
        foreach2-fromVec-Σ (( x , y , p) ∷ ps) =
            let (xs , ys , pxys) = foreach2-fromVec-Σ ps
                in ( x ∷ xs , y ∷ ys , (p , pxys))
        -- end iso 

        make-foreach2 : ∀ {l} {r} {n : ℕ} {A B : Set l}
                    → {P : A → B → Set r}
                    → {xs : Vec A n} → {ys : Vec B n}
                    → (∀ {x : A} {y : B} → P x y)
                    → foreach2 P xs ys 
        make-foreach2 {xs = []} {[]} f = bigtt 
        make-foreach2 {xs = x ∷ xs} {y ∷ ys} f = f , (make-foreach2 {xs = xs} {ys = ys} f) 


        make-foreach2-homg : ∀ {l} {r} {n : ℕ} {A : Set l}
                    → {P : A → A → Set r}
                    → {As : Vec A n} 
                    → (∀ {x : A} → P x x)
                    → foreach2 P As As 
        make-foreach2-homg {As = []} f = bigtt
        make-foreach2-homg {P = P} {As = A ∷ As} f = f  , (make-foreach2-homg {P = P} {As = As} f)


        foreach-toVec : ∀ {n : ℕ} {A : Set} {P : A → Set} {xs : Vec A n}
                        → foreach P xs
                        → Vec (Σ[ x ∈ A ] P x) n
        foreach-toVec {xs = []} bigtt = []
        foreach-toVec {xs = x ∷ xs} (fst , snd) = (x , fst) ∷ foreach-toVec {xs = xs} snd

        foreach-preserves : ∀ {n : ℕ} {A : Set} {P Q : A → Set}
                        → (∀ (x : A) → P x → Q x)
                        → (As : Vec A n)
                        → foreach P As
                        → foreach Q As
        foreach-preserves P⇒Q [] bigtt = bigtt
        foreach-preserves P⇒Q (x ∷ xs) (P , Ps) = (P⇒Q x P) , (foreach-preserves P⇒Q xs Ps)

open foreach-module public


-- only possible Dec witness of x ≡ x is (yes ≡.refl)
decEqId : ∀ {l} {A : Set l} → (decEq : ∀ (x y : A) → Dec (x ≡ y)) → (a : A) → (decEq a a) ≡ (yes ≡.refl)
decEqId decEq a with decEq a a
... | .true because ofʸ ≡.refl = ≡.refl
... | .false because ofⁿ a≢a = exFalso (a≢a ≡.refl) 







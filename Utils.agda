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

--
-- 

module Utils where

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_) 

subst : ∀ {a b : Level} {A : Set a} {B : A → Set b} → {x y : A} → x ≡ y → B x → B y
subst ≡.refl bx = bx

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
×'-cong : ∀ {l} {A B : Set l} {x1 x2 : A} {y1 y2 : B} → x1 ≡ x2 → y1 ≡ y2 → (x1 , y1) ≡ (x2 , y2)
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




open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation.NaturalIsomorphism as NI 
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) renaming (_ⓘˡ_ to _≃ˡ_)

-- reasoning combinators for NaturalIsomorphism 
module ≃-Reasoning {o l e  o' l' e' : Level} {C : Category o l e} {C' : Category o' l' e'}  where

  -- _ⓘᵥ_ : {F G H : Functor C D} → G ≃ H → F ≃ G → F ≃ H

  infix  3 _≃∎
  infixr 2 _≃⟨⟩_ step-≃ step-≃˘
  infix  1 begin≃_

  begin≃_ : ∀ {F G : Functor C C'} → F ≃ G → F ≃ G
  begin≃_ F≃G = F≃G

  _≃⟨⟩_ : ∀ (F {G} : Functor C C') → F ≃ G → F ≃ G
  _ ≃⟨⟩ F≃G = F≃G

  step-≃ : ∀ (F {G H} : Functor C C') → G ≃ H → F ≃ G → F ≃ H
  step-≃ _ G≃H F≃G = NI.trans F≃G G≃H 

  step-≃˘ : ∀ (F {G H} : Functor C C') → G ≃ H → G ≃ F → F ≃ H
  step-≃˘ _ G≃H G≃F = NI.trans (NI.sym G≃F) G≃H

  _≃∎ : ∀ (F : Functor C C') → F ≃ F
  _≃∎ _ = NI.refl 

  syntax step-≃  F G≃H F≃G = F ≃⟨  F≃G ⟩ G≃H
  syntax step-≃˘ F G≃H G≃F = F ≃˘⟨ G≃F ⟩ G≃H

open ≃-Reasoning

NI-≡ : ∀ {o l e o' l' e'} {C : Category o l e} {C' : Category o' l' e'} {F G : Functor C C'}
       → F ≡ G 
       → F ≃ G
NI-≡ ≡.refl = NI.refl

-- -- eval : Bifunctor (Functors C D) C D 
-- -- eval : Functor (Product (Functors C D) C) D 

private
    variable
        o l e o' l' e' o'' l'' e'' : Level 
        C : Category o l e 
        D : Category o' l' e' 
        E : Category o'' l'' e'' 


module CatUtil where 

  open import Categories.Category.Product using (Product ; _※_  ; πˡ ; πʳ ; _⁂_ ; _※ⁿⁱ_)
  open import Categories.Category.Product.Properties using (※-distrib)
  open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
  open import Categories.Category using (Category)
  open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)

  eval-≃ : ∀ {ao al ae bo bl be co cl ce ddo dl de : Level} {A : Category ao al ae} {B : Category bo bl be} {C : Category co cl ce} {D : Category ddo dl de}
            → (F : Functor A (Product (Functors C D) C)) 
            → (G : Functor B (Product (Functors C D) C))
            → (H : Functor A B) 
            → F ≃ (G ∘F H) → eval ∘F F ≃ (eval ∘F G) ∘F H 
  eval-≃ F G H η = 
      begin≃ 
            eval ∘F F
            ≃⟨ eval ≃ˡ η ⟩ 
            eval ∘F (G ∘F H)
            ≃˘⟨ NI.associator H G eval ⟩ 
            (eval ∘F G) ∘F H
            ≃∎ 

  -- useful for proving set semantics respects substitution 
  compose-distrib-≃ : ∀ {ao al ae bo bl be co cl ce ddo dl de : Level} 
                        {A : Category ao al ae} {B : Category bo bl be}
                        -- target of F 
                        {C : Category co cl ce} {D : Category ddo dl de}
                        -- target of G 
                        -- {CG : Category cgo cgl cge } {DG : Category dgo dgl dge }
                      → {F  : Functor A C}
                      → {F' : Functor B C}
                      → {G  : Functor A D}
                      → {G' : Functor B D}
                      → {H : Functor A B}
                      → F ≃ (F' ∘F H) 
                      → G ≃ (G' ∘F H) 
                      → (F ※ G) ≃ (F' ※ G') ∘F H
  compose-distrib-≃ {A = A} {B} {C} {D} {F} {F'} {G} {G'} {H} η1 η2 = 
    begin≃ 
        (F ※ G)
      ≃⟨ (η1 ※ⁿⁱ η2) ⟩
        ((F' ∘F H) ※ (G' ∘F H)) 
      ≃⟨ ※-distrib C D F' G' H  ⟩
        ((F' ※ G') ∘F H)
      ≃∎ 

    -- _∘ˡ_ 
  open import Categories.Category.Construction.Functors using (Functors)
  precomp-F : (F : Functor D E) → Functor (Functors C D) (Functors C E)
  precomp-F F = record
                     { F₀ = λ G → F ∘F G
                     ; F₁ = λ {G} {H} η →  F ∘ˡ η   
                     ; identity = Functor.identity F
                     ; homomorphism = Functor.homomorphism F
                     ; F-resp-≈ = λ f≈g  →  Functor.F-resp-≈ F f≈g
                     } 

  postcomp-F : ∀ {C : Category o l e} {D : Category o' l' e'} {E : Category o'' l'' e''} (F : Functor C D) → Functor (Functors D E) (Functors C E)
  postcomp-F {C = C} {D} {E} F = record
                     { F₀ = λ G → G ∘F F 
                     ; F₁ = λ {G} {H} η →  η ∘ʳ F
                     ; identity = λ {G} → E.Equiv.refl 
                     ; homomorphism = E.Equiv.refl 
                     ; F-resp-≈ = λ f≈g → f≈g 
                     } 
             where module E = Category E 
                

  -- MuSem : ∀ {k : ℕ} {Γ : TCCtx} {H : TypeExpr}
  --               {φ : FVar k} {αs : Vec (FVar 0) k}
  --             → Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H
  --             → Functor SetEnvCat (Sets^ k) → Functor SetEnvCat Sets 

  -- -- if 
  -- MuSem-≃  : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {H : TypeExpr} {Ks : Vec TypeExpr k}
  --               {φ : FVar k} {αs : Vec (FVar 0) k}
  --             → (⊢H : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ H)
  --             → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
  --             → MuSem ⊢H (SetSemVec ⊢Ks)
  --             ≃ MuSem ⊢H (SetSemVec (F ⊢Ks))
  

  μSem-≃ : ∀ {X : Category o l e} {Y : Category o' l' e'} {Z : Category o'' l'' e''} (G : Functor X Z)
           → (SemKs SemJs : Functor X Y)
           → (FV Extend : Functor X X)
           → SemKs ≃ SemJs ∘F Extend
           → FV ≃ FV ∘F Extend
           → (G ∘F FV ※ SemKs)
           ≃ (((G ∘F FV ※ SemJs)) ∘F Extend)
  μSem-≃ {X = X} {Y} {Z} G SemKs SemJs FV Extend SemKs≃SemJs∘H Forget-Extend-≃ = 
    let G-extend-≃ : G ∘F FV ≃ (G ∘F FV) ∘F Extend
        G-extend-≃ = 
          begin≃
            G ∘F FV
            ≃⟨  G ≃ˡ Forget-Extend-≃  ⟩ 
            G ∘F (FV ∘F Extend)
            ≃˘⟨ NI.associator Extend FV G ⟩
            (G ∘F FV) ∘F Extend
            ≃∎

        G-distrib-※ : (((G ∘F FV) ∘F Extend) ※ (SemJs ∘F Extend))
                      ≃ (((G ∘F FV) ※ SemJs) ∘F Extend)
        G-distrib-※ =  ※-distrib Z Y (G ∘F FV) SemJs Extend 

    in begin≃ 
                (G ∘F FV ※ SemKs)
            ≃⟨  (NI.refl {C = X} {D = Z} {x = G ∘F FV}) ※ⁿⁱ SemKs≃SemJs∘H   ⟩ 
                (G ∘F FV  ※ (SemJs ∘F Extend))
            ≃⟨  G-extend-≃  ※ⁿⁱ (NI.refl {C = X} {D = Y} {x = SemJs ∘F Extend})   ⟩ 
                (((G ∘F FV) ∘F Extend) ※ (SemJs ∘F Extend))
            ≃⟨   G-distrib-※   ⟩ 
                ((G ∘F FV ※ SemJs) ∘F Extend)
            ≃∎




module pointwise-iso {F G : Functor C D} where

  open import Categories.Category using (_[_,_])

  private
    module C = Category C
    module F = Functor F
    module G = Functor G

  import Categories.Morphism as Mor 
  open Category D
  open Mor D
  open _≅_

  -- We can construct a natural isomorphism from a pointwise isomorphism, provided that we can show naturality in one direction.
  pointwise-iso : (iso : ∀ X → F.F₀ X ≅ G.F₀ X) → (∀ {X Y} → (f : C [ X , Y ]) → from (iso Y) ∘ F.F₁ f ≈ G.F₁ f ∘ from (iso X)) → NI.NaturalIsomorphism F G
  pointwise-iso iso commute = NI.niHelper record
    { η = λ X → from (iso X)
    ; η⁻¹ = λ X → to (iso X)
    ; commute = commute
    ; iso = λ X → record
      { isoˡ = isoˡ (iso X)
      ; isoʳ = isoʳ (iso X)
      }
    }

--   import Relation.Binary.HeterogeneousEquality as Het 

--   equiv-iso : ∀ {A B : Obj} → A ≡ B → A ≅ B
--   equiv-iso ≡.refl = record { from = id ; to = id ; iso = record { isoˡ = identityˡ ; isoʳ = identityʳ } } 

--   equiv-iso-from-id : ∀ {A B : Obj} → (e : A ≡ B) → from (equiv-iso e) Het.≅  id
--   equiv-iso-from-id ≡.refl = Het.refl 

--   equiv-iso-from-left : ∀ {A B : Obj} → (e : A ≡ B) → ∀ g → from (equiv-iso e) ∘ g Het.≅ g
--   equiv-iso-from-left ≡.refl g = {!   !}

--   -- equiv-iso-from-id : ∀ {A B : Obj} → (e : A ≡ B) → from (equiv-iso e) ≡ id
--   -- equiv-iso-from-id ≡.refl = Het.refl 

--   open HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎ )
--   -- HomReasoning for D 
  
--   open Het.≅-Reasoning renaming (begin_ to begin≅_ ; _∎ to _≅∎)

--   equiv-iso-natural-Het : ∀ {H K : Functor C Sets} {X Y : Category.Obj C} (f : C [ X , Y ]) 
--                       → (equiv : ∀ X → Functor.F₀ H X ≡ Functor.F₀ K X) 
--                       → (∀ {X Y} → (f : C [ X , Y ]) →  Functor.F₁ H f Het.≅  Functor.F₁ K f)
--                       → from (equiv-iso (equiv Y)) ∘ Functor.F₁ H f Het.≅ Functor.F₁ K f ∘ from (equiv-iso (equiv X))
--   equiv-iso-natural-Het {H} {K} {X} {Y} f equiv map-equiv = 
--     let x = equiv X 
--         y = equiv Y 
--         fg = map-equiv f
--         ey = equiv-iso-from-id y
--       in begin≅ 
--       from (equiv-iso (equiv Y)) ∘ Functor.F₁ H f
--       ≅⟨ Het.cong {!   !}  {!   !} ⟩
--       id ∘ Functor.F₁ H f
--       ≅⟨ {! F.F₁ f  !} ⟩
--       Functor.F₁ H f
--       ≅⟨ map-equiv f ⟩
--       Functor.F₁ K f
--       ≅⟨ {! F.F₁ f  !} ⟩
--       Functor.F₁ K f ∘ id 
--       ≅⟨ {! F.F₁ f  !} ⟩
--       Functor.F₁ K f ∘ from (equiv-iso (equiv X))
--       ≅∎
          
--   -- from (equiv-iso (equiv Y)) ∘ F.F₁ f ≈
--   --       G.F₁ f ∘ from (equiv-iso (equiv X))


--   -- equiv-iso-natural : ∀ {X Y : Category.Obj C} (f : C [ X , Y ]) 
--   --                     → (equiv : ∀ X → F.F₀ X ≡ G.F₀ X) 
--   --                     → (∀ {X Y} → (f : C [ X , Y ]) →  F.F₁ f Het.≅  G.F₁ f)
--   --                     → from (equiv-iso (equiv Y)) ∘ F.F₁ f Het.≅ Functor.F₁ G f ∘ from (equiv-iso (equiv X))
--   -- equiv-iso-natural {X} {Y} f equiv map-equiv = 
--   --   let x = equiv X 
--   --       y = equiv Y 
--   --       fg = map-equiv f
--   --     in begin≅ 
--   --       from (equiv-iso (equiv Y)) ∘ F.F₁ f
--   --     ≅⟨ {! Het.cong (λ g → g ∘ F.F₁ f) (equiv-iso-from-id ?)  !} ⟩
--   --       id ∘ F.F₁ f
--   --     ≅⟨ {! F.F₁ f  !} ⟩
--   --       F.F₁ f
--   --     ≅⟨ {! F.F₁ f  !} ⟩
--   --       F.F₁ f
--   --       Functor.F₁ G f ∘ from (equiv-iso (equiv X))
--   --     ≅∎
          
--   -- -- from (equiv-iso (equiv Y)) ∘ F.F₁ f ≈
--   -- --       G.F₁ f ∘ from (equiv-iso (equiv X))




--   pointwise-iso-het : (equiv : ∀ X → F.F₀ X ≡ G.F₀ X) → (∀ {X Y} → (f : C [ X , Y ]) →  F.F₁ f Het.≅  G.F₁ f) → NI.NaturalIsomorphism F G
--   pointwise-iso-het equiv het-commute = 
--     let x = {!   !}
--       in 
--     pointwise-iso (λ X → equiv-iso (equiv X)) {! equiv-iso-natural   !}
--           -- λ {X} {Y} f → {!   !}
--   --         begin≈ 
--   --           from (equiv-iso (equiv Y)) ∘ F.F₁ f 
--   --         ≈⟨ {! equiv-iso-from-id  !} ⟩
--   --           G.F₁ f ∘ from (equiv-iso (equiv X))
--   --         ≈∎
          
--   -- -- from (equiv-iso (equiv Y)) ∘ F.F₁ f ≈
--   -- --       G.F₁ f ∘ from (equiv-iso (equiv X))



-- {-
--   -- useful for proving set semantics respects substitution 
--   compose-distrib-≃ : ∀ {ao al ae bo bl be co cl ce ddo dl de cgo cgl cge dgo dgl dge : Level} 
--                         {A : Category ao al ae} {B : Category bo bl be}
--                         -- target of F 
--                         {C : Category co cl ce} {D : Category ddo dl de}
--                         -- target of G 
--                         {CG : Category cgo cgl cge } {DG : Category dgo dgl dge }
--                       → (F  : Functor A (Product (Functors C D) C)) 
--                       → (F' : Functor B (Product (Functors C D) C))
--                       → (G  : Functor A (Product (Functors CG DG) CG)) 
--                       → (G' : Functor B (Product (Functors CG DG) CG))
--                       → (H : Functor A B) 
--                       → F ≃ (F' ∘F H) 
--                       → G ≃ (G' ∘F H) 
--                       → (F ※ G) ≃ (F' ※ G') ∘F H
--   compose-distrib-≃ {A = A} {B} {C} {D} {CG} {DG} F F' G G' H η1 η2 = 
--     begin≃ 
--         (F ※ G)
--       ≃⟨ (η1 ※ⁿⁱ η2) ⟩
--         ((F' ∘F H) ※ (G' ∘F H)) 
--       ≃⟨ ※-distrib (Product (Functors C D) C) (Product (Functors CG DG) CG)  F'   G'  H  ⟩
--         ((F' ※ G') ∘F H)
--       ≃∎ 



-- -}



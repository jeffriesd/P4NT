
-- open import Data.String using (String ; _≟_)
open import NestedTypeSyntax
open import Data.Product renaming (_×_ to _×'_ )
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (isYes)

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Vec using (Vec ; [_] ; [] ; _∷_)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any

open import Agda.Builtin.Bool

module TermSyntax where 



-- data _≀_⊢_ : TCCtx → FunCtx → TypeExpr → Set where

{-

This works, but no types.. 
Could just carry around two vectors of equal length 
x1 ... xn 
F1 ... Fn 

where x_i : F_i

-}



EType : TCCtx → FunCtx → Set 
EType Γ Φ = Σ TypeExpr λ F → Γ ≀ Φ ⊢ F 


E+ : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x y : EType Γ Φ) → EType Γ Φ
E+ (F , ⊢F) (G , ⊢G) = (F + G , +-I ⊢F ⊢G)
-- Data.Product.map (uncurry _+_) (uncurry  +-I) ((F , G) , (⊢F , ⊢G))

E× : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x y : EType Γ Φ) → EType Γ Φ
E× (F , ⊢F) (G , ⊢G) = Data.Product.map (uncurry _×_) (uncurry  ×-I) ((F , G) , (⊢F , ⊢G))

mutual 

  -- use isYes or whatever
  data TermCtx2 (Γ : TCCtx) (Φ : FunCtx) : Set where 
    Δ∅       : TermCtx2 Γ Φ 
    _,-_∶_⟨_⟩  : ∀ (Δ : TermCtx2 Γ Φ) 
               → (x : Id) 
               → EType Γ Φ
               -- need proof that x is not already appearing in Δ
               → (isYes (Δ-lookup x Δ) ≡ false)
               → TermCtx2 Γ Φ 

  data _:∋_ : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx2 Γ Φ → Id → Set where
    z : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx2 Γ Φ} {x : Id} 
        → {p : isYes (Δ-lookup x Δ) ≡ false}
        → {⊢F : EType Γ Φ}
        → (Δ ,- x ∶ ⊢F ⟨ p ⟩) :∋ x

    s : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx2 Γ Φ} {x y : Id} 
        → {p : isYes (Δ-lookup x Δ) ≡ false}
        → {⊢F : EType Γ Φ}
        →  Δ :∋ y
        → (Δ ,- x ∶ ⊢F ⟨ p ⟩) :∋ y



  Δ-lookup : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x : Id) (Δ : TermCtx2 Γ Φ)
            → Dec (Δ :∋ x)
  Δ-lookup x Δ∅ = no (λ ())
  Δ-lookup x (Δ ,- y ∶ _ ⟨ p ⟩) with x ≟ y | Δ-lookup x Δ
  ... | yes ≡.refl | _  = yes z 
  ... | no x≢y | yes Δ∋x = yes (s Δ∋x) 
  ... | no x≢y | no ¬Δ∋x = no Δ-lookup-helper 
    where Δ-lookup-helper : ¬ ((Δ ,- y ∶ _ ⟨ p ⟩) :∋ x)
          Δ-lookup-helper z = x≢y ≡.refl
          Δ-lookup-helper (s Δ∋x) = ¬Δ∋x Δ∋x 




x : Id
x = 1
y : Id 
y = 2
t : Id 
t = 3

-- x : 𝟙 
t2 : TermCtx2 ∅ ∅ 
t2 = Δ∅ ,- x ∶ (𝟙 , 𝟙-I) ⟨ ≡.refl ⟩ 

singVarTmCtx : ∀ {Γ : TCCtx} {Φ : FunCtx} → Id → EType Γ Φ →  TermCtx2 Γ Φ
singVarTmCtx v ⊢F = Δ∅ ,- v ∶ ⊢F ⟨ ≡.refl ⟩ 


-- x1 : F , ... , xN : F
nVarTmCtx : ∀ {Γ : TCCtx} {Φ : FunCtx} → ℕ → EType Γ Φ →  TermCtx2 Γ Φ
nVarTmCtx zero ⊢F = Δ∅
nVarTmCtx (suc zero) ⊢F = Δ∅ ,- zero ∶ ⊢F ⟨ ≡.refl ⟩ 
nVarTmCtx (suc n) ⊢F = nVarTmCtx n ⊢F ,- n ∶ ⊢F ⟨ {!   !} ⟩


xctx : TermCtx2 ∅ ∅ 
xctx = singVarTmCtx x (𝟘 , 𝟘-I)

xyctx : TermCtx2 ∅ ∅ 
xyctx = xctx ,- y ∶  (𝟘 , 𝟘-I) ⟨ ≡.refl ⟩ 

xyz : TermCtx2 ∅ ∅ 
xyz = xyctx ,- t ∶ (𝟘 , 𝟘-I) ⟨ ≡.refl  ⟩ 


-- _∈_ : ∀{k} → Id → Vec Id k → 
-- 
idLookup : ∀ {k} → (x : Id) → (xs : Vec Id k) → Dec (x ∈ xs)
idLookup x [] = no λ () 
idLookup x (y ∷ xs) with x ≟ y | idLookup x xs
... | yes ≡.refl | _ = yes (here ≡.refl)
... | no x≢y | yes x∈xs = yes (there x∈xs)
... | no x≢y | no ¬x∈xs = no idLookup-helper
    where idLookup-helper : ¬ (Any (_≡_ x) (y ∷ xs))
          idLookup-helper (here x≡y) = x≢y x≡y
          idLookup-helper (there x∈xs) = ¬x∈xs x∈xs 

-- 
-- this version has the advantage that, since it is indexed by vectors 
-- and uses 'smart constructors', it can automatically fill in a term context 
-- given a vector of (disjoint) ids and a vector of types.  
-- 
-- there is no way to do this as easily with TermCtx2 because it isn't indexed by these vectors. 
-- 
-- 
mutual
  data TermCtx (Γ : TCCtx) (Φ : FunCtx) : ∀ {k : ℕ} → {Vec Id k} → {Vec (EType Γ Φ) k} → Set where 
    Δ∅       : TermCtx Γ Φ {0} {[]} {[]}
    -- -- add new elements on the left to mirror vectors... ?
    _∷_⟨_⟩,-_  : ∀ {k : ℕ} → {xs : Vec Id k} → {⊢Fs : Vec (EType Γ Φ) k} 
                 → (x : Id) 
                 → (⊢F : EType Γ Φ)
                 -- need proof that x is not already appearing in Δ
                 → (isYes (idLookup x xs) ≡ false)
                 → (Δ : TermCtx Γ Φ {k} {xs} {⊢Fs}) 
                 → TermCtx Γ Φ {suc k} {x ∷ xs} {⊢F ∷ ⊢Fs}

    -- -- or we can make vector indices implicit 
    -- _,-_∷_⟨_⟩  : ∀ {k : ℕ} → {xs : Vec Id k} → {⊢Fs : Vec (EType Γ Φ) k} 
    --              → (Δ : TermCtx Γ Φ {k} {xs} {⊢Fs}) 
    --              → (x : Id) 
    --              → (⊢F : EType Γ Φ)
    --              -- need proof that x is not already appearing in Δ
    --              → (isYes (idLookup x xs) ≡ false)
    --              → TermCtx Γ Φ {suc k} {x ∷ xs} {⊢F ∷ ⊢Fs}


ids1 : Vec Id 3
-- ids1 = "a" ∷ ("b" ∷ ("c" ∷ []))
ids1 = 0 ∷ 1 ∷ 2 ∷ []

ts1 : Vec (EType ∅ ∅) 3
ts1 = (𝟙 , 𝟙-I) ∷ ((𝟙 , 𝟙-I) ∷ ((𝟙 , 𝟙-I) ∷ []))


-- auto works for natural numbers, but not Data.String
delta : TermCtx ∅ ∅ {3} {ids1} {ts1}
delta = zero ∷ 𝟙 , 𝟙-I ⟨ ≡.refl ⟩,- (1 ∷ 𝟙 , 𝟙-I ⟨ ≡.refl ⟩,- (2 ∷ 𝟙 , 𝟙-I ⟨ ≡.refl ⟩,- Δ∅))
-- 
-- delta = ((Δ∅ ,- 2 ∷ 𝟙 , 𝟙-I ⟨ ≡.refl ⟩) ,- 1 ∷ 𝟙 , 𝟙-I ⟨ ≡.refl ⟩) ,- zero ∷ 𝟙 , 𝟙-I ⟨ ≡.refl ⟩ 



{-
data _≀_∣_⊢_∷_ : ∀ {k : ℕ} → (Γ : TCCtx) (Φ : FunCtx) 
                → {xs : Vec Id k} {⊢Fs : Vec (EType Γ Φ) k} 
                → TermCtx Γ Φ {k} {xs} {⊢Fs} 
                → TermExpr 
                → EType Γ Φ
                → Set where 

  var-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ}
          → {xs : Vec Id k} {⊢Fs : Vec (EType Γ Φ) k} 
          → (Δ : TermCtx Γ Φ {k} {xs} {⊢Fs}) 
          → (x : Id)
          → (F : EType Γ Φ)
          → (p : isYes (idLookup x xs) ≡ false)
          → Γ ≀ Φ ∣ (x ∷ F ⟨ p ⟩,- Δ) ⊢ tmvar x ∷ F

  bot-elim : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ}
             → {xs : Vec Id k} {⊢Fs : Vec (EType Γ Φ) k} 
             → (Δ : TermCtx Γ Φ {k} {xs} {⊢Fs}) 
             → (F : EType Γ Φ)              
             → (t : TermExpr) 
             → Γ ≀ Φ ∣ Δ ⊢ t ∷ ((𝟘 , 𝟘-I)) 
             → Γ ≀ Φ ∣ Δ ⊢ ⊥e t ∷ F
-}

data TermExpr : Set where
  tmvar : Id → TermExpr
  ⊥e : TermExpr → TermExpr
  ⊤  : TermExpr
  inl : TermExpr → TermExpr
  inr : TermExpr → TermExpr
  cse_of[_↦_≀_↦_] : TermExpr → (x : Id) → TermExpr → (y : Id) → TermExpr → TermExpr
  _,,_ : TermExpr → TermExpr → TermExpr
  π₁ : TermExpr → TermExpr
  π₂ : TermExpr → TermExpr
  L[_]_,_ : ∀ {k : ℕ} → (Vec (FVar 0) k) → Id → TermExpr → TermExpr
  app_[_]_ : ∀ {k : ℕ} → TermExpr → Vec (FVar 0) k → TermExpr → TermExpr
  mapp  : TermExpr
  inn   : TermExpr
  foldd : TermExpr


data _≀_∣_⊢_∷_ : ∀ (Γ : TCCtx) (Φ : FunCtx) 
                → TermCtx2 Γ Φ 
                → TermExpr 
                → EType Γ Φ
                → Set where 

  var-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx2 Γ Φ)
          → (x : Id)
          → (F : EType Γ Φ)
          → (p : isYes (Δ-lookup x Δ) ≡ false)
          → Γ ≀ Φ ∣ Δ ,- x ∶ F ⟨ p ⟩ ⊢ tmvar x ∷ F

  bot-E : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx2 Γ Φ)
          → (F : EType Γ Φ)              
          → (t : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ t ∷ (𝟘 , 𝟘-I)
          → Γ ≀ Φ ∣ Δ ⊢ ⊥e t ∷ F

  ⊤-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx2 Γ Φ)
          → Γ ≀ Φ ∣ Δ ⊢ ⊤ ∷ (𝟙 , 𝟙-I)


  inl-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx2 Γ Φ)
          → (F : EType Γ Φ)              
          → (G : EType Γ Φ)              
          → (s : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ s ∷ F
          → Γ ≀ Φ ∣ Δ ⊢ inl s ∷ E+ F G

-- _≀∅∣∅⊢_ : TCCtx → TermExpr → Set where 
--   map : ∀ Γ 
--           -- → (k : φ )
--           → (φs : Vec (FVar k) n) 

-- open import Data.String using (String ; _≟_)
open import NestedTypeSyntax
open import Data.Product renaming (_×_ to _×'_  ; map to ×'-map) 
open import Data.Sum renaming ([_,_] to [_,⊎_])
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Nullary using (_because_ ; Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (isYes)

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Vec using (Vec ; [_] ; [] ; _∷_ ; _++_)
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any
open import Function using (const ; flip) renaming (id to idf; _∘_ to _∘'_)

open import Agda.Builtin.Bool
open ≡.≡-Reasoning

open import Utils 
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

ETypeVec : TCCtx → FunCtx → ℕ → Set 
ETypeVec Γ Φ k = Σ (Vec TypeExpr k)  (λ Fs → foreach (λ F → Γ ≀ Φ ⊢ F) Fs)

E+ : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x y : EType Γ Φ) → EType Γ Φ
E+ (F , ⊢F) (G , ⊢G) = (F + G , +-I ⊢F ⊢G)
-- Data.Product.map (uncurry _+_) (uncurry  +-I) ((F , G) , (⊢F , ⊢G))

E× : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x y : EType Γ Φ) → EType Γ Φ
E× (F , ⊢F) (G , ⊢G) = Data.Product.map (uncurry _×_) (uncurry  ×-I) ((F , G) , (⊢F , ⊢G))

E𝟘 : ∀ {Γ : TCCtx} {Φ : FunCtx} → EType Γ Φ
E𝟘 = ( 𝟘 , 𝟘-I )

E𝟙 : ∀ {Γ : TCCtx} {Φ : FunCtx} → EType Γ Φ
E𝟙 = ( 𝟙 , 𝟙-I )




-- mutual 

--   -- use isYes or whatever
--   data TermCtx2 (Γ : TCCtx) (Φ : FunCtx) : Set where 
--     Δ∅       : TermCtx2 Γ Φ 
--     _,-_∶_⟨_⟩  : ∀ (Δ : TermCtx2 Γ Φ) 
--                → (x : Id) 
--                → EType Γ Φ
--                -- need proof that x is not already appearing in Δ
--                → (isYes (Δ-lookup x Δ) ≡ false)
--                → TermCtx2 Γ Φ 

--   data _∷∋_ : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx2 Γ Φ → Id → Set where
--     z : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx2 Γ Φ} {x : Id} 
--         → {p : isYes (Δ-lookup x Δ) ≡ false}
--         → {⊢F : EType Γ Φ}
--         → (Δ ,- x ∶ ⊢F ⟨ p ⟩) ∷∋ x

--     s : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx2 Γ Φ} {x y : Id} 
--         → {p : isYes (Δ-lookup x Δ) ≡ false}
--         → {⊢F : EType Γ Φ}
--         →  Δ ∷∋ y
--         → (Δ ,- x ∶ ⊢F ⟨ p ⟩) ∷∋ y



--   Δ-lookup : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x : Id) (Δ : TermCtx2 Γ Φ)
--             → Dec (Δ ∷∋ x)
--   Δ-lookup x Δ∅ = no (λ ())
--   Δ-lookup x (Δ ,- y ∶ _ ⟨ p ⟩) with x ≟ y | Δ-lookup x Δ
--   ... | yes ≡.refl | _  = yes z 
--   ... | no x≢y | yes Δ∋x = yes (s Δ∋x) 
--   ... | no x≢y | no ¬Δ∋x = no Δ-lookup-helper 
--     where Δ-lookup-helper : ¬ ((Δ ,- y ∶ _ ⟨ p ⟩) ∷∋ x)
--           Δ-lookup-helper z = x≢y ≡.refl
--           Δ-lookup-helper (s Δ∋x) = ¬Δ∋x Δ∋x 

-- x : Id
-- x = 1
-- y : Id 
-- y = 2
-- t : Id 
-- t = 3

-- -- x : 𝟙 
-- t2 : TermCtx2 ∅ ∅ 
-- t2 = Δ∅ ,- x ∶ (𝟙 , 𝟙-I) ⟨ ≡.refl ⟩ 

-- singVarTmCtx : ∀ {Γ : TCCtx} {Φ : FunCtx} → Id → EType Γ Φ →  TermCtx2 Γ Φ
-- singVarTmCtx v ⊢F = Δ∅ ,- v ∶ ⊢F ⟨ ≡.refl ⟩ 


-- -- x1 : F , ... , xN : F
-- nVarTmCtx : ∀ {Γ : TCCtx} {Φ : FunCtx} → ℕ → EType Γ Φ →  TermCtx2 Γ Φ
-- nVarTmCtx zero ⊢F = Δ∅
-- nVarTmCtx (suc zero) ⊢F = Δ∅ ,- zero ∶ ⊢F ⟨ ≡.refl ⟩ 
-- nVarTmCtx (suc n) ⊢F = nVarTmCtx n ⊢F ,- n ∶ ⊢F ⟨ {!   !} ⟩


-- xctx : TermCtx2 ∅ ∅ 
-- xctx = singVarTmCtx x (𝟘 , 𝟘-I)

-- xyctx : TermCtx2 ∅ ∅ 
-- xyctx = xctx ,- y ∶  (𝟘 , 𝟘-I) ⟨ ≡.refl ⟩ 

-- xyz : TermCtx2 ∅ ∅ 
-- xyz = xyctx ,- t ∶ (𝟘 , 𝟘-I) ⟨ ≡.refl  ⟩ 

{-
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
   
   -}



mutual
  -- TermCtx3 doesn'tuse EType 
  data TermCtx3 (Γ : TCCtx) (Φ : FunCtx) : Set where 
    Δ∅       : TermCtx3 Γ Φ 
    _,-_∶_⟨_⟩  : ∀ (Δ : TermCtx3 Γ Φ) 
               → (x : Id) 
               → {F : TypeExpr} → (⊢F :  Γ ≀ Φ ⊢ F)
               -- need proof that x is not already appearing in Δ
               → (isYes (Δ-lookup3 x Δ) ≡ false)
               → TermCtx3 Γ Φ 
 
-- s:∶∋/∶∋/g
  data _∶∋_ : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx3 Γ Φ → Id → Set where
    z∋ : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx3 Γ Φ} {x : Id} 
        → {p : isYes (Δ-lookup3 x Δ) ≡ false}
        → {F : TypeExpr} → {⊢F :  Γ ≀ Φ ⊢ F}
        → (Δ ,- x ∶ ⊢F ⟨ p ⟩) ∶∋ x

    s∋ : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx3 Γ Φ} {x y : Id} 
        → {p : isYes (Δ-lookup3 x Δ) ≡ false}
        → {F : TypeExpr} → {⊢F :  Γ ≀ Φ ⊢ F}
        →  Δ ∶∋ y
        → (Δ ,- x ∶ ⊢F ⟨ p ⟩) ∶∋ y



  Δ-lookup3 : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x : Id) (Δ : TermCtx3 Γ Φ)
            → Dec (Δ ∶∋ x)
  Δ-lookup3 x Δ∅ = no (λ ())
  Δ-lookup3 x (Δ ,- y ∶ _ ⟨ p ⟩) with x ≟ y | Δ-lookup3 x Δ
  ... | yes ≡.refl | _  = yes z∋ 
  ... | no x≢y | yes Δ∋x = yes (s∋ Δ∋x) 
  ... | no x≢y | no ¬Δ∋x = no Δ-lookup3-helper 
    where Δ-lookup3-helper : ¬ ((Δ ,- y ∶ _ ⟨ p ⟩) ∶∋ x)
          Δ-lookup3-helper z∋  = x≢y ≡.refl
          Δ-lookup3-helper (s∋  Δ∋x) = ¬Δ∋x Δ∋x 

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
-- this version (TermCtx) has the advantage that, since it is indexed by vectors 
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






mutual 

  weakenFunCtx-Δ  : ∀ {k : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φ : FVar k) 
                  → TermCtx3 Γ Φ
                  → TermCtx3 Γ (Φ ,, φ)
  weakenFunCtx-Δ φ Δ∅ = Δ∅
  weakenFunCtx-Δ φ (Δ ,- x ∶ ⊢F ⟨ p ⟩) =  (weakenFunCtx-Δ φ Δ ,- x ∶ weakenFunCtximpl φ ⊢F ⟨ weaken-p ⟩)
    where weaken-p : isYes (Δ-lookup3 x (weakenFunCtx-Δ φ Δ)) ≡ false
          weaken-p = begin isYes (Δ-lookup3 x (weakenFunCtx-Δ φ Δ))
                      ≡⟨ ≡.sym (Δ-lookup3-weakenFunCtx φ Δ x) ⟩
                        isYes (Δ-lookup3 x Δ)
                      ≡⟨ p ⟩
                        false
                      ∎

  Δ-lookup3-to : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (φ : FVar k) 
            → (Δ : TermCtx3 Γ Φ)
            → (x : Id)
            → (Δ ∶∋  x)
            → ((weakenFunCtx-Δ φ Δ) ∶∋  x)
  Δ-lookup3-to φ Δ∅ x ()
  Δ-lookup3-to φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) .y z∋ = z∋
  Δ-lookup3-to φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) x (s∋  Δ∋x) = s∋ (Δ-lookup3-to φ Δ x Δ∋x) 


  Δ-lookup3-from : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (φ : FVar k) 
            → (Δ : TermCtx3 Γ Φ)
            → (x : Id)
            → ((weakenFunCtx-Δ φ Δ) ∶∋  x)
            → (Δ ∶∋  x)
  Δ-lookup3-from φ Δ∅ x ()
  Δ-lookup3-from φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) .y z∋ = z∋
  Δ-lookup3-from φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) x (s∋ Δ∋x) = s∋ (Δ-lookup3-from φ Δ x Δ∋x) 

  Δ-lookup3-weakenFunCtx : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (φ : FVar k) 
            → (Δ : TermCtx3 Γ Φ)
            → (x : Id)
            → isYes (Δ-lookup3 x Δ) 
            ≡ isYes (Δ-lookup3 x (weakenFunCtx-Δ φ Δ))
            -- → (p : isYes (Δ-lookup x Δ) ≡ false)
  Δ-lookup3-weakenFunCtx φ Δ∅ x = ≡.refl
  Δ-lookup3-weakenFunCtx φ (Δ ,- y ∶ _ ⟨ p ⟩) x with x ≟ y | Δ-lookup3 x Δ | Δ-lookup3 x (weakenFunCtx-Δ φ Δ)
  ... | yes ≡.refl | _   | r = ≡.refl
  ... | no x≢y | yes Δ∋x | yes wΔ∋x = ≡.refl
  ... | no x≢y | yes Δ∋x | no ¬wΔ∋x = exFalso (¬wΔ∋x (Δ-lookup3-to φ Δ x Δ∋x))
  ... | no x≢y | no ¬Δ∋x | yes wΔ∋x = exFalso (¬Δ∋x (Δ-lookup3-from φ Δ x wΔ∋x))
  ... | no x≢y | no ¬Δ∋x | no ¬wΔ∋x = ≡.refl


  weakenFunCtx-Δ-Vec : ∀ {k n : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φs : Vec (FVar k) n)
                  → TermCtx3 Γ Φ
                  → TermCtx3 Γ (Φ ,++ φs)
  weakenFunCtx-Δ-Vec [] Δ = Δ
  weakenFunCtx-Δ-Vec (φ ∷ φs) Δ = weakenFunCtx-Δ φ (weakenFunCtx-Δ-Vec φs Δ)

  weakenFunCtx-Δ-∅  : ∀ { Γ : TCCtx } → (Φ : FunCtx)
                  → TermCtx3 Γ ∅ 
                  → TermCtx3 Γ Φ 
  weakenFunCtx-Δ-∅ ∅ Δ = Δ
  weakenFunCtx-Δ-∅ (Φ ,, φ) Δ = weakenFunCtx-Δ φ (weakenFunCtx-Δ-∅ Φ Δ)

  -- Δ-lookup3-weakenFunCtx2 : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (φ : FVar k) 
  --           → (Δ : TermCtx3 Γ Φ)
  --           → (x : Id)
  --           → isYes (Δ-lookup3 x Δ) ≡ false
  --           → isYes (Δ-lookup3 x (weakenFunCtx-Δ φ Δ)) ≡ false




  -- Δ-lookup3 x (Δ ,- y ∶ _ ⟨ p ⟩) with x ≟ y | Δ-lookup3 x Δ

-- weakenFunCtxVec-Δ : ∀ {k n : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φs : Vec (FVar k) n)  (F : TypeExpr)
--                   → Γ ≀ Φ ⊢ F
--                   → Γ ≀ Φ ,++ φs ⊢ F



-- form type H [ μH ]
in-I-helper : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
        → {H : TypeExpr} 
        → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
        → Γ ≀ (∅ ,++ αs) ⊢ H [ φ :=[ βs ] (μ φ [λ αs , H ] VarExprVec βs) ]
in-I-helper {φ = φ} {αs} {βs} {H} ⊢H = ho-subst-preserves-typing H (μ φ [λ αs , H ] VarExprVec βs) ⊢H (μ-I H ⊢H (VarExprVec βs) (VarTypeVec βs))

-- substitute αs for βs in H [ μH ] 
in-I-helper2 : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
        → {H : TypeExpr} 
        → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
        → Γ ≀ ∅ ,++ βs ⊢ (H [ φ :=[ βs ] μ φ [λ αs , H ] VarExprVec βs ]) [ αs := VarExprVec βs ]Vec
in-I-helper2 {φ = φ} {αs} {βs} {H} ⊢H = fo-substVec-preserves-typing αs (H [ φ :=[ βs ] μ φ [λ αs , H ] VarExprVec βs ]) 
                                            (VarExprVec βs) (weakenFunCtx-∅-,++ αs (in-I-helper ⊢H)) (VarTypeVec βs)

-- form type H [ μH ]
fold-I-helper : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
        → {H : TypeExpr} → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
        → {F : TypeExpr} → (⊢F : Γ ≀ (∅ ,++ βs)  ⊢ F)
        → Γ ≀ (∅ ,++ αs) ⊢ H [ φ :=[ βs ] F ]
fold-I-helper {φ = φ} {αs} {βs} {H} ⊢H {F} ⊢F = ho-subst-preserves-typing H F ⊢H (weakenFunCtx-∅-,++ βs ⊢F)

fold-I-helper2 : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
        → {H : TypeExpr} → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
        → {F : TypeExpr} → (⊢F : Γ ≀ (∅ ,++ βs)  ⊢ F)
        → Γ ≀ (∅ ,++ βs) ⊢ (H [ φ :=[ βs ] F ]) [ αs := VarExprVec βs ]Vec 
fold-I-helper2 {φ = φ} {αs} {βs} {H} ⊢H {F} ⊢F = fo-substVec-preserves-typing αs (H [ φ :=[ βs ] F ]) (VarExprVec βs) (weakenFunCtx-∅-,++ αs (fold-I-helper ⊢H ⊢F)) (VarTypeVec βs)

-- use TermCtx3, etc. which doesn't use EType and just quantifies F and ⊢F explicitly
data _≀_∣_⊢_∶_ : ∀ (Γ : TCCtx) (Φ : FunCtx) 
                → TermCtx3 Γ Φ 
                → TermExpr 
                → {F : TypeExpr}
                → Γ ≀ Φ ⊢ F
                → Set where 


  vr-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx3 Γ Φ)
          → (x : Id)
          → {F : TypeExpr}
          → (⊢F : Γ ≀ Φ ⊢ F)
          → (p : isYes (Δ-lookup3 x Δ) ≡ false)
          → Γ ≀ Φ ∣ Δ ,- x ∶ ⊢F ⟨ p ⟩ ⊢ tmvar x ∶ ⊢F

  bot-E : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx3 Γ Φ)
          → {F : TypeExpr}
          → (⊢F : Γ ≀ Φ ⊢ F)
          → (t : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ t ∶ 𝟘-I
          → Γ ≀ Φ ∣ Δ ⊢ ⊥e t ∶ ⊢F


  ⊤-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx3 Γ Φ)
          → Γ ≀ Φ ∣ Δ ⊢ ⊤ ∶ 𝟙-I


  inl-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx3 Γ Φ)
          → {F : TypeExpr}
          → (⊢F : Γ ≀ Φ ⊢ F)
          → {G : TypeExpr}
          → (⊢G : Γ ≀ Φ ⊢ G)
          → (s : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ s ∶ ⊢F
          → Γ ≀ Φ ∣ Δ ⊢ inl s ∶ +-I ⊢F ⊢G 

  inr-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx3 Γ Φ)
          → {F : TypeExpr}
          → (⊢F : Γ ≀ Φ ⊢ F)
          → {G : TypeExpr}
          → (⊢G : Γ ≀ Φ ⊢ G)
          → (s : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ s ∶ ⊢G
          → Γ ≀ Φ ∣ Δ ⊢ inr s ∶ +-I ⊢F ⊢G 

  case-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx3 Γ Φ)
          → {F : TypeExpr} → (⊢F : Γ ≀ Φ ⊢ F)
          → {G : TypeExpr} → (⊢G : Γ ≀ Φ ⊢ G)
          → {K : TypeExpr} → (⊢K : Γ ≀ Φ ⊢ K)
          -- 
          → (t : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ t ∶ +-I ⊢F ⊢G 
          --
          → (x : Id)
          → (px : isYes (Δ-lookup3 x Δ) ≡ false)
          → (l : TermExpr)
          → Γ ≀ Φ ∣ Δ ,- x ∶ ⊢F ⟨ px ⟩ ⊢ l ∶ ⊢K
          --
          → (y : Id)
          → (py : isYes (Δ-lookup3 y Δ) ≡ false)
          → (r : TermExpr)
          → Γ ≀ Φ ∣ Δ ,- y ∶ ⊢G ⟨ py ⟩ ⊢ r ∶ ⊢K
          -- 
          → Γ ≀ Φ ∣ Δ ⊢ cse t of[ x ↦ l ≀ y ↦ r ] ∶ ⊢K

  pair-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
           → (Δ : TermCtx3 Γ Φ)
           → {F : TypeExpr} → (⊢F : Γ ≀ Φ ⊢ F)
           → {G : TypeExpr} → (⊢G : Γ ≀ Φ ⊢ G)
           → (s : TermExpr) 
           → Γ ≀ Φ ∣ Δ ⊢ s ∶ ⊢F 
           --
           → (t : TermExpr) 
           → Γ ≀ Φ ∣ Δ ⊢ t ∶ ⊢G
           -- 
           → Γ ≀ Φ ∣ Δ ⊢ (s ,, t) ∶ ×-I ⊢F ⊢G


  π₁-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
         → (Δ : TermCtx3 Γ Φ)
         → {F : TypeExpr} → (⊢F : Γ ≀ Φ ⊢ F)
         → {G : TypeExpr} → (⊢G : Γ ≀ Φ ⊢ G)
         → (t : TermExpr) 
         → Γ ≀ Φ ∣ Δ ⊢ t ∶ ×-I ⊢F ⊢G 
         -- 
         → Γ ≀ Φ ∣ Δ ⊢ π₁ t ∶ ⊢F


  π₂-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
         → (Δ : TermCtx3 Γ Φ)
         → {F : TypeExpr} → (⊢F : Γ ≀ Φ ⊢ F)
         → {G : TypeExpr} → (⊢G : Γ ≀ Φ ⊢ G)
         → (t : TermExpr) 
         → Γ ≀ Φ ∣ Δ ⊢ t ∶ ×-I ⊢F ⊢G 
         -- 
         → Γ ≀ Φ ∣ Δ ⊢ π₂ t ∶ ⊢G


  L-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ} {αs : Vec (FVar 0) k}
          {F G : TypeExpr}
        → (⊢F : Γ ≀ ( ∅ ,++ αs ) ⊢ F)
        → (⊢G : Γ ≀ ( ∅ ,++ αs ) ⊢ G)
        -- → Γ ≀ Φ ⊢ Nat^ αs [ F , G ]
        -- → (Δ : TermCtx3 Γ ( ∅ ,++ αs ))
        → (Δ : TermCtx3 Γ ∅ )
        → (x : Id)
        → (p : isYes (Δ-lookup3 x (weakenFunCtx-Δ-Vec αs Δ)) ≡ false)
        → (t : TermExpr)
        -- need to weaken Δ by αs for this to be well-typed
        → Γ ≀ ( ∅ ,++ αs ) ∣ (weakenFunCtx-Δ-Vec αs Δ) ,- x ∶ ⊢F ⟨ p ⟩ ⊢ t ∶ ⊢G
        -- 
        → Γ ≀ ∅ ∣ Δ ⊢ L[ αs ] x , t ∶ Nat-I ⊢F ⊢G

  app-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ} {αs : Vec (FVar 0) k}
          {F G : TypeExpr}
        → (⊢F : Γ ≀ ( ∅ ,++ αs ) ⊢ F)
        → (⊢G : Γ ≀ ( ∅ ,++ αs ) ⊢ G)
        → {Ks : Vec TypeExpr k} → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
        → (Δ : TermCtx3 Γ ∅ )
        → (t : TermExpr)
        → Γ ≀ ∅ ∣ Δ ⊢ t ∶ Nat-I ⊢F ⊢G 
        -- need to weaken Δ by Φ for s and conclusion 
        → (s : TermExpr)
        -- (fo-substVec-preserves-typing αs F Ks ⊢F ⊢Ks) : 
        -- 
        -- need F [ αs := Ks ] to be yped in Γ ≀ Φ .
        -- it should be typed in ∅ after the substitution. 
        -- 
        -- so for it to be typed in Φ after the substitution, 
        -- we need it to be typed in Φ ,++ αs before substituting (by weakenfunCtx-∅-,++)
        → Γ ≀ Φ ∣ (weakenFunCtx-Δ-∅ Φ Δ) ⊢ s ∶ (fo-substVec-preserves-typing αs F Ks (weakenFunCtx-∅-,++ αs ⊢F) ⊢Ks)
        -- 
        → Γ ≀ Φ ∣ (weakenFunCtx-Δ-∅ Φ Δ) ⊢ app t [ αs ] s  ∶ Nat-I ⊢F ⊢G


  -- g is the number of gammas 
  -- p is the number of φs 
  -- 
  -- 
  -- do map for single φ for now 
  -- 
  -- k is the arity of φ , number of βs 
  map-I : ∀ {Γ : TCCtx} {g : ℕ} {k : ℕ} 
          → {φ : FVar k}
          → {βs : Vec (FVar 0) k} 
          → {γs : Vec (FVar 0) g} 
          --
          → {H : TypeExpr}
          → (⊢H : Γ ≀ (∅ ,++ γs) ,, φ ⊢ H)
          -- 
          → {F : TypeExpr}
          → (⊢F : Γ ≀ (∅ ,++ (γs ++ βs)) ⊢ F)
          -- 
          → {G : TypeExpr}
          → (⊢G : Γ ≀ (∅ ,++ (γs ++ βs)) ⊢ G)
          --

          -- want H[F] : Γ ≀ ∅ ,++ γs 
          -- so we need H to be formed in 
          -- Γ ≀ (∅ ,++ γs) ,, φ
          -- and F to be formed in 
          -- Γ ≀ (∅ ,++ γs) ,++ βs
          -- 
          -- to change context of F to (∅ ,++ γs) ,++ βs we use 
          --   FunCtx-resp-++ : ∀ {Γ : TCCtx} {k j : ℕ} (αs : Vec (FVar 0) k) (βs : Vec (FVar 0) j)
          --     {F : TypeExpr}
          --   → Γ ≀ ( ∅ ,++ (αs ++ βs)) ⊢ F
          --   → Γ ≀ ( ∅ ,++ αs ) ,++ βs ⊢ F
          -- 
          -- FunCtx-resp-++ γs βs ⊢F :  Γ ≀ ( ∅ ,++ γs ) ,++ βs ⊢ F
          
          -- -- ho-subst-preserves-typing H F ⊢H ⊢F : Γ ≀ (∅ ,++ γs) ⊢ H [ φ :=[ βs ] F ]
          -- -- ho-subst-preserves-typing H F ⊢H ⊢F : Γ ≀ (∅ ,++ γs) ⊢ H [ φ :=[ βs ] F ]

          -- → Γ ≀ ∅ ∣ Δ∅ ⊢ mapp ∶ Nat-I (Nat-I ⊢F ⊢G) (Nat-I (ho-subst-preserves-typing H F ⊢H (FunCtx-resp-++ {Γ} γs βs ⊢F)) ((ho-subst-preserves-typing H G ⊢H (FunCtx-resp-++ {Γ} γs βs ⊢G))))
          → Γ ≀ ∅ ∣ Δ∅ ⊢ mapp ∶ Nat-I {αs = []} (Nat-I ⊢F ⊢G) (Nat-I (ho-subst-preserves-typing {αs = βs} H F ⊢H (FunCtx-resp-++ γs βs ⊢F)) 
                                                                     (ho-subst-preserves-typing {αs = βs} H G ⊢H (FunCtx-resp-++ γs βs ⊢G)))

  -- ho-subst-preserves-typing : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : FVar k} {αs : Vec (FVar 0) k}
  --                            → (F H : TypeExpr)
  --                            → Γ ≀ (Φ ,, φ) ⊢ F
  --                            → Γ ≀ (Φ ,++ αs) ⊢ H
  --                            → Γ ≀ Φ ⊢ F [ φ :=[ αs ] H ]

  in-I : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
         → {H : TypeExpr} 
         → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
         -- 
         → Γ ≀ ∅ ∣ Δ∅ ⊢ inn ∶ Nat-I {αs = βs} (in-I-helper2 ⊢H) (μ-I H ⊢H (VarExprVec βs) (VarTypeVec βs))

  fold-I : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
         → {H : TypeExpr} 
         → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
         --
         → {F : TypeExpr} 
         → (⊢F : Γ ≀ (∅ ,++ βs)  ⊢ F)
         -- 
         → Γ ≀ ∅ ∣ Δ∅ ⊢ foldd ∶ Nat-I {αs = []} (Nat-I {αs = βs} (fold-I-helper2 ⊢H ⊢F) ⊢F) (Nat-I {αs = βs} (μ-I H ⊢H (VarExprVec βs) (VarTypeVec βs)) ⊢F)



module TermSemantics where 

  open import Categories.Functor using (Functor ; _∘F_)
  open import SetEnvironments using (SetEnvCat ; SetEnv)
  open import SetCats 
  open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
  open import NestedSetSemantics 
  open import Categories.Category using (Category)
  open import Categories.Category.Product 
  open import Data.Unit renaming (⊤ to ⊤') 
  open import Data.Empty renaming (⊥ to ⊥') 
  open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
  open import Level

  open import SetSemWeakenFunCtx using (SetSem-weakenFunCtx-NT)

  private 
    variable 
      o l e : Level 
      C : Category o l e 

  -- interpretation of term context Δ is given as the product 
  -- of the functors interpreting the types in Δ 
  ContextInterp : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx3 Γ Φ 
                  → Functor SetEnvCat Sets 
  ContextInterp Δ∅ = ConstF ⊤'
  ContextInterp (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) = ContextInterp Δ ×Set SetSem ⊢F



  proj₁-commute : ∀ {F G : Functor C Sets} {X Y : Category.Obj C}
                 (f : C Categories.Category.[ X , Y ])
                 → Sets Categories.Category.[ 
                    proj₁ ∘' (Functor.F₁ (F ×Set G) f)
                  ≈ Functor.F₁ F f ∘' proj₁  ]
  proj₁-commute f {fst , snd} = ≡.refl 


  proj₁Nat : ∀ {F G : Functor C Sets}
            → NaturalTransformation ((F ×Set G)) F
  proj₁Nat {o} {l} {e} {C = C} {F} {G} = record { η = λ _ → proj₁ ; commute = λ f {x} → proj₁-commute {C = C} {F} {G} f {x} ; sym-commute = λ f {x} → ≡.sym (proj₁-commute {C = C} {F} {G} f {x}) } 
  

  proj₂-commute : ∀ {F G : Functor C Sets} {X Y : Category.Obj C}
                 (f : C Categories.Category.[ X , Y ])
                 → Sets Categories.Category.[ 
                    proj₂ ∘' (Functor.F₁ ((F ×Set G)) f)
                  ≈ Functor.F₁ G f ∘' proj₂  ]
  proj₂-commute f {fst , snd} = ≡.refl 


  proj₂Nat : ∀ {F G : Functor C Sets}
            → NaturalTransformation (F ×Set G) G
  proj₂Nat {o} {l} {e} {C = C} {F} {G} = record { η = λ X → proj₂ ; commute = λ f {x} → proj₂-commute {C = C} {F} {G} f {x} ; sym-commute = λ f {x} → ≡.sym (proj₂-commute {C = C} {F} {G} f {x}) } 
  

  -- TODO should be able to define this in terms of a more 
  -- general projection natural transformation 
  var-interp : ∀ {Γ : TCCtx} {Φ : FunCtx} 
               → (Δ : TermCtx3 Γ Φ)
               → {x : Id}
               → {F : TypeExpr}
               → (⊢F : Γ ≀ Φ ⊢ F)
               → {p : isYes (Δ-lookup3 x Δ) ≡ false}
               → NaturalTransformation (ContextInterp (Δ ,- x ∶ ⊢F ⟨ p ⟩)) 
                                       (SetSem ⊢F)
  var-interp Δ ⊢F = proj₂Nat {F = ContextInterp Δ} {G = SetSem ⊢F}
  -- record { η = λ { ρ (Δsem , ⊢Fsem) → ⊢Fsem   } 
  --                          ; commute = {!   !} ; sym-commute = {!   !} } 


  -- TODO use Categories.Functor.Construction.Constant instead of ConstF 
  -- 

  -- TODO move this to SetCats or something 
  𝟘! : ∀ {F : Functor C Sets} 
       → NaturalTransformation (ConstF ⊥') F
  𝟘! = record { η = λ _ → exFalso ;  commute = λ f → λ {} ; sym-commute = λ f → λ {} } 

  𝟙! : ∀ {F : Functor C Sets} 
       → NaturalTransformation F (ConstF ⊤') 
  𝟙! = record { η = λ _ → const tt ;  commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl } 


  inl-Nat : ∀ {F G : Functor C Sets}
            → NaturalTransformation F ((F +Set G))
  inl-Nat = record { η = λ _ → inj₁  ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl }

  inr-Nat : ∀ {F G : Functor C Sets}
            → NaturalTransformation G ((F +Set G))
  inr-Nat = record { η = λ _ → inj₂ ; commute = λ f → ≡.refl ; sym-commute = λ f → ≡.refl }

  prod-Nat-commute : ∀ {F G H : Functor C Sets} 
                      → (η₁ : NaturalTransformation F G)
                      → (η₂ : NaturalTransformation F H) 
                      → {X Y : Category.Obj C}
                      → (f : C Categories.Category.[ X , Y ]) 
                      → Sets Categories.Category.[ 
                        < NaturalTransformation.η η₁ Y , NaturalTransformation.η η₂ Y >
                        ∘' (Functor.F₁ F f)
                      ≈ 
                        (Functor.F₁ ((G ×Set H)) f)
                        ∘' < NaturalTransformation.η η₁ X , NaturalTransformation.η η₂ X >
                      ]
-- goal : (NaturalTransformation.η η₁ Y (Functor.F₁ F f x) ,
--  NaturalTransformation.η η₂ Y (Functor.F₁ F f x))
-- ≡
-- (Functor.F₁ G f (NaturalTransformation.η η₁ X x) ,
--  Functor.F₁ H f (NaturalTransformation.η η₂ X x))
  prod-Nat-commute η₁ η₂ f = ×'-cong (NaturalTransformation.commute η₁ f) (NaturalTransformation.commute η₂ f) 



  -- TODO can this be defined in terms of _※ⁿ_ 
  prod-Nat : ∀ {F G H : Functor C Sets}
            → NaturalTransformation F G
            → NaturalTransformation F H
            → NaturalTransformation F ((G ×Set H))
  prod-Nat η₁ η₂ = 
      record { η = λ X → < (NaturalTransformation.η η₁ X)  , (NaturalTransformation.η η₂ X ) > 
             ; commute     = λ f → prod-Nat-commute η₁ η₂ f 
             ; sym-commute = λ f → ≡.sym (prod-Nat-commute η₁ η₂ f) } 


  prod-Nat2-commute : ∀ {F1 G1 F2 G2 : Functor C Sets} (η₁ : NaturalTransformation F1 G1)
                        (η₂ : NaturalTransformation F2 G2) {X Y : Category.Obj C}
                        (f : C Categories.Category.[ X , Y ]) 
                        → Sets Categories.Category.[ 
                          ×'-map (NaturalTransformation.η η₁ Y) (NaturalTransformation.η η₂ Y)
                            ∘' (Functor.F₁ (F1 ×Set F2) f)
                          ≈ (Functor.F₁ (G1 ×Set G2) f)
                          ∘' (×'-map (NaturalTransformation.η η₁ X) (NaturalTransformation.η η₂ X)) ]
  prod-Nat2-commute η₁ η₂ f {x , y} = ×'-cong (NaturalTransformation.commute η₁ f) (NaturalTransformation.commute η₂ f) 



  prod-Nat2 : ∀ {F1 G1 F2 G2 : Functor C Sets}
            → NaturalTransformation F1 G1
            → NaturalTransformation F2 G2
            → NaturalTransformation (F1 ×Set F2) (G1 ×Set G2)
  prod-Nat2 {F1 = F1} {G1} {F2} {G2} η₁ η₂ = 
      record { η = λ X → ×'-map (NaturalTransformation.η η₁ X) (NaturalTransformation.η η₂ X) 
             ; commute = λ f → prod-Nat2-commute η₁ η₂ f 
             ; sym-commute = λ f → ≡.sym (prod-Nat2-commute η₁ η₂ f) } 


  -- prod-Nat-gen : ∀ {F G H : Functor C Sets}
  --           → NaturalTransformation F G
  --           → NaturalTransformation F H
  --           → NaturalTransformation F (SetProd ∘F (G ※ H))


  sum-Nat-commute : ∀ {F G H : Functor C Sets} 
                    → (η₁ : NaturalTransformation F H)
                    → (η₂ : NaturalTransformation G H) 
                    → {X Y : Category.Obj C}
                    → (f : C Categories.Category.[ X , Y ]) 
                    → Sets Categories.Category.[
                      [ NaturalTransformation.η η₁ Y ,⊎ NaturalTransformation.η η₂ Y ]
                      ∘' Functor.F₁ ((F +Set G)) f
                      ≈ 
                        Functor.F₁ H f 
                        ∘' [ NaturalTransformation.η η₁ X ,⊎ NaturalTransformation.η η₂ X ]
                    ]
  sum-Nat-commute {F = F} {G} {H} η₁ η₂ {X} {Y} f {inj₁ x} = NaturalTransformation.commute η₁ f
  sum-Nat-commute {F = F} {G} {H} η₁ η₂ {X} {Y} f {inj₂ y} = NaturalTransformation.commute η₂ f 

  -- this doesn't quite work 
  curry-Nat : ∀ {F G H : Functor C Sets}
            → NaturalTransformation (F ×Set G) H 
            → NaturalTransformation F (ConstF (NaturalTransformation G H))
  curry-Nat {F = F} {G} {H} η = 
          record { η = λ X fx → record { η = λ Y gy → NaturalTransformation.η η Y ({!   !} , gy) ; commute = {!   !} ; sym-commute = {!   !} } 
                 ; commute = {!   !} 
                 ; sym-commute = {!   !} } 


  sum-Nat : ∀ {F G H : Functor C Sets}
            → NaturalTransformation F H
            → NaturalTransformation G H
            → NaturalTransformation ((F +Set G)) H
  sum-Nat η₁ η₂ = 
      record { η = λ X → [ (NaturalTransformation.η η₁ X) ,⊎ (NaturalTransformation.η η₂ X ) ] 
             ; commute     = λ f {x} → sum-Nat-commute η₁ η₂ f {x}
             ; sym-commute = λ f {x} → ≡.sym (sum-Nat-commute η₁ η₂ f {x}) }


  weaken-Δ-NT : ∀ {Γ : TCCtx} {Φ : FunCtx} (α : FVar 0)
              → (Δ : TermCtx3 Γ Φ)
              → NaturalTransformation (ContextInterp Δ) (ContextInterp (weakenFunCtx-Δ α Δ))
  weaken-Δ-NT α Δ∅ = idnat
  weaken-Δ-NT α (Δ ,- x ∶ ⊢F ⟨ p ⟩) = 
      let r : NaturalTransformation (ContextInterp Δ) (ContextInterp (weakenFunCtx-Δ α Δ))
          r = weaken-Δ-NT α Δ 
          w : NaturalTransformation (SetSem ⊢F) (SetSem (weakenFunCtximpl α ⊢F))
          w = SetSem-weakenFunCtx-NT α ⊢F 
        in prod-Nat2 r w  
   
  weaken-Δ-Vec-NT : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (αs : Vec (FVar 0) k)
              → (Δ : TermCtx3 Γ Φ)
              → NaturalTransformation (ContextInterp Δ) (ContextInterp (weakenFunCtx-Δ-Vec αs Δ))
  weaken-Δ-Vec-NT []       Δ = idnat
  weaken-Δ-Vec-NT (α ∷ αs) Δ = weaken-Δ-NT α (weakenFunCtx-Δ-Vec αs Δ) ∘v weaken-Δ-Vec-NT αs Δ





  TermSetSem : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx3 Γ Φ} 
              → {F : TypeExpr} → {⊢F : Γ ≀ Φ ⊢ F}
              → {t : TermExpr} 
              →  (⊢t : Γ ≀ Φ ∣ Δ ⊢ t ∶ ⊢F)
              → NaturalTransformation (ContextInterp Δ) (SetSem ⊢F) 
  TermSetSem (vr-I Δ x ⊢F p) = var-interp Δ {x} ⊢F {p = p}
  TermSetSem (bot-E _ _ t ⊢t) = 𝟘! ∘v TermSetSem ⊢t
  TermSetSem (⊤-I _) = 𝟙!
  TermSetSem (inl-I _ ⊢F ⊢G t ⊢t) = inl-Nat ∘v TermSetSem ⊢t
  TermSetSem (inr-I _ ⊢F ⊢G t ⊢t) = inr-Nat ∘v TermSetSem ⊢t
  TermSetSem (case-I Δ ⊢F ⊢G ⊢K t ⊢t x px l ⊢l y py r ⊢r)  = 
    let [l,r] : NaturalTransformation ((ContextInterp Δ ×Set SetSem ⊢F) +Set (ContextInterp Δ ×Set SetSem ⊢G)) (SetSem ⊢K) 
        [l,r] = sum-Nat (TermSetSem ⊢l) (TermSetSem ⊢r) 

        Δsem : Functor SetEnvCat Sets
        Δsem = ContextInterp Δ 

        distr : NaturalTransformation (Δsem  ×Set (SetSem ⊢F +Set SetSem ⊢G)) 
                                      ((Δsem ×Set SetSem ⊢F) +Set (Δsem ×Set SetSem ⊢G))
        distr = ×Set-distr Δsem (SetSem ⊢F) (SetSem ⊢G) 

        semt : NaturalTransformation Δsem (SetSem ⊢F +Set SetSem ⊢G)
        semt = TermSetSem ⊢t

        Δsem×tsem : NaturalTransformation Δsem (Δsem ×Set (SetSem ⊢F +Set SetSem ⊢G)) 
        Δsem×tsem = prod-Nat idnat (TermSetSem ⊢t)

      in [l,r] ∘v distr ∘v Δsem×tsem 

  TermSetSem (pair-I _ ⊢F ⊢G _ ⊢s _ ⊢t) = prod-Nat (TermSetSem ⊢s) (TermSetSem ⊢t)
  TermSetSem (π₁-I _ _ ⊢G t ⊢t) = proj₁Nat ∘v TermSetSem ⊢t
  TermSetSem (π₂-I _ ⊢F _ t ⊢t) = proj₂Nat ∘v TermSetSem ⊢t
  TermSetSem (L-I {αs = αs} ⊢F ⊢G Δ x p t ⊢t) = 
    let tsem : NaturalTransformation (ContextInterp (weakenFunCtx-Δ-Vec αs Δ) ×Set SetSem ⊢F) (SetSem ⊢G)
        tsem = TermSetSem ⊢t

        -- goal is NaturalTransformation (ContextInterp Δ) (NatTypeSem (SetSem ⊢F) (SetSem ⊢G))
        -- so for a particular ρ, we want a morphism (ContextInterp Δ) ρ → (NatTypeSem (SetSem ⊢F) (SetSem ⊢G)) ρ

        -- for a particular (ρ : SetEnv) we have 
        -- 
        -- tsem ρ : wΔ ρ × SetSem ⊢F ρ → SetSem ⊢G ρ 
        -- 
        -- and using weaken-Δ-Vec-NT ρ we can get from 
        -- (Δ ρ) to (wΔ ρ) 
        -- 
        -- 

      in {! Lsem ⊢t  !}
  TermSetSem (app-I ⊢F ⊢G ⊢Ks Δ t ⊢t s ⊢s) = {!   !}
  TermSetSem (map-I ⊢H ⊢F ⊢G) = {!   !}

  -- goal for in-I : NaturalTransformation
  --                (extendSetSem-αs βs (NatEnv ρ) (SetSem (in-I-helper2 ⊢H)))
  --                (extendSetSem-αs βs (NatEnv ρ) (MuSem ⊢H (SetSemVec (VarTypeVec βs))))
  -- 
  -- can use higher-order functoriality of extendSetSem-αs 
  -- and a natural transformation from 
  -- (SetSem (in-I-helper2 ⊢H)) to 
  -- (MuSem ⊢H (SetSemVec (VarTypeVec βs)))
  -- 
  -- which we should be able to define if we have a natural transformation 
  -- from 
  -- (SetSem (in-I-helper2 ⊢H)) to 
  -- (SetSem ⊢H) 
  TermSetSem (in-I {βs = βs} ⊢H) = record { η = λ ρ x → NatT3[ {!   !} ] ; commute = {!   !} ; sym-commute = {!   !} }
  TermSetSem (fold-I ⊢H ⊢F) = {!   !}

    -- curry₁ : {F G : Bifunctor C₁ C₂ D} →
    --          NaturalTransformation F G →
    --          NaturalTransformation (curry₀ F) (curry₀ G)

  Lsem : ∀ {Γ} {Δ : TermCtx3 Γ ∅} {k} {αs : Vec (FVar 0) k} {F} {G}
         {⊢F : Γ ≀ ∅ ,++ αs ⊢ F} {⊢G : Γ ≀ ∅ ,++ αs ⊢ G} {x}
         {p : isYes (Δ-lookup3 x (weakenFunCtx-Δ-Vec αs Δ)) ≡ false} {t}
         → (⊢t : Γ ≀ ∅ ,++ αs ∣ weakenFunCtx-Δ-Vec αs Δ ,- x ∶ ⊢F ⟨ p ⟩ ⊢ t ∶ ⊢G) 
         → NaturalTransformation (ContextInterp Δ) (SetSem (Nat-I ⊢F ⊢G))
  Lsem ⊢t = 
    let semt = TermSetSem ⊢t
    -- just need natural transformation from SetSem ⊢F to SetSem ⊢G and then we can use 
    -- higher-order map of extendSetSem-αs 
      in record { η = λ ρ ⟦Δ⟧ρ → NatT3[ {!   !} ] 
                    ; commute = {!   !} 
                    ; sym-commute = {!   !} } 



  -- TermSetSem ⊢F (vr-I Δ x₁ .⊢F p) = {!   !}
  -- TermSetSem ⊢F (bot-E _ .⊢F t₁ ⊢t) = {!   !}
  -- TermSetSem .𝟙-I (⊤-I _) = {!   !}
  -- TermSetSem .(+-I ⊢F ⊢G) (inl-I _ ⊢F ⊢G s₁ ⊢t) = {!   !}
  -- TermSetSem .(+-I ⊢F ⊢G) (inr-I _ ⊢F ⊢G s₁ ⊢t) = {!   !}
  -- TermSetSem ⊢F (case-I _ ⊢F₁ ⊢G .⊢F t₁ ⊢t x₁ px l ⊢t₁ y₁ py r ⊢t₂) = {!   !}
  -- TermSetSem .(×-I ⊢F ⊢G) (pair-I _ ⊢F ⊢G s₁ ⊢t t₁ ⊢t₁) = {!   !}
  -- TermSetSem ⊢F (π₁-I _ .⊢F ⊢G t₁ ⊢t) = {!   !}
  -- TermSetSem ⊢F (π₂-I _ ⊢F₁ .⊢F t₁ ⊢t) = {!   !}
  -- TermSetSem .(Nat-I ⊢F ⊢G) (L-I ⊢F ⊢G _ x₁ p t₁ ⊢t) = {!   !}
  -- TermSetSem .(Nat-I ⊢F ⊢G) (app-I ⊢F ⊢G ⊢Ks Δ t₁ ⊢t s₁ ⊢t₁) = {!   !}
  -- TermSetSem .(Nat-I (Nat-I ⊢F ⊢G) (Nat-I (ho-subst-preserves-typing _ _ ⊢H (FunCtx-resp-++ _ _ ⊢F)) (ho-subst-preserves-typing _ _ ⊢H (FunCtx-resp-++ _ _ ⊢G)))) (map-I ⊢H ⊢F ⊢G) = {!   !}
  -- TermSetSem .(Nat-I (fo-substVec-preserves-typing _ (_ [ _ :=[ _ ] μ _ [λ _ , _ ] Data.Vec.map (λ β → AppF β [ [] ]) _ ]) (Data.Vec.map (λ β → AppF β [ [] ]) _) (weakenFunCtx-∅-,++ _ (ho-subst-preserves-typing _ (μ _ [λ _ , _ ] Data.Vec.map (λ β → AppF β [ [] ]) _) ⊢H (μ-I _ ⊢H (Data.Vec.map (λ β → AppF β [ [] ]) _) (VarTypeVec _)))) (VarTypeVec _)) (μ-I _ ⊢H (Data.Vec.map (λ β → AppF β [ [] ]) _) (VarTypeVec _))) (in-I ⊢H) = {!   !}
  -- TermSetSem .(Nat-I (Nat-I (fo-substVec-preserves-typing _ (_ [ _ :=[ _ ] _ ]) (Data.Vec.map (λ β → AppF β [ [] ]) _) (weakenFunCtx-∅-,++ _ (ho-subst-preserves-typing _ _ ⊢H (weakenFunCtx-∅-,++ _ ⊢F))) (VarTypeVec _)) ⊢F) (Nat-I (μ-I _ ⊢H (Data.Vec.map (λ β → AppF β [ [] ]) _) (VarTypeVec _)) ⊢F)) (fold-I ⊢H ⊢F) = {!   !} 
open import NestedSemanticsFunctorCleanup using (SetSem)
open import EnvironmentsInnerRecCleanupExt
open import HFixFunctorLib

open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Data.Unit hiding (_≟_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Sum
open import NestedSyntax6NoStrings
open import Data.Vec using ([] ; _∷_ )
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Product renaming (_×_ to _×'_)

open ≡.≡-Reasoning

open import Function renaming (_∘_ to _∘'_)

open import Data.Bool using (if_then_else_; true; false)
open import Utils
open import SetCatslzero

open import Categories.Functor using (Functor ; _∘F_)


module SetInterpFunctorExamples where 

-- this typechecks as of 3/14/21 






-- test set semantics of some simple types 

β : FVar 0
β = zero FVar.^F zero 

nat-expr : TypeExpr
nat-expr = μ β [λ [] , 𝟙 + AppF β [ [] ] ] [] 

nat-type : ∅ ≀ ∅ ⊢ nat-expr
nat-type = μ-I (𝟙 + AppF zero FVar.^F zero [ [] ])
            (+-I 𝟙-I (AppF-I lookupZ [] Data.Unit.tt))
            [] Data.Unit.tt 

env : SetEnv
env = record { tc = λ _ → ConstF ⊤ ; fv = λ _ → ConstF ⊤ } 

-- set interpretation of natural numbers 
nat-interp : Set 
nat-interp = Functor.F₀ (SetSem ∅ ∅ nat-expr nat-type) env 

-- example inhabitants of nat-interp
nat0 : nat-interp
nat0 = hffin (inj₁ Data.Unit.tt) 

nat1 : nat-interp
nat1 = hffin (inj₂ (hffin (inj₁ Data.Unit.tt)))


-- nat-interpis isomorphic to agda natural numbers 
toNat : nat-interp → ℕ
toNat (hffin (inj₁ Data.Unit.tt)) = 0
toNat (hffin (inj₂ y)) = suc (toNat y) 

fromNat : ℕ → nat-interp 
fromNat zero = nat0
fromNat (suc n) = hffin (inj₂ (fromNat n)) 

toNat∘fromNat : ∀ (n : ℕ) → toNat (fromNat n) ≡ n
toNat∘fromNat zero = ≡.refl
toNat∘fromNat (suc n) = ≡.cong suc (toNat∘fromNat n) 

fromNat∘toNat : ∀ (n : nat-interp) → fromNat (toNat n) ≡ n
fromNat∘toNat (hffin (inj₁ _)) = ≡.refl
fromNat∘toNat (hffin (inj₂ y)) = ≡.cong (hffin ∘' inj₂) (fromNat∘toNat y)


-- interpretation of list as nested type is isomorphic to Agda List
φ : FVar 1 
φ = 1 FVar.^F 1

α : FVar 0
α = 2 FVar.^F 0

nlist-body : TypeExpr
nlist-body = 𝟙 + (AppF0 β × AppF φ [ AppF0 β  ∷ [] ])

nlist-expr : TypeExpr
nlist-expr = μ φ [λ β ∷ [] , nlist-body ] (AppF0 α ∷ []) 

nlist-body-type : ∅ ≀ (∅ ,, β ,, φ) ⊢ nlist-body
nlist-body-type = 
  let β,φ⊢β : ∅ ≀ ∅ ,, β ,, φ ⊢ AppF0 β
      β,φ⊢β  = AppF-I (lookupDiffArity (λ ()) lookupZ) [] Data.Unit.tt
      β,φ⊢φβ : ∅ ≀ ∅ ,, β ,, φ ⊢ AppF φ [ AppF0 β ∷ [] ]
      β,φ⊢φβ = AppF-I lookupZ ((AppF0 β) ∷ []) (β,φ⊢β , Data.Unit.tt)
    in +-I 𝟙-I (×-I β,φ⊢β β,φ⊢φβ)


nlist-type : ∅ ≀ (∅ ,, α) ⊢ nlist-expr 
nlist-type = μ-I nlist-body nlist-body-type ((AppF0 α) ∷ []) (AppF-I lookupZ [] Data.Unit.tt , Data.Unit.tt)


nlist-interp : Functor SetEnvCat Sets
nlist-interp = SetSem ∅ (∅ ,, α) nlist-expr nlist-type

nlist-interp-obj : Set → Set 
nlist-interp-obj A = Functor.F₀ nlist-interp (env [ α :fv= ConstF A ])

nlist-interp-⊤ : Set
nlist-interp-⊤ = Functor.F₀ nlist-interp (env [ α :fv= ConstF ⊤ ])

-- empty list of units
nlist-interp-⊤-elem : nlist-interp-⊤
nlist-interp-⊤-elem = hffin (inj₁ Data.Unit.tt) 

-- 2 element list of units 
nlist-interp-⊤-elem2 : nlist-interp-⊤
nlist-interp-⊤-elem2 = hffin (inj₂ (Data.Unit.tt , hffin (inj₂ (Data.Unit.tt , (hffin (inj₁ Data.Unit.tt))))))



open import Data.List

toList : ∀ A → nlist-interp-obj A → List A 
toList A (hffin (inj₁ Data.Unit.tt)) = []
toList A (hffin (inj₂ (x , xs))) = x ∷ toList A xs


fromList : ∀ A → List A → nlist-interp-obj A 
fromList A [] = hffin (inj₁ Data.Unit.tt) 
fromList A (x ∷ xs) = hffin (inj₂ (x , fromList A xs))


fromList∘toList : ∀ A → (xs : nlist-interp-obj A) → fromList A (toList A xs) ≡ xs
fromList∘toList A (hffin (inj₁ Data.Unit.tt)) = ≡.refl
fromList∘toList A (hffin (inj₂ (x , xs))) = ≡.cong (hffin ∘' inj₂ ∘' ((_,_) x)) (fromList∘toList A xs) 

-- ≡.cong ((_,_) x) (fromList∘toList A xs)
toList∘fromList : ∀ A → (xs : List A) → toList A (fromList A xs) ≡ xs
toList∘fromList A [] = ≡.refl 
toList∘fromList A (x ∷ xs) = ≡.cong (_∷_ x) (toList∘fromList A xs)


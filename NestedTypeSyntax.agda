module NestedTypeSyntax where

open import Relation.Binary.PropositionalEquality hiding ([_])
-- open import Data.String using (String ; _≟_)
-- open import Data.Nat using (ℕ; zero; suc)
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Agda.Builtin.String

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
-- open import Data.List hiding ([_])
open import Data.Sum
open import Data.Product renaming (_×_ to _×'_)
open import Data.Vec as Vec using (Vec ; [_] ; [] ; _∷_ ; _++_)
open import Data.Vec using (Vec ; [_] ; [] ; _∷_)
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Relation.Nullary using (_because_; ofʸ; ofⁿ)
open import Data.Unit using (⊤)
open import Level using (Lift)
open import Utils



-- _=s=_ : (x y : String) → Set 
-- x =s= y = primStringEquality x y ≡ true 

-- _=?=_ : (x y : String) → Dec (x =s= y)
-- x =?= y with primStringEquality x y
-- ... | false = no λ ()
-- ... | true = yes refl

-- represent variables with names (as natural numbers)
Id : Set
Id = ℕ
-- Id = String

-- need to distinguish between
-- variables that will go into
-- functorial vs. non-functorial (type constructor)
-- contexts
data TCVar : ℕ → Set where
  _^T_ : Id → (k : ℕ) → TCVar k


-- A variable is indexed by a natural number, indicating its arity. 
data FVar : ℕ → Set where
  _^F_ : Id → (k : ℕ) → FVar k

cong-^T : ∀ {k : ℕ} {v v' : Id} → v ^T k ≡ v' ^T k → v ≡ v'
cong-^T refl = refl

-- if the names aren't equal, neither are the names with their arities
≢-TCVar : ∀ {k : ℕ} → (v v' : Id) → v ≢ v' → (v ^T k) ≢ (v' ^T k)
≢-TCVar v v' v≢v' vT≡v'T  = v≢v' (cong-^T vT≡v'T)

cong-^F : ∀ {k : ℕ} {v v' : Id} → v ^F k ≡ v' ^F k → v ≡ v'
cong-^F refl = refl

≢-FVar : ∀ {k : ℕ} → (v v' : Id) → v ≢ v' → (v ^F k) ≢ (v' ^F k)
≢-FVar v v' v≢v' vF≡v'F  = v≢v' (cong-^F vF≡v'F)

-- suc is injective 
suc-cong2 : ∀ {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-cong2 refl = refl

-- negation distributes over injective functions 
¬-cong : ∀ {A B : Set} {p q : A} {f : A → B} → (¬ (p ≡ q)) → (inj : (f p ≡ f q) → p ≡ q ) → (¬ (f p ≡ f q))
¬-cong ¬p inj fp≡fq = ¬p (inj fp≡fq)



-- decidable equality for natural numbers 
eqNat : ∀ (x y : ℕ) → Dec (x ≡ y)
eqNat zero zero = true because (ofʸ refl)
eqNat (suc x) zero = false because (ofⁿ (λ()))
eqNat zero (suc y) = false because (ofⁿ (λ()))
eqNat (suc x) (suc y) with eqNat x y
... | .true because ofʸ p = true because (ofʸ (cong suc p))
... | .false because ofⁿ ¬p = false because (ofⁿ (¬-cong ¬p suc-cong2))


_≟_ : ∀ (x y : Id) → Dec (x ≡ y)
_≟_ = eqNat 


-- data constructors here are type constructors 
-- datatype of type expressions
data TypeExpr : Set where
  𝟘 : TypeExpr
  𝟙 : TypeExpr
  Nat^_[_,_] : ∀ {k : ℕ} → Vec (FVar 0) k → TypeExpr → TypeExpr → TypeExpr
  _+_ : TypeExpr → TypeExpr → TypeExpr
  _×_ : TypeExpr → TypeExpr → TypeExpr
  AppT_[_]  : ∀ {k : ℕ} → TCVar k → Vec TypeExpr k → TypeExpr
  AppF_[_]  : ∀ {k : ℕ} → FVar  k → Vec TypeExpr k → TypeExpr
  μ_[λ_,_]_ : ∀ {k : ℕ} → FVar  k → Vec (FVar 0) k 
                → TypeExpr → Vec TypeExpr k → TypeExpr


-- apply a 0-ary (functorial) type variable to 0 arguments
AppF0 : FVar 0 → TypeExpr
AppF0 β = AppF β [ [] ]

VarExpr : FVar 0 → TypeExpr
VarExpr β = AppF β [ [] ]

VarExprVec : ∀ {k} → Vec (FVar 0) k → Vec TypeExpr k
VarExprVec = Vec.map AppF0 


-------------------------------
-------------------------------

  -- infixr ? _,_
  -- 1, 2, 3
  -- (1, (2, 3))

  -- infixl ? _,_
  -- 1, 2, 3
  -- ((1, 2), 3)

-- list of variables and their arities

-- parameterize TypeContext with F : ℕ → Set,
-- where F is intended to be instantiated with TCVar or FVar.
-- this allows us to use only one type for TypeContext so the
-- data constructors can be the same symbols for TCCtx and FunCtx
infixl 20 _,,_
data TypeContext (F : ℕ → Set) : Set where
  ∅ : TypeContext F
  _,,_ : ∀ {k : ℕ} → TypeContext F → F k → TypeContext F

-- type constructor contexts are lists of TCVar
-- where each variable can have a different arity
TCCtx : Set
TCCtx = TypeContext TCVar

-- type constructor contexts are lists of FVar
-- where each variable can have a different arity
FunCtx : Set
FunCtx = TypeContext FVar

∅tc : TCCtx
∅tc = ∅

∅fv : FunCtx
∅fv = ∅

-- append a vector of variables (all of the same arity) 
-- to a context 
_,++_ : ∀ {F : ℕ → Set} {k n : ℕ} → TypeContext F → Vec (F k) n → TypeContext F
Γ ,++ [] = Γ
Γ ,++ (α ∷ αs) = (Γ ,++ αs) ,, α

-- MAKE A NOTE OF ,++ and arity requirement

-- -- concatenate two contexts -- not used 
_,,++_ : ∀ {V : ℕ → Set} → TypeContext V → TypeContext V → TypeContext V
Γ ,,++ ∅ = Γ
Γ ,,++ (Δ ,, d) = (Γ ,,++ Δ) ,, d

-- Γ ,,++ ∅ = Γ
-- ∅ ,,++ Δ = Δ
-- Γ ,,++ (Δ ,, d) = (Γ ,,++ Δ) ,, d

-- _,,++_ : FunCtx → FunCtx → FunCtx
-- Γ ,,++ ∅ = Γ
-- ∅ ,,++ Δ = Δ
-- Γ ,,++ (Δ ,, d) = (Γ ,,++ Δ) ,, d

-- -- context lookup relation 
data _∋_ : ∀ {V : ℕ → Set} {k : ℕ} → TypeContext V → V k → Set where
  lookupZ : ∀ {V : ℕ → Set} {k : ℕ} {Γ : TypeContext V} {v : V k}
            → (Γ ,, v) ∋ v

  -- names are different 
  lookupDiffId : ∀ {V : ℕ → Set} {k : ℕ} {Γ : TypeContext V} {v v' : V k}
            → v ≢ v' -- later variables 'overwrite' earlier ones
            → Γ ∋ v
            → (Γ ,, v') ∋ v

  -- (v ,, v' ,, v) ∋ v 
  -- 

  -- arities are different
            -- need this because v ≢ v' doesn't even type-check unless k = j
  lookupDiffArity : ∀ {V : ℕ → Set} {k j : ℕ} {Γ : TypeContext V} {v : V k} {v' : V j}
                    → k ≢ j
                    → Γ ∋ v
                    → (Γ ,, v') ∋ v



-- variable cannot be in an empty context 
-- -- easy to prove since none of the constructors 
-- -- for _∋_ produce ∅ ∋ φ 
notemptyTC : ∀ {k} {φ : TCVar k} → (∅tc ∋ φ) → ⊥
notemptyTC () 

notemptyFV : ∀ {k} {φ : FVar k} → (∅fv ∋ φ) → ⊥
notemptyFV () 

-- If we know that (Γ ,, v) ∋ v' and v ≢ v' , we can deduce Γ ∋ v'
diffArityTC : ∀ {k j : ℕ} (Γ : TCCtx) → (v : TCVar k) → (v' : TCVar j)
            → k ≢ j
            → (Γ ,, v) ∋ v'
            → Γ ∋ v'
diffArityTC Γ (v ^T k) (.v ^T .k) k≢j lookupZ = exFalso' k≢j
diffArityTC Γ (v ^T k) (v' ^T .k) k≢j (lookupDiffId _ _) = exFalso' k≢j
diffArityTC Γ (v ^T k) (v' ^T j) k≢j (lookupDiffArity _ Γ∋v') = Γ∋v'

diffIdTC : ∀ {k : ℕ} (Γ : TCCtx) → (v v' : Id)
             → v ≢ v'
             → (Γ ,, (v ^T k)) ∋ (v' ^T k)
             → Γ ∋ (v' ^T k)
diffIdTC Γ v .v v≢v' lookupZ = exFalso' v≢v'
diffIdTC Γ v v' v≢v' (lookupDiffId _ Γ∋v') = Γ∋v'
diffIdTC Γ v v' v≢v' (lookupDiffArity _ Γ∋v') = Γ∋v'

diffArityFun : ∀ {k j : ℕ} {Φ : FunCtx} → {v : FVar k} → {v' : FVar j}
            → k ≢ j
            → (Φ ,, v) ∋ v'
            → Φ ∋ v'
diffArityFun k≢j lookupZ = exFalso' k≢j
diffArityFun k≢j (lookupDiffId _ _) = exFalso' k≢j
diffArityFun k≢j (lookupDiffArity _ Φ∋v') = Φ∋v'

diffIdFun : ∀ {k : ℕ} {Φ : FunCtx} → {v v' : Id}
             → v ≢ v'
             → (Φ ,, (v ^F k)) ∋ (v' ^F k)
             → Φ ∋ (v' ^F k)
diffIdFun v≢v' lookupZ = exFalso' v≢v'
diffIdFun v≢v' (lookupDiffId _ Φ∋v') = Φ∋v'
diffIdFun v≢v' (lookupDiffArity _ Φ∋v') = Φ∋v'


-- lookupZcong : ∀ {k : 𝕟}

-- decidable context lookup
lookupTC : ∀ {k : ℕ}  → (Γ : TCCtx) → (v : TCVar k) → Dec (Γ ∋ v)
lookupTC ∅ v = false because (ofⁿ λ())
lookupTC (Γ ,, (φ ^T k)) (ψ ^T j) with eqNat k j | φ ≟ ψ | lookupTC Γ (ψ ^T j)
... | no k≢j | _ | yes Γ∋ψ = true because (ofʸ (lookupDiffArity (≢-sym k≢j) Γ∋ψ))
... | no k≢j | _ | no ¬p = false because (ofⁿ (λ Γ,φ∋ψ → ¬p (diffArityTC Γ (φ ^T k) (ψ ^T j) k≢j  Γ,φ∋ψ)))
-- ... | no k≢j | yes refl = {!   !}
... | yes refl | .true because ofʸ refl | _ = true because (ofʸ lookupZ)
... | yes refl | no ¬p | .true because ofʸ Γ∋ψ = true because (ofʸ (lookupDiffId (λ ψ≡φ → ¬p (cong-^T (sym ψ≡φ))) Γ∋ψ)) -- true because (ofʸ (lookupDiffArity (≢-sym k≢j) Γ∋ψ))
... | yes refl | no ¬p | .false because ofⁿ ¬q = false because (ofⁿ (λ Γ,φ∋ψ → ¬q (diffIdTC Γ φ ψ ¬p Γ,φ∋ψ)))

lookupFV : ∀ {k : ℕ}  → (Γ : FunCtx) → (v : FVar k) → Dec (Γ ∋ v)
lookupFV ∅ v = false because (ofⁿ λ())
lookupFV (Γ ,, (φ ^F k)) (ψ ^F j) with eqNat k j | φ ≟ ψ | lookupFV Γ (ψ ^F j)
... | no k≢j | _ | yes Γ∋ψ = true because (ofʸ (lookupDiffArity (≢-sym k≢j) Γ∋ψ))
... | no k≢j | _ | no ¬p = false because (ofⁿ (λ Γ,φ∋ψ → ¬p (diffArityFun k≢j Γ,φ∋ψ)))
... | yes refl | .true because ofʸ refl | _ = true because (ofʸ lookupZ)
... | yes refl | no ¬p | .true because ofʸ Γ∋ψ = true because (ofʸ (lookupDiffId (λ ψ≡φ → ¬p (cong-^F (sym ψ≡φ))) Γ∋ψ)) -- true because (ofʸ (lookupDiffArity (≢-sym k≢j) Γ∋ψ))
... | yes refl | no ¬p | .false because ofⁿ ¬q = false because (ofⁿ (λ Γ,φ∋ψ → ¬q (diffIdFun ¬p Γ,φ∋ψ)))


-- well typed expressions
-- _≀_ - \wr
infix 5 _≀_⊢_

data _≀_⊢_ : TCCtx → FunCtx → TypeExpr → Set where
  𝟘-I : ∀ {Γ : TCCtx} {Φ : FunCtx} → Γ ≀ Φ ⊢ 𝟘
  𝟙-I : ∀ {Γ : TCCtx} {Φ : FunCtx} → Γ ≀ Φ ⊢ 𝟙

  --
  -- NOTE that here is an example of why it is convenient
  -- to have the arity of variables included in the type 
  AppT-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ} {φ : TCVar k}
             → (Γ∋φ : Γ ∋ φ)
             -- → (Fs : Vec (Σ TypeExpr (λ F → Γ ≀ Φ ⊢ F)) k)
             → (Fs : Vec TypeExpr k)
             → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
             → Γ ≀ Φ ⊢ AppT φ [ Fs ]

  -- application of functorial variable
  AppF-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ} {φ : FVar k}
             → (Φ∋φ : Φ ∋ φ)
             -- → (Fs : Vec (Σ TypeExpr (λ F → Γ ≀ Φ ⊢ F)) k)
             → (Fs : Vec TypeExpr k)
             → (⊢Fs : foreach (λ F → Γ ≀ Φ ⊢ F) Fs)
             → Γ ≀ Φ ⊢ AppF φ [ Fs ]

  +-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {F G : TypeExpr}
        → (⊢F : Γ ≀ Φ ⊢ F)
        → (⊢G : Γ ≀ Φ ⊢ G)
        → Γ ≀ Φ ⊢ F + G

  ×-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {F G : TypeExpr}
        → (⊢F : Γ ≀ Φ ⊢ F)
        → (⊢G : Γ ≀ Φ ⊢ G)
        → Γ ≀ Φ ⊢ F × G

  -- Nat type is primitive type of natural transformations.
  -- Nat type requires F and G to be formed in Gamma
  -- with alphas in functorial context
  Nat-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ} {αs : Vec (FVar 0) k}
            {F G : TypeExpr}
          → (⊢F : Γ ≀ ( ∅ ,++ αs ) ⊢ F)
          → (⊢G : Γ ≀ ( ∅ ,++ αs ) ⊢ G)
          -- -- NOTE mention this decision in thesis
          -- shouldn't we require that αs are disjoint from Φ?
          -- but then we can't prove that weakening preserves typing
          -- do we really need them to be disjoint?
          -- if αs = α and Φ = α,
          -- it won't ever be ambiguous which α is being referred
          -- to in F or G -- it will be the bound one.
          → Γ ≀ Φ ⊢ Nat^ αs [ F , G ]

{-
  -- mu intro - without gammas
  μ-I : ∀ {Γ : TCCtx} {Φ : FunCtx}
          -- k is arity of φ, number of alphas, number of Gs
          {k : ℕ} {φ : FVar k} 
          {αs : Vec (FVar 0) k}
          → (F : TypeExpr)
          → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ F)
          → (Gs : Vec TypeExpr k)
          → (⊢Gs : foreach (λ G → Γ ≀ Φ ⊢ G) Gs)
          → Γ ≀ Φ ⊢ μ φ [λ αs , F ] Gs
          -}

  -- mu intro - without gammas
  μ-I : ∀ {Γ : TCCtx} {Φ : FunCtx}
          -- k is arity of φ, number of alphas, number of Gs
          {k : ℕ} {φ : FVar k} 
          {αs : Vec (FVar 0) k} {F : TypeExpr}
          → (⊢F : Γ ≀ (∅ ,++ αs) ,, φ  ⊢ F)
          → (Gs : Vec TypeExpr k)
          → (⊢Gs : foreach (λ G → Γ ≀ Φ ⊢ G) Gs)
          → Γ ≀ Φ ⊢ μ φ [λ αs , F ] Gs


∋-resp-weakTC :  ∀ {m n : ℕ} {Γ : TCCtx} (α : TCVar n)
                → (φ : TCVar m)
                → Γ ∋ φ
                → (Γ ,, α) ∋ φ
∋-resp-weakTC (α ^T n) (φ ^T m) Γ∋φ with eqNat m n | α ≟ φ
... | .true because ofʸ refl | .true because ofʸ refl = lookupZ
... | .true because ofʸ refl | .false because ofⁿ α≢φ = lookupDiffId (≢-TCVar φ α (≢-sym α≢φ)) Γ∋φ
... | .false because ofⁿ m≢n | _                      = lookupDiffArity m≢n Γ∋φ


∋-resp-weakFV :  ∀ {m n : ℕ} {Φ : FunCtx} (α : FVar n)
                → (φ : FVar m)
                → Φ ∋ φ
                → (Φ ,, α) ∋ φ
∋-resp-weakFV (α ^F n) (φ ^F m) Φ∋φ with eqNat m n | α ≟ φ
... | .true because ofʸ refl | .true because ofʸ refl = lookupZ
... | .true because ofʸ refl | .false because ofⁿ α≢φ = lookupDiffId (≢-FVar φ α (≢-sym α≢φ)) Φ∋φ
... | .false because ofⁿ m≢n | _                      = lookupDiffArity m≢n Φ∋φ

∋-resp-weakFV-vec :  ∀ {m n k : ℕ} {Φ : FunCtx} (αs : Vec (FVar k) n)
                → (φ : FVar m)
                → Φ ∋ φ
                → (Φ ,++ αs) ∋ φ
∋-resp-weakFV-vec [] φ n = n
∋-resp-weakFV-vec (α ∷ αs) φ Φ∋φ = ∋-resp-weakFV α φ (∋-resp-weakFV-vec αs φ Φ∋φ)


FunCtx-∋-weaken-,++ : ∀ {k n j} → {Φ : FunCtx} → (φs : Vec (FVar k) n) → (ψ : FVar j)
                      → Φ ∋ ψ
                      → (Φ ,++ φs) ∋ ψ
FunCtx-∋-weaken-,++ [] ψ Φ∋ψ = Φ∋ψ
FunCtx-∋-weaken-,++ (φ ∷ φs) ψ Φ∋ψ = ∋-resp-weakFV φ ψ (FunCtx-∋-weaken-,++ φs ψ Φ∋ψ)

FunCtx-∋-weaken-,++-mid : ∀ {k n m j} → {Φ : FunCtx} → (φs : Vec (FVar k) n) → (ψ : FVar j) → (p : FVar m)
                      → (Φ ,++ φs) ∋ p
                      → ((Φ ,, ψ) ,++ φs) ∋ p
FunCtx-∋-weaken-,++-mid [] ψ p Φ,φs∋ψ = ∋-resp-weakFV ψ p Φ,φs∋ψ
FunCtx-∋-weaken-,++-mid (φ ∷ φs) ψ .φ lookupZ = lookupZ
FunCtx-∋-weaken-,++-mid (φ ∷ φs) ψ p (lookupDiffId p≢φ Φ,φs∋ψ) = lookupDiffId p≢φ (FunCtx-∋-weaken-,++-mid φs ψ p Φ,φs∋ψ)
FunCtx-∋-weaken-,++-mid (φ ∷ φs) ψ p (lookupDiffArity m≢k Φ,φs∋ψ) = lookupDiffArity m≢k (FunCtx-∋-weaken-,++-mid φs ψ p Φ,φs∋ψ)


FunCtx-∋-++ : ∀ {k j p : ℕ} (αs : Vec (FVar 0) k) (βs : Vec (FVar 0) j) (φ : FVar p)
           → ( ∅fv ,++ (αs ++ βs))   ∋ φ
           → (( ∅fv ,++ αs ) ,++ βs) ∋ φ
FunCtx-∋-++ [] βs φ ∋φ = ∋φ
FunCtx-∋-++ (α ∷ αs) βs .α lookupZ = FunCtx-∋-weaken-,++ βs α lookupZ
FunCtx-∋-++ (α ∷ αs) βs φ (lookupDiffId φ≢α ∋φ) = FunCtx-∋-weaken-,++-mid βs α φ (FunCtx-∋-++ αs βs φ ∋φ)
FunCtx-∋-++ (α ∷ αs) βs φ (lookupDiffArity p≢0 ∋φ) = FunCtx-∋-weaken-,++-mid βs α φ (FunCtx-∋-++ αs βs φ ∋φ)


{-# TERMINATING #-}
-- form a Nat type in a slightly different context 
FunCtx-resp-++ : ∀ {Γ : TCCtx} {k j : ℕ} (αs : Vec (FVar 0) k) (βs : Vec (FVar 0) j)
             {F : TypeExpr}
           → Γ ≀ ( ∅ ,++ (αs ++ βs)) ⊢ F
           → Γ ≀ ( ∅ ,++ αs ) ,++ βs ⊢ F
FunCtx-resp-++ αs βs 𝟘-I = 𝟘-I
FunCtx-resp-++ αs βs 𝟙-I = 𝟙-I
FunCtx-resp-++ αs βs (AppT-I Γ∋φ Fs ⊢Fs) = AppT-I Γ∋φ Fs (foreach-preserves (λ F ⊢F → FunCtx-resp-++ αs βs ⊢F) Fs ⊢Fs)
FunCtx-resp-++ αs βs (AppF-I {φ = φ} αs,βs∋φ Fs ⊢Fs) = AppF-I (FunCtx-∋-++ αs βs φ αs,βs∋φ) Fs (foreach-preserves (λ F ⊢F → FunCtx-resp-++ αs βs ⊢F) Fs ⊢Fs)
FunCtx-resp-++ αs βs (+-I ⊢F ⊢G) = +-I (FunCtx-resp-++ αs βs ⊢F) (FunCtx-resp-++ αs βs ⊢G)
FunCtx-resp-++ αs βs (×-I ⊢F ⊢G) = ×-I (FunCtx-resp-++ αs βs ⊢F) (FunCtx-resp-++ αs βs ⊢G)
FunCtx-resp-++ αs βs (Nat-I ⊢F ⊢G) = Nat-I ⊢F ⊢G
FunCtx-resp-++ αs βs (μ-I ⊢F Gs ⊢Gs) = μ-I ⊢F Gs (foreach-preserves (λ G ⊢G → FunCtx-resp-++ αs βs ⊢G) Gs ⊢Gs)


-- first-order substitution
mutual
  _[_:=_] : TypeExpr → FVar 0 → TypeExpr → TypeExpr
  𝟘 [ α := H ] = 𝟘
  𝟙 [ α := H ] = 𝟙
  -- identity on Nat^ types because α is functorial variable
  -- and Nat^ binds all fvars in F and G
  Nat^ βs [ F , G ] [ α := H ] = Nat^ βs [ F  , G ]
  (F + G) [ α := H ] = (F [ α := H ]) + (G [ α := H ])
  (F × G) [ α := H ] = (F [ α := H ]) × (G [ α := H ])
  AppT φ [ Gs ] [ α := H ] = AppT φ [ substVec Gs α H ]


  -- AppF φ ^F 0     [ [] ] [ α ^F 0 := H ] with φ ≟ α
  -- ... | .true because ofʸ φ≡α = H
  -- ... | .false because ofⁿ ¬φ≡α = AppF φ ^F 0 [ [] ]
  -- AppF φ ^F suc k [ Gs ] [ α := H ] = AppF φ ^F suc k [ substVec Gs α H ]


  AppF φ ^F k [ Gs ] [ (α ^F j) := H ] with eqNat k j | φ ≟ α 
  ... | yes refl | yes refl = H 
  ... | _ | _  = AppF (φ ^F k) [ substVec Gs (α ^F j) H ] 

  -- no recursive substitution of G because
  -- it only contains functorial variables that are bound by μ (βs and φ)
  (μ φ [λ βs , G ] Ks) [ α := H ] = μ φ [λ βs , G ] (substVec Ks α H)

  -- apply substitution to a vector of types.
  -- using Vec.map results in failure of termination check for Agda
  substVec : ∀ {n : ℕ} → Vec TypeExpr n → FVar 0 → TypeExpr → Vec TypeExpr n
  substVec [] α H = []
  substVec (G ∷ Gs) α H = (G [ α := H ]) ∷ substVec Gs α H





mutual
  substVec-preserves : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {α : FVar 0}
                        → (H : TypeExpr)
                        → (Gs : Vec TypeExpr k)
                        → Γ ≀ Φ ⊢ H
                        → foreach (λ G → Γ ≀ Φ ⊢ G [ α := H ]) Gs
                        → foreach (λ G → Γ ≀ Φ ⊢ G) (substVec Gs α H)
  substVec-preserves H [] ⊢H ⊢Gs = bigtt
  substVec-preserves H (G ∷ Gs) ⊢H (⊢G[α:=H] , ⊢Gs) = ⊢G[α:=H] , substVec-preserves H Gs ⊢H ⊢Gs

  -- {-# TERMINATING #-}
  foreach-preserves-subst : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {α : FVar 0}
                          → (H : TypeExpr)
                          → (Gs : Vec TypeExpr k)
                          → Γ ≀ Φ ⊢ H
                          → foreach (λ G → Γ ≀ Φ ,, α ⊢ G) Gs
                          → foreach (λ G → Γ ≀ Φ ⊢ G [ α := H ]) Gs
  -- foreach-preserves-subst H Gs ⊢H ⊢Gs = foreach-preserves (λ G ⊢G → fo-subst-preserves-typing G H ⊢G ⊢H) Gs ⊢Gs
  -- -- -- ^ this generalized version doesn't pass termination checking for some reason
  foreach-preserves-subst H [] ⊢H ⊢Gs = bigtt
  foreach-preserves-subst H (G ∷ Gs) ⊢H (⊢G , ⊢Gs) = (fo-subst-preserves-typing ⊢G ⊢H) , foreach-preserves-subst H Gs ⊢H ⊢Gs

  foreach-preserves-∋ : ∀ {k : ℕ}  {Φ : FunCtx} {α : FVar 0}
                        → (βs : Vec (FVar 0) k)
                        → foreach (λ β → ¬ ((Φ ,, α) ∋ β)) βs
                        → foreach (λ β → ¬ (Φ ∋ β)) βs
  foreach-preserves-∋ = foreach-preserves (λ β ¬Φ,α∋β → neg-∋-cong ¬Φ,α∋β)

  -- is this really a congruence? maybe give it a different name 
  -- 
  -- TODO this can be substd with in instance of contrapositive (∋-resp-weakFV ...)
  neg-∋-cong : ∀ {j k : ℕ} {Φ : FunCtx} {α : FVar j} {β : FVar k}
              → ¬ ((Φ ,, α) ∋ β)
              → ¬ (Φ ∋ β)
  neg-∋-cong {j = j} {k = k} ¬Φ,α∋β Φ∋β with eqNat j k
  ... | .true because ofʸ refl = ¬Φ,α∋β (lookupDiffId (λ { refl → ¬Φ,α∋β lookupZ }) Φ∋β)
  ... | .false because ofⁿ ¬j≡k = ¬Φ,α∋β (lookupDiffArity (≢-sym ¬j≡k) Φ∋β)


------------------------------------------------------
  fo-subst-preserves-typing : ∀ {Γ : TCCtx} {Φ : FunCtx} {α : FVar 0} {F H : TypeExpr}
                             → Γ ≀ (Φ ,, α) ⊢ F
                             → Γ ≀ Φ ⊢ H
                             → Γ ≀ Φ ⊢ F [ α := H ]
  fo-subst-preserves-typing 𝟘-I ⊢H = 𝟘-I
  fo-subst-preserves-typing 𝟙-I ⊢H = 𝟙-I
  fo-subst-preserves-typing (Nat-I ⊢F ⊢G) ⊢H = Nat-I ⊢F ⊢G
  fo-subst-preserves-typing (+-I ⊢F ⊢G) ⊢H = +-I (fo-subst-preserves-typing ⊢F ⊢H) (fo-subst-preserves-typing ⊢G ⊢H)
  fo-subst-preserves-typing (×-I ⊢F ⊢G) ⊢H = ×-I (fo-subst-preserves-typing ⊢F ⊢H) (fo-subst-preserves-typing ⊢G ⊢H)

  fo-subst-preserves-typing {α = α} {H = H} (AppT-I Γ∋φ Gs ⊢Gs) ⊢H = AppT-I Γ∋φ (substVec Gs α H) (substVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs)) 


  fo-subst-preserves-typing {α = α ^F j} {H = H} (AppF-I {φ = φ ^F k} Φ,α∋φ Gs ⊢Gs) ⊢H with eqNat k j | φ ≟ α 
  ... | yes refl | yes refl = ⊢H
  ... | yes refl | no φ≢α   = AppF-I (diffIdFun (≢-sym φ≢α) Φ,α∋φ) (substVec Gs (α ^F zero) H) (substVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs))
  ... | no k≢j   | _ = AppF-I (diffArityFun (≢-sym k≢j) Φ,α∋φ) (substVec Gs (α ^F zero) H) ((substVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs)))


  -- -- OG AppF case 
  -- fo-subst-preserves-typing {α = α ^F 0} (AppF-I {φ = φ ^F 0} Φ,α∋φ [] ⊤) ⊢H with φ ≟ α
  -- ... | yes refl = ⊢H
  -- ... | no ¬φ≡α = AppF-I (diffIdFun (≢-sym ¬φ≡α) Φ,α∋φ) [] bigtt
  -- fo-subst-preserves-typing {α = α ^F 0} {H = H} (AppF-I {φ = φ ^F suc k} Φ,α∋φ (G ∷ Gs) (⊢G , ⊢Gs)) ⊢H = 
  --   AppF-I (diffArityFun (λ()) Φ,α∋φ) ((G [ (α ^F 0) := H ]) ∷ substVec Gs (α ^F 0) H)
  --           ((fo-subst-preserves-typing ⊢G ⊢H) , (substVec-preserves H Gs ⊢H (foreach-preserves-subst H Gs ⊢H ⊢Gs)))



  fo-subst-preserves-typing {α = α} {H = H} (μ-I ⊢G Ks ⊢Ks ) ⊢H =
    μ-I ⊢G  (substVec Ks α H)
    (substVec-preserves H Ks ⊢H (foreach-preserves-subst H Ks ⊢H ⊢Ks))


      -- (foreach-preserves-∋ βs bind-βs) (neg-∋-cong bind-φ)
      -- not using this function -- was going to use it for recursive substitution of G but that is now removed
      -- since there are no more γs appearing in body of mu type
      --   where help : ∀ {k n : ℕ} {Φ : FunCtx} { βs : Vec (FVar 0) n} {φ : FVar k} {α : FVar 0}
      --                 → ¬ ((Φ ,, α) ∋ φ)
      --                 → ¬ (Φ ∋ α)
      --                 → ¬ ((Φ ,, φ) ∋ α)
      --         help {k = zero} {φ = φ ^F .0} {α = α ^F .0} ¬Φ,α∋φ ¬Φ∋α Φ,φ∋α with φ ≟ α
      --         ... | .true because ofʸ refl = ¬Φ,α∋φ Φ,φ∋α
      --         ... | .false because ofⁿ φ≢α = φ≢α (exFalso (¬Φ∋α (diffIdFun φ≢α Φ,φ∋α)))
      --         -- help {k = suc k} {φ = φ} {α = α} ¬Φ,α∋φ ¬Φ∋α p = neg-∋-cong ¬Φ,α∋φ (diffArityFun (λ()) (exFalso (¬Φ∋α (diffArityFun (λ()) p))))
      --         help {k = suc k} {φ = φ} {α = α} ¬Φ,α∋φ ¬Φ∋α Φ,φ∋α = exFalso (¬Φ∋α (diffArityFun (λ()) Φ,φ∋α))

  -- actually we don't need ¬Γ∋φ to prove this
  weakenTCCtx : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {F : TypeExpr} (φ : TCVar k) 
                  → Γ ≀ Φ ⊢ F
                  → Γ ,, φ ≀ Φ ⊢ F
  weakenTCCtx  φ 𝟘-I = 𝟘-I
  weakenTCCtx  φ 𝟙-I = 𝟙-I
  weakenTCCtx  φ  (Nat-I ⊢F ⊢G) = Nat-I (weakenTCCtx  φ ⊢F ) (weakenTCCtx φ ⊢G) 
  weakenTCCtx  φ (+-I ⊢F ⊢G) = +-I (weakenTCCtx  φ ⊢F) (weakenTCCtx  φ ⊢G)
  weakenTCCtx  φ (×-I ⊢F ⊢G) = ×-I (weakenTCCtx  φ ⊢F) (weakenTCCtx  φ ⊢G)
  weakenTCCtx  {Γ = Γ} (φ ^T k) (AppT-I {φ = ψ ^T j} Γ∋ψ Gs ⊢Gs) with eqNat k j | φ ≟ ψ
  -- if k = j and φ = ψ
  ... | .true because ofʸ refl | .true because ofʸ refl = AppT-I lookupZ Gs (foreach-preserves-weakening  Gs ⊢Gs)
  -- otherwise.. 
  ... | .true because ofʸ refl | .false because ofⁿ ¬p = AppT-I (lookupDiffId (≢-TCVar ψ φ (≢-sym ¬p)) Γ∋ψ) Gs (foreach-preserves-weakening  Gs ⊢Gs)
  ... | .false because ofⁿ k≢j | _ =  AppT-I (lookupDiffArity (≢-sym k≢j) Γ∋ψ) Gs (foreach-preserves-weakening  Gs ⊢Gs)
  weakenTCCtx  φ (AppF-I Φ∋ψ Gs ⊢Gs) = AppF-I Φ∋ψ Gs (foreach-preserves-weakening  Gs ⊢Gs)
  weakenTCCtx  φ (μ-I ⊢F Gs ⊢Gs) = μ-I (weakenTCCtx  φ ⊢F)  Gs (foreach-preserves-weakening  Gs ⊢Gs)


  weakenTCCtxVec :  ∀ {k n : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φs : Vec (TCVar k) n)  (F : TypeExpr)
                    → Γ ≀ Φ ⊢ F
                    -- → (¬ (Γ ∋ φ))
                    → Γ ,++ φs ≀ Φ ⊢ F
  weakenTCCtxVec {n = zero} [] F ⊢F = ⊢F
  weakenTCCtxVec {n = suc n} (φ ∷ φs) F ⊢F = weakenTCCtx  φ (weakenTCCtxVec φs F ⊢F)

  weakenFunCtxVec :  ∀ {k n : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φs : Vec (FVar k) n)  (F : TypeExpr)
                    → Γ ≀ Φ ⊢ F
                    → Γ ≀ Φ ,++ φs ⊢ F
  weakenFunCtxVec {n = zero} [] F ⊢F = ⊢F
  -- weakenFunCtxVec {n = suc n} (φ ∷ φs) F ⊢F = weakenFunCtxVec φs F (weakenFunCtx  φ F ⊢F)
  weakenFunCtxVec {n = suc n} (φ ∷ φs) F ⊢F = weakenFunCtx  φ (weakenFunCtxVec φs F ⊢F)

  -- {-# TERMINATING #-}
  foreach-preserves-weakening  : ∀ {k n : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : TCVar k}
                                    → (Gs : Vec TypeExpr n)
                                    → foreach (λ G → Γ ≀ Φ ⊢ G) Gs
                                    → foreach (λ G → Γ ,, φ ≀ Φ ⊢ G) Gs
  -- foreach-preserves-weakening  {φ = φ} = foreach-preserves (λ G ⊢G → weakenTCCtx φ G ⊢G)
  foreach-preserves-weakening {φ = φ} [] _ = bigtt
  foreach-preserves-weakening {φ = φ} (G ∷ Gs) (⊢G , ⊢Gs) = (weakenTCCtx φ ⊢G) , (foreach-preserves-weakening Gs ⊢Gs) 

  weakenFunCtx : ∀ {k : ℕ} { Γ : TCCtx } {Φ : FunCtx} {F : TypeExpr} (φ : FVar k)
                  → Γ ≀ Φ ⊢ F
                  → Γ ≀ Φ ,, φ ⊢ F
  weakenFunCtx  φ 𝟘-I = 𝟘-I
  weakenFunCtx  φ 𝟙-I = 𝟙-I
  weakenFunCtx  φ (Nat-I ⊢F ⊢G ) = Nat-I ⊢F ⊢G
  weakenFunCtx  φ (+-I ⊢F ⊢G) = +-I (weakenFunCtx  φ ⊢F ) (weakenFunCtx  φ ⊢G )
  weakenFunCtx  φ (×-I ⊢F ⊢G) = ×-I (weakenFunCtx  φ ⊢F ) (weakenFunCtx  φ ⊢G )
  weakenFunCtx  {Γ = Γ} (φ) (AppT-I Γ∋ψ Gs ⊢Gs) = AppT-I Γ∋ψ Gs (foreach-preserves-weakening-FV  Gs ⊢Gs)
  -- weakenFunCtx  {Γ = Γ} (φ ^F k) AppT (ψ ^T j) [ Gs ] (AppT-I Γ∋ψ .Gs ⊢Gs) = AppT-I Γ∋ψ Gs (foreach-preserves-weakening-FV  Gs ⊢Gs)

  weakenFunCtx  (φ ^F k) (AppF-I {φ = ψ ^F j} Φ∋ψ Gs ⊢Gs) with eqNat k j | φ ≟ ψ
  ... | yes refl | yes refl = AppF-I lookupZ Gs (foreach-preserves-weakening-FV  Gs ⊢Gs)
  ... | yes refl | no φ≢ψ   = AppF-I (lookupDiffId (≢-FVar ψ φ (≢-sym φ≢ψ)) Φ∋ψ) Gs (foreach-preserves-weakening-FV Gs ⊢Gs)
  ... | no k≢j   | _        = AppF-I (lookupDiffArity (≢-sym k≢j) Φ∋ψ) Gs (foreach-preserves-weakening-FV  Gs ⊢Gs)



  weakenFunCtx  φ (μ-I ⊢F Gs ⊢Gs ) =
      μ-I ⊢F Gs (foreach-preserves-weakening-FV  Gs ⊢Gs)



  weakenFunCtximpl  : ∀ {k : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φ : FVar k) → {F : TypeExpr}
                  → Γ ≀ Φ ⊢ F
                  → Γ ≀ Φ ,, φ ⊢ F
  weakenFunCtximpl  φ {F} ⊢F = weakenFunCtx φ ⊢F 

  weakenFunCtx-∅  : ∀ { Γ : TCCtx } → (Φ : FunCtx) 
                  → {F : TypeExpr} → Γ ≀ ∅ ⊢ F
                  → Γ ≀ Φ ⊢ F
  weakenFunCtx-∅ ∅ ⊢F = ⊢F 
  weakenFunCtx-∅ (Φ ,, φ) ⊢F = weakenFunCtximpl φ (weakenFunCtx-∅ Φ ⊢F)

-- :%s/FunCtx-∋-weaken-,++/FunCtx-∋-weaken-∅,++/g
  FunCtx-∋-weaken-∅,++ : ∀ {k n j} → {Φ : FunCtx} → (φs : Vec (FVar k) n) → (ψ : FVar j)
                       → (∅fv ,++ φs) ∋ ψ
                       → (Φ ,++ φs) ∋ ψ
  FunCtx-∋-weaken-∅,++ (φ ∷ φs) .φ lookupZ = lookupZ
  FunCtx-∋-weaken-∅,++ (φ ∷ φs) ψ (lookupDiffId ψ≢φ φs∋ψ) = lookupDiffId ψ≢φ (FunCtx-∋-weaken-∅,++ φs ψ φs∋ψ)
  FunCtx-∋-weaken-∅,++ (φ ∷ φs) ψ (lookupDiffArity j≢k φs∋ψ) = lookupDiffArity j≢k (FunCtx-∋-weaken-∅,++ φs ψ φs∋ψ) 


  weakenFunCtx-∅-,++  : ∀ {k n} { Γ : TCCtx } {Φ : FunCtx} → (φs : Vec (FVar k) n)
                  → {F : TypeExpr} → Γ ≀ (∅ ,++ φs) ⊢ F
                  → Γ ≀ (Φ ,++ φs) ⊢ F
  weakenFunCtx-∅-,++ φs 𝟘-I = 𝟘-I
  weakenFunCtx-∅-,++ φs 𝟙-I = 𝟙-I
  weakenFunCtx-∅-,++ φs (AppT-I Γ∋φ Fs ⊢Fs) = AppT-I Γ∋φ Fs (foreach-preserves (λ F ⊢F → weakenFunCtx-∅-,++ φs ⊢F) Fs ⊢Fs)
  weakenFunCtx-∅-,++ φs (AppF-I {φ = φ} Φ∋φ Fs ⊢Fs) = AppF-I (FunCtx-∋-weaken-∅,++ φs φ Φ∋φ) Fs (foreach-preserves (λ F ⊢F → weakenFunCtx-∅-,++ φs ⊢F) Fs ⊢Fs)
  weakenFunCtx-∅-,++ φs (+-I ⊢F ⊢G) = +-I (weakenFunCtx-∅-,++ φs ⊢F) (weakenFunCtx-∅-,++ φs ⊢G)
  weakenFunCtx-∅-,++ φs (×-I ⊢F ⊢G) = ×-I (weakenFunCtx-∅-,++ φs ⊢F) (weakenFunCtx-∅-,++ φs ⊢G)
  weakenFunCtx-∅-,++ φs (Nat-I ⊢F ⊢G) = Nat-I ⊢F ⊢G
  weakenFunCtx-∅-,++ φs (μ-I ⊢F Gs ⊢Gs) = μ-I ⊢F Gs ((foreach-preserves (λ G ⊢G → weakenFunCtx-∅-,++ φs ⊢G) Gs ⊢Gs))


  FunCtx-∋-swap : ∀ {k j n} {Φ : FunCtx} {φ : FVar k} {ψ : FVar j} {p : FVar n}
                  → ((Φ ,, φ) ,, ψ) ∋ p 
                  → ((Φ ,, ψ) ,, φ) ∋ p 
  FunCtx-∋-swap {φ  = (φ ^F k)} {ψ = (ψ ^F j)} lookupZ with eqNat k j | φ ≟ ψ 
  ... | yes refl | yes refl = lookupZ 
  ... | no k≢j   | _ = lookupDiffArity (≢-sym k≢j) lookupZ 
  ... | yes refl | no φ≢ψ = lookupDiffId (≢-sym (≢-FVar φ ψ φ≢ψ)) lookupZ 
  FunCtx-∋-swap  (lookupDiffId _ lookupZ) = lookupZ
  FunCtx-∋-swap (lookupDiffId p≢ψ (lookupDiffId p≢φ Φ∋p)) = lookupDiffId p≢φ (lookupDiffId p≢ψ Φ∋p)
  FunCtx-∋-swap (lookupDiffId p≢ψ (lookupDiffArity j≢k Φ∋p)) = lookupDiffArity j≢k (lookupDiffId p≢ψ Φ∋p)
  FunCtx-∋-swap  (lookupDiffArity _ lookupZ) = lookupZ
  FunCtx-∋-swap (lookupDiffArity k≢j (lookupDiffId p≢φ Φ∋p)) = lookupDiffId p≢φ (lookupDiffArity k≢j Φ∋p)
  FunCtx-∋-swap (lookupDiffArity k≢j (lookupDiffArity n≢k Φ∋p)) = lookupDiffArity n≢k (lookupDiffArity k≢j Φ∋p) 


  {-# TERMINATING #-}
  FunCtx-,,-swap : ∀ {k j} { Γ : TCCtx } → (Φ : FunCtx) (φ : FVar k) (ψ : FVar j)
                  → {F : TypeExpr} → Γ ≀ (Φ ,, φ) ,, ψ ⊢ F
                  → Γ ≀ (Φ ,, ψ) ,, φ ⊢ F
  FunCtx-,,-swap Φ φ ψ 𝟘-I = 𝟘-I
  FunCtx-,,-swap Φ φ ψ 𝟙-I = 𝟙-I
  FunCtx-,,-swap Φ φ ψ (AppT-I {φ = p} Γ∋p Fs ⊢Fs) = AppT-I Γ∋p Fs ((foreach-preserves (λ F ⊢F → FunCtx-,,-swap Φ φ ψ ⊢F) Fs ⊢Fs))
  FunCtx-,,-swap Φ φ ψ (AppF-I {φ = p} Φ∋p Fs ⊢Fs) = AppF-I (FunCtx-∋-swap Φ∋p) Fs ((foreach-preserves (λ F ⊢F → FunCtx-,,-swap Φ φ ψ ⊢F) Fs ⊢Fs))
  FunCtx-,,-swap Φ φ ψ (+-I ⊢F ⊢G) = +-I (FunCtx-,,-swap Φ φ ψ ⊢F) (FunCtx-,,-swap Φ φ ψ ⊢G)
  FunCtx-,,-swap Φ φ ψ (×-I ⊢F ⊢G) = ×-I (FunCtx-,,-swap Φ φ ψ ⊢F) (FunCtx-,,-swap Φ φ ψ ⊢G)
  FunCtx-,,-swap Φ φ ψ (Nat-I ⊢F ⊢G) = Nat-I ⊢F ⊢G
  FunCtx-,,-swap Φ φ ψ (μ-I ⊢F Gs ⊢Gs) = μ-I ⊢F Gs (foreach-preserves (λ G ⊢G → FunCtx-,,-swap Φ φ ψ ⊢G) Gs ⊢Gs)

  weakenFunCtx-,,++-right : ∀ { Γ : TCCtx } → (Φ Ψ : FunCtx) 
                  → {F : TypeExpr} → Γ ≀ Φ ⊢ F
                  → Γ ≀ Φ ,,++ Ψ ⊢ F
  weakenFunCtx-,,++-right Φ ∅ ⊢F = ⊢F
  weakenFunCtx-,,++-right Φ (Ψ ,, ψ) ⊢F = weakenFunCtximpl ψ (weakenFunCtx-,,++-right Φ Ψ ⊢F) 

  -- weakenFunCtx-,,++-both : ∀ { Γ : TCCtx } → (Φ Ψ Ψ' : FunCtx) 
  --                 → {F : TypeExpr} → Γ ≀ Φ ⊢ F
  --                 → Γ ≀ (Ψ ,,++ Φ) ,,++ Ψ' ⊢ F
  -- weakenFunCtx-,,++-both Φ Ψ ∅ ⊢F = weakenFunCtx-,,++-left Φ Ψ ⊢F
  -- weakenFunCtx-,,++-both Φ Ψ (Ψ' ,, x) ⊢F = weakenFunCtximpl x (weakenFunCtx-,,++-both Φ Ψ Ψ' ⊢F)
  -- -- weakenFunCtx-,,++-both Φ ∅  Ψ' ⊢F = {!   !}
  -- -- weakenFunCtx-,,++-both Φ (Ψ ,, x) Ψ' ⊢F = {!   !}


  -- weakenFunCtx-,,-left : ∀ {k} { Γ : TCCtx } → (Φ : FunCtx) (φ : FVar k)
  --                 → {F : TypeExpr} → Γ ≀ Φ ⊢ F
  --                 → Γ ≀ (∅ ,, φ) ,,++ Φ ⊢ F
  -- weakenFunCtx-,,-left ∅ φ ⊢F = weakenFunCtximpl φ ⊢F
  -- weakenFunCtx-,,-left (Φ ,, x) φ ⊢F = {!   !} 




  -- {-# TERMINATING #-}
  foreach-preserves-weakening-FV  : ∀ {k n : ℕ} {Γ : TCCtx } {Φ : FunCtx} {φ : FVar k}
                                    → (Gs : Vec TypeExpr n)
                                    → foreach (λ G → Γ ≀ Φ ⊢ G) Gs
                                    → foreach (λ G → Γ ≀ Φ ,, φ  ⊢ G) Gs
  -- foreach-preserves-weakening-FV  {φ = φ} = foreach-preserves (λ G ⊢G → weakenFunCtx  φ G ⊢G )
  foreach-preserves-weakening-FV {φ = φ} [] _ = bigtt
  foreach-preserves-weakening-FV {φ = φ} (G ∷ Gs) (⊢G , ⊢Gs) = (weakenFunCtx φ ⊢G) , (foreach-preserves-weakening-FV Gs ⊢Gs) 
--------------------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------




-- second order substitution
mutual

  _[_:=_]Vec : ∀ {k : ℕ} → TypeExpr → (Vec (FVar 0) k)  → (Vec TypeExpr k) → TypeExpr
  F [ [] := [] ]Vec = F
  F [ α ∷ αs := H ∷ Hs ]Vec = (F [ α := H ]) [ αs := Hs ]Vec


  {- -- works but not used

  ∋-resp-weak2 :  ∀ {n : ℕ} {Φ : FunCtx} (ψ φ : FVar n)
                  → ¬ (Φ ∋ φ)
                  → ¬ (ψ ≡ φ)
                  → ¬ ((Φ ,, ψ) ∋ φ)
  ∋-resp-weak2 ψ .ψ p q lookupZ = q refl
  ∋-resp-weak2 ψ φ p q (lookupDiffId x Φ∋φ) = p Φ∋φ
  ∋-resp-weak2 ψ φ p q (lookupDiffArity x Φ∋φ) = x refl
  -}

  diffIdSwap : ∀ {Φ : FunCtx} {α β : Id} {m p : ℕ} {φ : FVar p}
                 → (α ≢ β)
                 → (Φ ,, (β ^F m) ,, (α ^F m)) ∋ φ
                 → (Φ ,, (α ^F m) ,, (β ^F m)) ∋ φ
  diffIdSwap {α = α} {β = β} α≢β lookupZ = lookupDiffId (≢-FVar α β α≢β) lookupZ
  diffIdSwap α≢β (lookupDiffId x lookupZ) = lookupZ
  diffIdSwap α≢β (lookupDiffId x (lookupDiffId x₁ p)) = lookupDiffId x₁ (lookupDiffId x p)
  diffIdSwap α≢β (lookupDiffId x (lookupDiffArity x₁ p)) = exFalso (x₁ refl)
  diffIdSwap α≢β (lookupDiffArity x lookupZ) = lookupZ
  diffIdSwap α≢β (lookupDiffArity x (lookupDiffId x₁ p)) = exFalso (x refl)
  diffIdSwap α≢β (lookupDiffArity x (lookupDiffArity x₁ p)) = lookupDiffArity x₁ (lookupDiffArity x p)

  diffAritySwap : ∀ {Φ : FunCtx} {α β : Id} {n m p : ℕ} {φ : FVar p}
                 → (n ≢ m)
                 → (Φ ,, (α ^F n) ,, (β ^F m)) ∋ φ
                 → (Φ ,, (β ^F m) ,, (α ^F n)) ∋ φ
  diffAritySwap n≢m lookupZ = lookupDiffArity (≢-sym n≢m) lookupZ
  diffAritySwap n≢m (lookupDiffId x lookupZ) = exFalso (n≢m refl)
  diffAritySwap n≢m (lookupDiffId x (lookupDiffId x₁ q)) = lookupDiffId x₁ (lookupDiffId x q)
  diffAritySwap n≢m (lookupDiffId x (lookupDiffArity x₁ q)) = lookupDiffArity x₁ (lookupDiffId x q)
  diffAritySwap n≢m (lookupDiffArity x lookupZ) = lookupZ
  diffAritySwap n≢m (lookupDiffArity x (lookupDiffId x₁ q)) = lookupDiffId x₁ (lookupDiffArity x q)
  diffAritySwap n≢m (lookupDiffArity x (lookupDiffArity x₁ q)) = lookupDiffArity x₁ (lookupDiffArity x q)

  fo-substVec-preserves-typing : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} (αs : Vec (FVar 0) k) {H : TypeExpr} 
                               → (Gs : Vec TypeExpr k)
                               → Γ ≀ (Φ ,++ αs) ⊢ H
                               → foreach (λ G → Γ ≀ Φ ⊢ G) Gs
                               → Γ ≀ Φ ⊢ H [ αs := Gs ]Vec
  fo-substVec-preserves-typing []          []       ⊢H ⊢Gs = ⊢H
  fo-substVec-preserves-typing {k} {Γ} {Φ} (α ∷ αs) (G ∷ Gs) ⊢H (⊢G , ⊢Gs) = 
   let -- ⊢H : Γ ≀ (Φ ,++ αs) ,, α ⊢ H 
       -- ⊢H[α:=G] : Γ ≀ Φ ,++ αs ⊢ H [ α := G ]
       ⊢H[α:=G] = (fo-subst-preserves-typing ⊢H (weakenFunCtxVec αs G ⊢G)) 
      -- goal is : Γ ≀ Φ ⊢ ((H [ α := G ]) [ αs := Gs ]Vec)
      in fo-substVec-preserves-typing αs Gs ⊢H[α:=G] ⊢Gs 


  _[_:=[_]_] : ∀ {k : ℕ} → TypeExpr → (FVar k) → Vec (FVar 0) k → TypeExpr → TypeExpr
  -- when k = 0, higher-order subst coincides with first-order subst
  -- H [ (α ^F .0) :=[ [] ] F ] = H [ (α ^F 0) := F ]
  -- _[_:=[_]_] {k = zero} H (α ^F .0) [] F = H [ α ^F 0 := F ]

  {-# CATCHALL #-}
  𝟘 [ φ :=[ αs ] F ] = 𝟘
  {-# CATCHALL #-}
  𝟙 [ φ :=[ αs ] F ] = 𝟙
  {-# CATCHALL #-}
  Nat^ βs [ G , K ] [ φ :=[ αs ] F ] = Nat^ βs [ G  , K ]
  {-# CATCHALL #-}
  (G + K) [ φ :=[ αs ] F ] = (G [ φ :=[ αs ] F ]) + (K [ φ :=[ αs ] F ])
  {-# CATCHALL #-}
  (G × K) [ φ :=[ αs ] F ] = (G [ φ :=[ αs ] F ]) × (K [ φ :=[ αs ] F ])
  {-# CATCHALL #-}
  AppT ψ [ Gs ] [ φ :=[ αs ] F ] = AppT ψ [ so-substVec Gs φ αs F ]

  {-# CATCHALL #-}
  AppF ψ ^F j [ Gs ] [ φ ^F k :=[ αs ] F ] with ψ ≟ φ | eqNat k j
  ... | yes refl | yes refl = F [ αs := (so-substVec Gs (φ ^F k) αs F) ]Vec 
  ... | yes refl | no k≢j   = AppF (ψ ^F j) [ so-substVec Gs (φ ^F k) αs F ]
  ... | no ψ≢φ   | _        = AppF (ψ ^F j) [ so-substVec Gs (φ ^F k) αs F ]

  {-# CATCHALL #-}
  (μ ψ [λ βs , G ] Ks ) [ φ :=[ αs ] F ] = μ ψ [λ βs , G ] (so-substVec Ks φ αs F)



  so-substVec : ∀ {n k : ℕ} → Vec TypeExpr n → FVar k → Vec (FVar 0) k → TypeExpr → Vec TypeExpr n
  so-substVec [] φ αs F = []
  so-substVec (G ∷ Gs) φ αs F = (G [ φ :=[ αs ] F ]) ∷ so-substVec Gs φ αs F



mutual
  so-substVec-preserves : ∀ {n k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : FVar k} {αs : Vec (FVar 0) k}
                        → (H : TypeExpr)
                        → (Gs : Vec TypeExpr n)
                        → Γ ≀ (Φ ,++ αs) ⊢ H
                        → foreach (λ G → Γ ≀ Φ ,, φ ⊢ G) Gs
                        → foreach (λ G → Γ ≀ Φ ⊢ G) (so-substVec Gs φ αs H)
  so-substVec-preserves H [] ⊢H ⊢Gs = bigtt
  so-substVec-preserves H (G ∷ Gs) ⊢H (⊢G , ⊢Gs) = (so-subst-preserves-typing ⊢G ⊢H) , so-substVec-preserves H Gs ⊢H ⊢Gs

  so-subst-preserves-typing : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : FVar k} {αs : Vec (FVar 0) k} {F H : TypeExpr}
                             → Γ ≀ (Φ ,, φ) ⊢ F
                             → Γ ≀ (Φ ,++ αs) ⊢ H
                             → Γ ≀ Φ ⊢ F [ φ :=[ αs ] H ]
  -- so-subst-preserves-typing {k = zero} {φ = φ ^F 0} {αs = []} ⊢F ⊢H = fo-subst-preserves-typing ⊢F ⊢H

  so-subst-preserves-typing {k = k} 𝟘-I ⊢H = 𝟘-I
  so-subst-preserves-typing {k = k} 𝟙-I ⊢H = 𝟙-I
  so-subst-preserves-typing {k = k} (Nat-I ⊢F ⊢G) ⊢H = Nat-I ⊢F ⊢G
  so-subst-preserves-typing {k = k} (+-I ⊢F ⊢G) ⊢H = +-I (so-subst-preserves-typing ⊢F ⊢H) (so-subst-preserves-typing ⊢G ⊢H)
  so-subst-preserves-typing {k = k} (×-I ⊢F ⊢G) ⊢H = ×-I (so-subst-preserves-typing ⊢F ⊢H) (so-subst-preserves-typing ⊢G ⊢H)
  so-subst-preserves-typing {k = k} {φ = φ} {αs = αs} {H = H} (AppT-I Γ∋ψ Gs ⊢Gs) ⊢H = AppT-I Γ∋ψ (so-substVec Gs φ αs H) (so-substVec-preserves H Gs ⊢H ⊢Gs)

  so-subst-preserves-typing {k = k} {φ = φ ^F k} {αs = αs} {H = H} (AppF-I {φ = ψ ^F j} Φ,φ∋ψ Gs ⊢Gs) ⊢H with ψ ≟ φ | eqNat (k) j
  ... | yes refl | yes refl  = fo-substVec-preserves-typing αs (so-substVec Gs (φ ^F k) αs H) ⊢H (so-substVec-preserves H Gs ⊢H ⊢Gs)
  ... | yes refl | no sk≢j   = AppF-I (diffArityFun sk≢j Φ,φ∋ψ) (so-substVec Gs (φ ^F k) αs H) (so-substVec-preserves H Gs ⊢H ⊢Gs) 
  ... | no ψ≢φ   | yes refl  = AppF-I (diffIdFun (≢-sym ψ≢φ) Φ,φ∋ψ) (so-substVec Gs (φ ^F (k)) αs H) (so-substVec-preserves H Gs ⊢H ⊢Gs)
  ... | no ψ≢φ   | no sk≢j   = AppF-I (diffArityFun sk≢j Φ,φ∋ψ) (so-substVec Gs (φ ^F k) αs H) (so-substVec-preserves H Gs ⊢H ⊢Gs)


  so-subst-preserves-typing {k = k} {φ = φ} {αs = αs} {H = H} (μ-I ⊢G Ks ⊢Ks) ⊢H = μ-I ⊢G (so-substVec Ks φ αs H) (so-substVec-preserves H Ks ⊢H ⊢Ks)

mutual
  demoteVec : ∀ {k n : ℕ} → Vec TypeExpr n → FVar k → TCVar k → Vec TypeExpr n
  -- demoteVec (Gs) φ ψ = Vec.map (λ G → G [ φ :== ψ ]) Gs
  demoteVec [] φ ψ = []
  demoteVec (G ∷ Gs) φ ψ = (G [ φ :== ψ ]) ∷ demoteVec Gs φ ψ

  -- demotion of functorial variables to non-functorial variables 
  _[_:==_] : ∀ {k : ℕ} → TypeExpr → FVar k → TCVar k → TypeExpr
  𝟘 [ φ :== ψ ] = 𝟘
  𝟙 [ φ :== ψ ] = 𝟙
  Nat^ βs [ F , G ] [ φ :== ψ ] = Nat^ βs [ F , G ]
  (F + G) [ φ :== ψ ] = (F [ φ :== ψ ]) + (G [ φ :== ψ ])
  (F × G) [ φ :== ψ ] = (F [ φ :== ψ ]) × (G [ φ :== ψ ])
  AppT p [ Gs ] [ φ :== ψ ] = AppT p [ demoteVec Gs φ ψ ]
  AppF p ^F j [ Gs ] [ φ ^F k :== ψ ^T k ] with eqNat j k | p ≟ φ
  ... | .true because ofʸ refl | .true because ofʸ refl = AppT ψ ^T k [ demoteVec Gs (φ ^F k) (ψ ^T k) ]
  ... | _                      | .false because ofⁿ p≢φ = AppF p ^F j [ demoteVec Gs (φ ^F k) (ψ ^T k) ]
  ... | .false because ofⁿ j≢k | _ = AppF (p ^F j) [ demoteVec Gs (φ ^F k) (ψ ^T k) ]

  (μ p [λ βs , G ] Ks) [ φ :== ψ ] = μ p [λ βs , G ] demoteVec Ks φ ψ


  demoteVec-preserves-typing : ∀ {k n : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : FVar k} {ψ : TCVar k}
                               → (Gs : Vec TypeExpr n)
                               → foreach (λ G → Γ ≀ Φ ,, φ ⊢ G) Gs
                               → foreach (λ G → Γ ,, ψ ≀ Φ ⊢ G) (demoteVec Gs φ ψ)
  demoteVec-preserves-typing [] _ = bigtt
  demoteVec-preserves-typing (G ∷ Gs) (⊢G , ⊢Gs) = demotion-preserves-typing G ⊢G , demoteVec-preserves-typing Gs ⊢Gs

  demotion-preserves-typing : ∀ {k : ℕ} {Γ : TCCtx} {Φ : FunCtx} {φ : FVar k} {ψ : TCVar k}
                           → (F : TypeExpr)
                           → Γ ≀ (Φ ,, φ) ⊢ F
                           → (Γ ,, ψ ) ≀ Φ ⊢ F [ φ :== ψ ]
  demotion-preserves-typing 𝟘 𝟘-I = 𝟘-I
  demotion-preserves-typing 𝟙 𝟙-I = 𝟙-I
  demotion-preserves-typing {φ = φ} {ψ = ψ} (AppT p [ Fs ]) (AppT-I Γ∋p  Fs ⊢Fs) = AppT-I (∋-resp-weakTC ψ p Γ∋p) (demoteVec Fs φ ψ) (demoteVec-preserves-typing Fs ⊢Fs)

  demotion-preserves-typing {k = k} {φ = φ ^F k} {ψ = ψ ^T k} (AppF p ^F j [ Fs ]) (AppF-I Φφ∋p Fs ⊢Fs) with eqNat j k | p ≟ φ
  ... | .true because ofʸ refl | .true because ofʸ refl = AppT-I lookupZ (demoteVec Fs (φ ^F k) (ψ ^T k)) (demoteVec-preserves-typing Fs ⊢Fs)
  ... | .true because ofʸ refl | .false because ofⁿ p≢φ = AppF-I (diffIdFun (≢-sym p≢φ) Φφ∋p) (demoteVec Fs (φ ^F k) (ψ ^T k)) (demoteVec-preserves-typing Fs ⊢Fs)
  ... | .false because ofⁿ j≢k | .true because ofʸ refl = AppF-I (diffArityFun (≢-sym j≢k) Φφ∋p)  (demoteVec Fs (φ ^F k) (ψ ^T k)) (demoteVec-preserves-typing Fs ⊢Fs)
  ... | .false because ofⁿ j≢k | .false because ofⁿ p≢φ = AppF-I (diffArityFun (≢-sym j≢k) Φφ∋p)  (demoteVec Fs (φ ^F k) (ψ ^T k)) (demoteVec-preserves-typing Fs ⊢Fs)

  demotion-preserves-typing (F + G) (+-I ⊢F ⊢G) = +-I (demotion-preserves-typing F ⊢F) (demotion-preserves-typing G ⊢G)
  demotion-preserves-typing (F × G) (×-I ⊢F ⊢G) = ×-I (demotion-preserves-typing F ⊢F) (demotion-preserves-typing G ⊢G)
  -- should there be a Nat case for this ? 
  demotion-preserves-typing {ψ = ψ} (Nat^ βs [ F , G ]) (Nat-I ⊢F ⊢G) = weakenTCCtx ψ (Nat-I ⊢F ⊢G)
  demotion-preserves-typing {φ = φ} {ψ = ψ} (μ p [λ βs , F ] Gs) (μ-I ⊢F Gs ⊢Gs) = μ-I (weakenTCCtx ψ ⊢F) (demoteVec Gs φ ψ) (demoteVec-preserves-typing Gs ⊢Gs)

  
-------------------------------------------------------
-- examples
-------------------------------------------------------


-- vector of βs is well typed in context that includes all the βs 
VarTypeVec : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} → (βs : Vec (FVar 0) k) 
             → foreach (λ β → Γ ≀ Φ ,++ βs ⊢ β) (VarExprVec βs)
VarTypeVec [] = bigtt
VarTypeVec (β ∷ βs) = (AppF-I lookupZ [] bigtt) , foreach-preserves-weakening-FV (VarExprVec βs) (VarTypeVec βs)


-------------------------------
-- -- -- PTree example -- -- -- 
-------------------------------


φ : FVar 1
φ = 1 ^F 1

β : FVar 0
β = 2 ^F 0

α : FVar 0
α = 3 ^F 0

PTree-body : TypeExpr 
PTree-body = VarExpr β + AppF φ [ [ VarExpr β × VarExpr β ] ]

PTree-args : Vec TypeExpr 1
PTree-args = [ VarExpr α ]

PTree-α : TypeExpr
PTree-α = μ φ [λ [ β ] , AppF β [ [] ] + AppF φ  [ [ AppF β [ [] ] × AppF β [ [] ] ] ] ] [ AppF α [ [] ] ] 

⊢PTree-α : ∅tc ≀ ∅fv ,, α ⊢ PTree-α
⊢PTree-α = μ-I ⊢body PTree-args (⊢args , bigtt) 
  where
        0≢1 : 0 ≢ 1
        0≢1 = λ () 

        β,φ∋β : (∅fv ,, β ,, φ) ∋ β
        β,φ∋β = lookupDiffArity 0≢1 lookupZ 

        ⊢β : ∅tc ≀ ∅ ,, β ,, φ ⊢ VarExpr β
        ⊢β = AppF-I β,φ∋β [] bigtt 

        β×β : TypeExpr
        β×β = VarExpr β × VarExpr β

        ⊢β×β : ∅tc ≀ ∅ ,, β ,, φ ⊢ β×β
        ⊢β×β = ×-I ⊢β ⊢β 

        ⊢φβ×β : ∅tc ≀ ∅ ,, β ,, φ ⊢ AppF φ [ [ β×β ] ]
        ⊢φβ×β = AppF-I lookupZ [ β×β ] (⊢β×β , bigtt) 

        ⊢body : ∅tc ≀ ∅ ,, β ,, φ ⊢ PTree-body
        ⊢body = +-I ⊢β ⊢φβ×β  

        ⊢args : ∅tc ≀ ∅fv ,, α ⊢ VarExpr α
        ⊢args = AppF-I lookupZ [] bigtt 



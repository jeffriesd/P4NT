open import Syntax.NestedTypeSyntax
open import Data.Product renaming (_×_ to _×'_  ; map to ×'-map) 
open import Data.Sum renaming ([_,_] to [_,⊎_]) hiding (map) 
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Nullary using (_because_ ; Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (isYes)

import Relation.Binary.PropositionalEquality as ≡ 
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Vec using (Vec ; [_] ; [] ; _∷_ ; _++_) 

open import Agda.Builtin.Bool
open ≡.≡-Reasoning

open import Utils using (exFalso ; foreach) 
module Syntax.TermSyntax where 


isYes' : ∀ {a} {P : Set a} → Dec P → Bool
isYes' (yes _) = true
isYes' (no  _) = false


TermId : Set
TermId = ℕ 

module term-contexts where 

  mutual
    -- A term context is parameterized by type contexts Γ and Φ
    -- and is either empty, or a term context Δ extended
    -- with a variable x of type F that is not
    -- already appearing in Δ 
    data TermCtx (Γ : TCCtx) (Φ : FunCtx) : Set where 
      Δ∅       : TermCtx Γ Φ 
      _,-_∶_⟨_⟩  : ∀ (Δ : TermCtx Γ Φ) 
                 → (x : TermId) 
                 → {F : TypeExpr} → (⊢F :  Γ ≀ Φ ⊢ F)
                 -- need proof that x is not already appearing in Δ
                 → (isYes (Δ-lookup x Δ) ≡ false)
                 → TermCtx Γ Φ 
   
    -- lookup relation for term variables 
    data _∶∋_ : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx Γ Φ → TermId → Set where
      z∋ : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx Γ Φ} {x : TermId} 
          → {p : isYes (Δ-lookup x Δ) ≡ false}
          → {F : TypeExpr} → {⊢F :  Γ ≀ Φ ⊢ F}
          → (Δ ,- x ∶ ⊢F ⟨ p ⟩) ∶∋ x
  
      s∋ : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx Γ Φ} {x y : TermId} 
          → {p : isYes (Δ-lookup x Δ) ≡ false}
          → {F : TypeExpr} → {⊢F :  Γ ≀ Φ ⊢ F}
          →  Δ ∶∋ y
          → (Δ ,- x ∶ ⊢F ⟨ p ⟩) ∶∋ y
  
    -- lookup relation is decidable 
    Δ-lookup : ∀ {Γ : TCCtx} {Φ : FunCtx} → (x : TermId) (Δ : TermCtx Γ Φ)
              → Dec (Δ ∶∋ x)
    Δ-lookup x Δ∅ = no (λ ())
    Δ-lookup x (Δ ,- y ∶ _ ⟨ p ⟩) with x ≟ y | Δ-lookup x Δ
    ... | yes ≡.refl | _  = yes z∋ 
    ... | no x≢y | yes Δ∋x = yes (s∋ Δ∋x) 
    ... | no x≢y | no ¬Δ∋x = no Δ-lookup-helper 
      where Δ-lookup-helper : ¬ ((Δ ,- y ∶ _ ⟨ p ⟩) ∶∋ x)
            Δ-lookup-helper z∋  = x≢y ≡.refl
            Δ-lookup-helper (s∋  Δ∋x) = ¬Δ∋x Δ∋x 

open term-contexts public 


-------------------------------------------------------

-- grammar of term expressions 
data TermExpr : Set where
  tmvar : TermId → TermExpr
  ⊥e  : TermExpr → TermExpr
  ⊤i   : TermExpr
  inl : TermExpr → TermExpr
  inr : TermExpr → TermExpr
  case_of[_↦_≀_↦_] : (t : TermExpr) → (x : TermId)
                     → (l : TermExpr) → (y : TermId) → (r : TermExpr) → TermExpr
  _,,_ : TermExpr → TermExpr → TermExpr
  π₁ : TermExpr → TermExpr
  π₂ : TermExpr → TermExpr
  L[_]_,_  : {k : ℕ} → (αs : Vec (FVar 0) k) → (x : TermId) → (t : TermExpr) → TermExpr
  app_[_]_ : {k : ℕ} → (t : TermExpr) → (Ks : Vec TypeExpr k) → (s : TermExpr) → TermExpr
  map   : (F : TypeExpr) → (G : TypeExpr) → (H : TypeExpr) → TermExpr
  inn   : (H : TypeExpr) → TermExpr
  fold  : (F : TypeExpr) → (H : TypeExpr) → TermExpr


mutual 

  weakenFunCtx-Δ  : ∀ {k : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φ : FVar k) 
                  → TermCtx Γ Φ
                  → TermCtx Γ (Φ ,, φ)
  weakenFunCtx-Δ φ Δ∅ = Δ∅
  weakenFunCtx-Δ φ (Δ ,- x ∶ ⊢F ⟨ p ⟩) =  (weakenFunCtx-Δ φ Δ ,- x ∶ weakenFunCtximpl φ ⊢F ⟨ weaken-p ⟩)
    -- need proof that weakening types in a term context doesn't 
    -- affect the lookup of variables 
    where weaken-p : isYes (Δ-lookup x (weakenFunCtx-Δ φ Δ)) ≡ false
          weaken-p = begin isYes (Δ-lookup x (weakenFunCtx-Δ φ Δ))
                      ≡⟨ ≡.sym (Δ-lookup-weakenFunCtx φ Δ x) ⟩
                        isYes (Δ-lookup x Δ)
                      ≡⟨ p ⟩
                        false
                      ∎

  -- ∶∋ respects weakening 
  Δ-lookup-to : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (φ : FVar k) 
            → (Δ : TermCtx Γ Φ)
            → (x : TermId)
            → (Δ ∶∋  x)
            → ((weakenFunCtx-Δ φ Δ) ∶∋  x)
  Δ-lookup-to φ Δ∅ x ()
  Δ-lookup-to φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) .y z∋ = z∋
  Δ-lookup-to φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) x (s∋  Δ∋x) = s∋ (Δ-lookup-to φ Δ x Δ∋x) 


  -- :∋ respects weakening, other direction
  Δ-lookup-from : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (φ : FVar k) 
            → (Δ : TermCtx Γ Φ)
            → (x : TermId)
            → ((weakenFunCtx-Δ φ Δ) ∶∋  x)
            → (Δ ∶∋  x)
  Δ-lookup-from φ Δ∅ x ()
  Δ-lookup-from φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) .y z∋ = z∋
  Δ-lookup-from φ (Δ ,- y ∶ ⊢F ⟨ p ⟩) x (s∋ Δ∋x) = s∋ (Δ-lookup-from φ Δ x Δ∋x) 

  -- weakening types in a term context doesn't affect lookup of term variables
  Δ-lookup-weakenFunCtx : ∀ {k} {Γ : TCCtx} {Φ : FunCtx} (φ : FVar k) 
            → (Δ : TermCtx Γ Φ)
            → (x : TermId)
            → isYes (Δ-lookup x Δ) 
            ≡ isYes (Δ-lookup x (weakenFunCtx-Δ φ Δ))
            -- → (p : isYes (Δ-lookup x Δ) ≡ false)
  Δ-lookup-weakenFunCtx φ Δ∅ x = ≡.refl
  Δ-lookup-weakenFunCtx φ (Δ ,- y ∶ _ ⟨ p ⟩) x with x ≟ y | Δ-lookup x Δ | Δ-lookup x (weakenFunCtx-Δ φ Δ)
  ... | yes ≡.refl | _   | r = ≡.refl
  ... | no x≢y | yes Δ∋x | yes wΔ∋x = ≡.refl
  ... | no x≢y | yes Δ∋x | no ¬wΔ∋x = exFalso (¬wΔ∋x (Δ-lookup-to φ Δ x Δ∋x))
  ... | no x≢y | no ¬Δ∋x | yes wΔ∋x = exFalso (¬Δ∋x (Δ-lookup-from φ Δ x wΔ∋x))
  ... | no x≢y | no ¬Δ∋x | no ¬wΔ∋x = ≡.refl


  weakenFunCtx-Δ-Vec : ∀ {k n : ℕ} { Γ : TCCtx } {Φ : FunCtx} (φs : Vec (FVar k) n)
                  → TermCtx Γ Φ
                  → TermCtx Γ (Φ ,++ φs)
  weakenFunCtx-Δ-Vec [] Δ = Δ
  weakenFunCtx-Δ-Vec (φ ∷ φs) Δ = weakenFunCtx-Δ φ (weakenFunCtx-Δ-Vec φs Δ)

  weakenFunCtx-Δ-∅  : ∀ { Γ : TCCtx } → (Φ : FunCtx)
                  → TermCtx Γ ∅ 
                  → TermCtx Γ Φ 
  weakenFunCtx-Δ-∅ ∅ Δ = Δ
  weakenFunCtx-Δ-∅ (Φ ,, φ) Δ = weakenFunCtx-Δ φ (weakenFunCtx-Δ-∅ Φ Δ)



-- form type H [ μH ]
in-I-helper' : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
               → {H : TypeExpr} 
               → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
               → Γ ≀ (∅ ,++ αs) ⊢ H [ φ :=[ βs ] (μ φ [λ αs , H ] VarExprVec βs) ]
in-I-helper' {φ = φ} {αs} {βs} {H} ⊢H = so-subst-preserves-typing ⊢H (μ-I ⊢H (VarExprVec βs) (VarTypeVec βs))


-- substitute αs for βs in H [ μH ] 
in-I-helper : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
              → {H : TypeExpr} 
              → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
              → Γ ≀ (∅ ,++ βs) ⊢ ((H [ φ :=[ βs ] (μ φ [λ αs , H ] VarExprVec βs) ]) [ αs := VarExprVec βs ]Vec)
in-I-helper {φ = φ} {αs} {βs} {H} ⊢H = [:=]Vec-preserves-typing αs 
                                            (VarExprVec βs) (weakenFunCtx-∅-,++ αs (in-I-helper' ⊢H)) (VarTypeVec βs)

-- form type H [ μH ]
fold-I-helper' : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
                 → {H : TypeExpr} → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
                 → {F : TypeExpr} → (⊢F : Γ ≀ (∅ ,++ βs)  ⊢ F)
                 → Γ ≀ (∅ ,++ αs) ⊢ H [ φ :=[ βs ] F ]
fold-I-helper' {φ = φ} {αs} {βs} {H} ⊢H {F} ⊢F = so-subst-preserves-typing ⊢H (weakenFunCtx-∅-,++ βs ⊢F)


fold-I-helper : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
                → {H : TypeExpr} → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
                → {F : TypeExpr} → (⊢F : Γ ≀ (∅ ,++ βs)  ⊢ F)
                → Γ ≀ (∅ ,++ βs) ⊢ (H [ φ :=[ βs ] F ]) [ αs := VarExprVec βs ]Vec 
fold-I-helper {φ = φ} {αs} {βs} {H} ⊢H {F} ⊢F = [:=]Vec-preserves-typing αs (VarExprVec βs) (weakenFunCtx-∅-,++ αs (fold-I-helper' ⊢H ⊢F)) (VarTypeVec βs)



-- well formed terms, formed with respect to contexts Γ, Φ, Δ 
-- and with respect to TermExpr and a well formed type Γ ≀ Φ ⊢ F 
data _≀_∣_⊢_∶_ : ∀ (Γ : TCCtx) (Φ : FunCtx) 
                → TermCtx Γ Φ 
                → TermExpr 
                → {F : TypeExpr}
                → Γ ≀ Φ ⊢ F
                → Set where 

  var-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx Γ Φ)
          → (x : TermId)
          → {F : TypeExpr}
          → (⊢F : Γ ≀ Φ ⊢ F)
          → (p : isYes (Δ-lookup x Δ) ≡ false)
          → Γ ≀ Φ ∣ Δ ,- x ∶ ⊢F ⟨ p ⟩ ⊢ tmvar x ∶ ⊢F

  ⊥e-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx Γ Φ)
          → {F : TypeExpr}
          → (⊢F : Γ ≀ Φ ⊢ F)
          → (t : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ t ∶ 𝟘-I
          → Γ ≀ Φ ∣ Δ ⊢ ⊥e t ∶ ⊢F


  ⊤-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
        → (Δ : TermCtx Γ Φ)
        → Γ ≀ Φ ∣ Δ ⊢ ⊤i ∶ 𝟙-I


  inl-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx Γ Φ)
          → {F G : TypeExpr} 
          → (⊢F : Γ ≀ Φ ⊢ F) (⊢G : Γ ≀ Φ ⊢ G)
          → (s : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ s ∶ ⊢F
          → Γ ≀ Φ ∣ Δ ⊢ inl s ∶ +-I ⊢F ⊢G 

  inr-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx Γ Φ)
          → {F G : TypeExpr} 
          → (⊢F : Γ ≀ Φ ⊢ F) (⊢G : Γ ≀ Φ ⊢ G)
          → (s : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ s ∶ ⊢G
          → Γ ≀ Φ ∣ Δ ⊢ inr s ∶ +-I ⊢F ⊢G 

  case-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
          → (Δ : TermCtx Γ Φ)
          → {F G K : TypeExpr} 
          → (⊢F : Γ ≀ Φ ⊢ F) → (⊢G : Γ ≀ Φ ⊢ G) → (⊢K : Γ ≀ Φ ⊢ K)
          → (t : TermExpr) 
          → Γ ≀ Φ ∣ Δ ⊢ t ∶ +-I ⊢F ⊢G 
          → (x : TermId)
          → (px : isYes (Δ-lookup x Δ) ≡ false)
          → (l : TermExpr)
          → Γ ≀ Φ ∣ Δ ,- x ∶ ⊢F ⟨ px ⟩ ⊢ l ∶ ⊢K
          → (y : TermId)
          → (py : isYes (Δ-lookup y Δ) ≡ false)
          → (r : TermExpr)
          → Γ ≀ Φ ∣ Δ ,- y ∶ ⊢G ⟨ py ⟩ ⊢ r ∶ ⊢K
          → Γ ≀ Φ ∣ Δ ⊢ case t of[ x ↦ l ≀ y ↦ r ] ∶ ⊢K

  pair-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
           → (Δ : TermCtx Γ Φ)
           → {F G : TypeExpr} 
           → (⊢F : Γ ≀ Φ ⊢ F) (⊢G : Γ ≀ Φ ⊢ G)
           → (s : TermExpr) 
           → Γ ≀ Φ ∣ Δ ⊢ s ∶ ⊢F 
           → (t : TermExpr) 
           → Γ ≀ Φ ∣ Δ ⊢ t ∶ ⊢G
           → Γ ≀ Φ ∣ Δ ⊢ (s ,, t) ∶ ×-I ⊢F ⊢G

  π₁-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
         → (Δ : TermCtx Γ Φ)
         → {F G : TypeExpr} 
         → (⊢F : Γ ≀ Φ ⊢ F) (⊢G : Γ ≀ Φ ⊢ G)
         → (t : TermExpr) 
         → Γ ≀ Φ ∣ Δ ⊢ t ∶ ×-I ⊢F ⊢G 
         → Γ ≀ Φ ∣ Δ ⊢ π₁ t ∶ ⊢F

  π₂-I : ∀ {Γ : TCCtx} {Φ : FunCtx} 
         → (Δ : TermCtx Γ Φ)
         → {F G : TypeExpr}
         → (⊢F : Γ ≀ Φ ⊢ F) (⊢G : Γ ≀ Φ ⊢ G)
         → (t : TermExpr) 
         → Γ ≀ Φ ∣ Δ ⊢ t ∶ ×-I ⊢F ⊢G 
         → Γ ≀ Φ ∣ Δ ⊢ π₂ t ∶ ⊢G

  L-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ} {αs : Vec (FVar 0) k}
        → {F G : TypeExpr}
        → (⊢F : Γ ≀ ( ∅ ,++ αs ) ⊢ F) (⊢G : Γ ≀ ( ∅ ,++ αs ) ⊢ G)
        → (Δ : TermCtx Γ ∅ )
        → (x : TermId)
        → (p : isYes (Δ-lookup x (weakenFunCtx-Δ-Vec αs Δ)) ≡ false)
        → (t : TermExpr)
        → Γ ≀ ( ∅ ,++ αs ) ∣ (weakenFunCtx-Δ-Vec αs Δ) ,- x ∶ ⊢F ⟨ p ⟩ ⊢ t ∶ ⊢G
        → Γ ≀ ∅ ∣ Δ ⊢ L[ αs ] x , t ∶ Nat-I ⊢F ⊢G

  app-I : ∀ {Γ : TCCtx} {Φ : FunCtx} {k : ℕ} {αs : Vec (FVar 0) k}
          → {F G : TypeExpr} {Ks : Vec TypeExpr k}
          → (⊢F : Γ ≀ ( ∅ ,++ αs ) ⊢ F) (⊢G : Γ ≀ ( ∅ ,++ αs ) ⊢ G)
          → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
          → (Δ : TermCtx Γ ∅ )
          → (t : TermExpr)
          → Γ ≀ ∅ ∣ Δ ⊢ t ∶ Nat-I ⊢F ⊢G 
          -- need to weaken Δ by Φ for s and conclusion 
          → (s : TermExpr)
          -- need F [ αs := Ks ] to be typed in Γ ≀ Φ .
          -- it should be typed in ∅ after the substitution. 
          -- 
          -- so for it to be typed in Φ after the substitution, 
          -- we need it to be typed in Φ ,++ αs before substituting (by weakenfunCtx-∅-,++)
          → Γ ≀ Φ ∣ (weakenFunCtx-Δ-∅ Φ Δ) ⊢ s ∶ ([:=]Vec-preserves-typing αs Ks (weakenFunCtx-∅-,++ αs ⊢F)  ⊢Ks)
          → Γ ≀ Φ ∣ (weakenFunCtx-Δ-∅ Φ Δ) ⊢ app t [ Ks ] s  ∶ ([:=]Vec-preserves-typing αs Ks (weakenFunCtx-∅-,++ αs ⊢G) ⊢Ks)


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
          → {H F G  : TypeExpr}
          → (⊢H : Γ ≀ (∅ ,++ γs) ,, φ ⊢ H)
          -- use ,++ (γs ++ βs) so ⊢F and ⊢G have the right form for Nat-I ⊢F ⊢G 
          → (⊢F : Γ ≀ (∅ ,++ (γs ++ βs)) ⊢ F)
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
          
          -- -- so-subst-preserves-typing H F ⊢H ⊢F : Γ ≀ (∅ ,++ γs) ⊢ H [ φ :=[ βs ] F ]
          -- -- so-subst-preserves-typing H F ⊢H ⊢F : Γ ≀ (∅ ,++ γs) ⊢ H [ φ :=[ βs ] F ]

          -- → Γ ≀ ∅ ∣ Δ∅ ⊢ mapp ∶ Nat-I (Nat-I ⊢F ⊢G) (Nat-I (so-subst-preserves-typing H F ⊢H (FunCtx-resp-++ {Γ} γs βs ⊢F)) ((so-subst-preserves-typing H G ⊢H (FunCtx-resp-++ {Γ} γs βs ⊢G))))
          → Γ ≀ ∅ ∣ Δ∅ ⊢ map F G H ∶ Nat-I {αs = []} (Nat-I ⊢F ⊢G) (Nat-I (so-subst-preserves-typing {αs = βs} ⊢H (FunCtx-resp-++ γs βs ⊢F)) 
                                                                     (so-subst-preserves-typing {αs = βs} ⊢H (FunCtx-resp-++ γs βs ⊢G)))


  in-I : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
         → {H : TypeExpr} 
         → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
         -- 
         → Γ ≀ ∅ ∣ Δ∅ ⊢ inn H ∶ Nat-I {αs = βs} (in-I-helper ⊢H) (μ-I ⊢H (VarExprVec βs) (VarTypeVec βs))

  fold-I : ∀ {Γ : TCCtx} {k : ℕ} {φ : FVar k} {αs βs : Vec (FVar 0) k} 
         → {H F : TypeExpr} 
         → (⊢H : Γ ≀ ((∅ ,++ αs) ,, φ) ⊢ H)
         → (⊢F : Γ ≀ (∅ ,++ βs)  ⊢ F)
         → Γ ≀ ∅ ∣ Δ∅ ⊢ fold F H ∶ Nat-I {αs = []} (Nat-I {αs = βs} (fold-I-helper ⊢H ⊢F) ⊢F) (Nat-I {αs = βs} (μ-I ⊢H (VarExprVec βs) (VarTypeVec βs)) ⊢F)

 
{- map for multiple φs requires us to formalize so-susbt for vectors of φs 
  mapvec-I : ∀ {Γ : TCCtx} {g : ℕ} {k : ℕ} {n : ℕ} -- n is number of phis  -- k is arity of each phi 
          → {φs : Vec (FVar k) n}
          → {βs : Vec (FVar 0) k} 
          → {γs : Vec (FVar 0) g} 
          --
          → {H : TypeExpr}
          → (⊢H : Γ ≀ (∅ ,++ γs) ,++ φs ⊢ H)
          -- 
          → {Fs : Vec TypeExpr n}
          → (⊢Fs : foreach (Γ ≀ (∅ ,++ (γs ++ βs)) ⊢_ ) Fs)
          -- 
          → {Gs : Vec TypeExpr n}
          → (⊢G : foreach (Γ ≀ (∅ ,++ (γs ++ βs)) ⊢_) Gs)
          --
          → Γ ≀ ∅ ∣ Δ∅ ⊢ map Fs Gs H ∶ Nat-I {αs = []} {!!} (Nat-I {αs = γs} {!so-subst-preserves-typing {αs = βs} ⊢F ? !} {!!} )   
          


  -- g is the number of gammas 
  -- p is the number of φs 
  -- 
  -- 
  -- do map for single φ for now 
  -- 
  -- k is the arity of φ , number of βs 
  map-I' : ∀ {Γ : TCCtx} {g : ℕ} {k : ℕ} 
          → {φ : FVar k}
          → {βs : Vec (FVar 0) k} 
          → {γs : Vec (FVar 0) g} 
          --
          → {H : TypeExpr}
          → (⊢H : Γ ≀ (∅ ,++ γs) ,, φ ⊢ H)
          -- 
          → {F : TypeExpr}
          → (⊢F : Γ ≀ ((∅ ,++ γs) ,++ βs) ⊢ F)
          -- 
          → {G : TypeExpr}
          → (⊢G : Γ ≀ ((∅ ,++ γs) ,++ βs) ⊢ G)
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
          -- -- so-subst-preserves-typing H F ⊢H ⊢F : Γ ≀ (∅ ,++ γs) ⊢ H [ φ :=[ βs ] F ]
          -- -- so-subst-preserves-typing H F ⊢H ⊢F : Γ ≀ (∅ ,++ γs) ⊢ H [ φ :=[ βs ] F ]
          -- → Γ ≀ ∅ ∣ Δ∅ ⊢ mapp ∶ Nat-I (Nat-I ⊢F ⊢G) (Nat-I (so-subst-preserves-typing H F ⊢H (FunCtx-resp-++ {Γ} γs βs ⊢F)) ((so-subst-preserves-typing H G ⊢H (FunCtx-resp-++ {Γ} γs βs ⊢G))))
          → Γ ≀ ∅ ∣ Δ∅ ⊢ map [ F ] [ G ] H ∶ Nat-I {αs = []} (Nat-I ⊢F ⊢G) (Nat-I (so-subst-preserves-typing {αs = βs} ⊢H (FunCtx-resp-++ γs βs ⊢F)) 
                                                                     (so-subst-preserves-typing {αs = βs} ⊢H (FunCtx-resp-++ γs βs ⊢G)))

-}



module example-contexts where

  x : TermId
  x = 0 

  y : TermId
  y = 1
  
  ctx-x : TermCtx ∅ ∅
  ctx-x = Δ∅ ,- x ∶ 𝟙-I ⟨ ≡.refl ⟩  

  -- ctx-x-y : TermCtx ∅ ∅
  -- ctx-x-y = ctx-x ,- y ∶ 𝟙-I ⟨ {!!} ⟩ -- Goal: isYes (Δ-lookup y ctx-x) ≡ false

  -- ctx-x-y' : TermCtx ∅ ∅
  -- ctx-x-y' = ctx-x ,- y ∶ 𝟙-I ⟨ {!!} ⟩ -- false ≡ false 

  ctx-x-y'' : TermCtx ∅ ∅
  ctx-x-y'' = ctx-x ,- y ∶ 𝟙-I ⟨ ≡.refl ⟩ 

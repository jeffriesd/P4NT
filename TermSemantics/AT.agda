
open import Syntax.NestedTypeSyntax
open import Syntax.TermSyntax
open import TypeSemantics.TypeSemantics 
open import RelEnvironments.Core 
open import SetEnvironments.Core 
open import RelSem.RelCats
open import Categories.Functor using (Functor)
open import SetCats 
open RelObj

open import Data.Unit
-- open import TermSemantics.TermSetSemantics using (ContextInterp) 
open import Categories.NaturalTransformation 

open import Utils 
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product 
import Relation.Binary.PropositionalEquality as ≡ 

module TermSemantics.AT where 


ContextInterp : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx Γ Φ 
                → Functor SetEnvCat Sets 
ContextInterp Δ∅ = ConstF ⊤
ContextInterp (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) = ContextInterp Δ ×Set SetSem ⊢F

ContextInterpRel : ∀ {Γ : TCCtx} {Φ : FunCtx} → TermCtx Γ Φ 
                → Functor RelEnvCat Rels 
ContextInterpRel Δ∅ = ConstF Rel⊤
ContextInterpRel (Δ ,- _ ∶ ⊢F ⟨ _ ⟩) = ContextInterpRel Δ ×Rels RelSem ⊢F



TermSetSem : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx Γ Φ}
            → {F : TypeExpr} → {⊢F : Γ ≀ Φ ⊢ F}
            → {t : TermExpr}
            →  (⊢t : Γ ≀ Φ ∣ Δ ⊢ t ∶ ⊢F)
            → NaturalTransformation (ContextInterp Δ) (SetSem ⊢F)
TermSetSem = {!!} 

_,_∈[_][_]_ : ∀ {A B C D : Set} → C → D → (A ≡ C) → (B ≡ D) → REL A B → Set
x , y ∈[ ≡.refl ][ ≡.refl ] R = x , y ∈ R



ContextInterp-over-1 : ∀ {Γ : TCCtx} {Φ : FunCtx} (Δ : TermCtx Γ Φ)
                       → (ρ : RelEnv)
                       → fst (Functor.F₀ (ContextInterpRel Δ) ρ)
                       ≡ Functor.F₀ (ContextInterp Δ) (Functor.F₀ π₁Env ρ)
ContextInterp-over-1 Δ∅ ρ = ≡.refl
ContextInterp-over-1 (Δ ,- x ∶ ⊢F ⟨ s ⟩) ρ = {!×'-cong (ContextInterp-over-1 Δ ρ) ?  !} 

ContextInterp-over-2 : ∀ {Γ : TCCtx} {Φ : FunCtx} (Δ : TermCtx Γ Φ)
                       → (ρ : RelEnv)
                       → snd (Functor.F₀ (ContextInterpRel Δ) ρ)
                       ≡ Functor.F₀ (ContextInterp Δ) (Functor.F₀ π₂Env ρ)
ContextInterp-over-2 = {!!} 




AbstractionThm' : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx Γ Φ}
                 → {F : TypeExpr} → {⊢F : Γ ≀ Φ ⊢ F}
                 → {t : TermExpr}
                 → (⊢t : Γ ≀ Φ ∣ Δ ⊢ t ∶ ⊢F)
                 → (ρ : RelEnv)
                 → ∀ {a : Functor.F₀ (ContextInterp Δ) (Functor.F₀ π₁Env ρ)}
                     {b : Functor.F₀ (ContextInterp Δ) (Functor.F₀ π₂Env ρ)}
                 → a , b ∈ rel (Functor.F₀ (ContextInterpRel Δ) ρ)
                 →   NaturalTransformation.η (TermSetSem ⊢t) (Functor.F₀ π₁Env ρ) a 
                   , NaturalTransformation.η (TermSetSem ⊢t) (Functor.F₀ π₂Env ρ) b 
                     ∈ rel (Functor.F₀ (RelSem ⊢F) ρ)
AbstractionThm' = {!!} 


AbstractionThm : ∀ {Γ : TCCtx} {Φ : FunCtx} {Δ : TermCtx Γ Φ}
                 → {F : TypeExpr} → {⊢F : Γ ≀ Φ ⊢ F}
                 → {t : TermExpr}
                 → (⊢t : Γ ≀ Φ ∣ Δ ⊢ t ∶ ⊢F)
                 → (ρ : RelEnv)
                 → ∀ {a : Functor.F₀ (ContextInterp Δ) (Functor.F₀ π₁Env ρ)}
                     {b : Functor.F₀ (ContextInterp Δ) (Functor.F₀ π₂Env ρ)}

                 → a , b ∈[ ContextInterp-over-1 Δ ρ ][ ContextInterp-over-2 Δ ρ ]
                         rel (Functor.F₀ (ContextInterpRel Δ) ρ)

                 →   NaturalTransformation.η (TermSetSem ⊢t) (Functor.F₀ π₁Env ρ) a 
                   , NaturalTransformation.η (TermSetSem ⊢t) (Functor.F₀ π₂Env ρ) b 
                     ∈[ ≡.sym (SetSem-over-1 ⊢F ρ) ][ ≡.sym (SetSem-over-2 ⊢F ρ) ] 
                     rel (Functor.F₀ (RelSem ⊢F) ρ)
AbstractionThm = {!!} 

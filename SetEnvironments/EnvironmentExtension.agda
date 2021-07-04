module SetEnvironments.EnvironmentExtension where 


{-
-- import core 
open import SetEnvironments.Core


open import Categories.Category using (Category)
-- open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)

open import Categories.Category.Product using (Product ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_ ; assocʳ)
open import Categories.Category.Construction.Functors using (Functors; module curry ; evalF)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality as ≡ 
open ≡.≡-Reasoning


open import SetCats 
open import Syntax.NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
open import Utils
-}

open import Level renaming (zero to lzero ; suc to lsuc)
open import SetCats using (Sets ; SetTerminal ; [Sets^_,Sets] ; SetFunctors-Terminal ; Sets→0Functors)

open import RTEnvironments.EnvironmentExtension {lsuc lzero} {lsuc lzero} {lsuc lzero} {lsuc lzero} {lzero} {lzero}
                                                {Sets} {[Sets^_,Sets]} {SetFunctors-Terminal} {Sets→0Functors}
  renaming (extendEnv-αs to extendSetEnv-αs
           ; extendEnv-ρ×As to  extendSetEnv-ρ×As 
           ; extendEnv-α to  extendSetEnv-α
           ; extendEnv2 to extendSetEnv2 
           -- ; extendTEnv2 to extendTSetEnv
           )
         public



module extendT where 

    open import Syntax.NestedTypeSyntax using (FVar) 
    open import Data.Vec using (Vec)
    open import Categories.Functor using (Functor)
    open import Categories.Category.Product using (Product)
    open import SetEnvironments.Core using (SetEnvCat)
    open import SetCats using ([Sets^_,Sets] ; Sets^)

    -- abstract 

    extendTSetEnv : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
                → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) SetEnvCat
    extendTSetEnv = extendTEnv2  

open extendT public  



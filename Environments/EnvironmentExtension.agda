

open import Categories.Category 
-- open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)

open import Categories.Category.Product using (Product ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_ ; assocʳ)
open import Categories.Category.Construction.Functors using (Functors; module curry ; evalF)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.Functor.Construction.Constant using (const)

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec ; _∷_; replicate ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
import Relation.Binary.PropositionalEquality as ≡ 
-- open ≡.≡-Reasoning
open import Categories.Object.Terminal


open import SetCats 
open import NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
open import Utils


module Environments.EnvironmentExtension {o l e : Level} (C : Category o l e) (C⊤ : Terminal C)  where 

private module C = Category C
open C.HomReasoning 
open Category C 
open VecCat C 

open import Categories.Morphism.Reasoning C as MR

open import Environments.Core C C⊤






-- used in extendmorph2-vec-nat 
id-comm-1 : ∀ {X Y Z : C.Obj} → (f : X ⇒ Y) → (g : Y ⇒ Z) → (h : X ⇒ Z) → g ∘ f ≈ h → (id ∘ g) ∘ (id ∘ f) ≈ id ∘ h 
id-comm-1 f g h gf≈h = begin (id ∘ g) ∘ id ∘ f
                                ≈⟨ C.∘-resp-≈ C.identityˡ C.identityˡ  ⟩
                                g ∘ f 
                                ≈⟨ gf≈h ⟩ 
                                h
                                ≈˘⟨ C.identityˡ ⟩
                                id ∘ h ∎  

-- eliminate two ids on left 
id-comm-id-idˡ : ∀ {X Y : C.Obj} → (f : X ⇒ Y) → (id ∘ id) ∘ f ≈ f
id-comm-id-idˡ f = begin (id ∘ id) ∘ f
                        ≈⟨ C.∘-resp-≈ C.identityˡ C.Equiv.refl ⟩
                        id ∘ f
                        ≈⟨ C.identityˡ ⟩
                        f ∎ 

-- eliminate two ids on right
id-comm-id-idʳ  : ∀ {X Y : C.Obj} → (f : X ⇒ Y) → f ∘ (id ∘ id) ≈ f
id-comm-id-idʳ f = begin f ∘ (id ∘ id) 
                        ≈⟨ C.∘-resp-≈ C.Equiv.refl C.identityˡ ⟩ 
                        f ∘ id 
                        ≈⟨ C.identityʳ ⟩
                        f ∎ 


-------------------------------------------------------
-- extend morphisms of environments 
-------------------------------------------------------

-- TODO maybe rename this to identity-rho or something? 
-- 
-- this gives rise to a functor extendGenEnv : [C^k ,C] → GenEnvCat
-- λ F → ρ [ φ :fv= F ]
extendmorph-η : ∀ {k} 
                {F G : Functor (C^ k) C} 
              → (ρ : GenEnv)
              → (φ : FVar k)
              → NaturalTransformation F G 
              → GenEnvMorph (ρ [ φ ∷ Vec.[] :fvs= F ∷ Vec.[] ])
                            (ρ [ φ ∷ Vec.[] :fvs= G ∷ Vec.[] ])
extendmorph-η {k} {F} {G} record { tc = tc ; fv = fv } (φ ^F k) η = record { eqTC = ≡.refl ; fv = λ ψ → mapfv ψ }
  where mapfv : ∀ {j} (ψ : FVar j) 
          → NaturalTransformation (GenEnv.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ) 
                                  (GenEnv.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= G ∷ Vec.[] ]) ψ)
        mapfv (ψ ^F j) with eqNat k j | φ ≟ ψ 
        ... | yes ≡.refl | yes ≡.refl = η 
        ... | no _ | _ = idnat -- (fv (ψ ^F j))
        ... | yes ≡.refl | no _ = idnat -- (fv (ψ ^F j)) 



-- this gives rise to a functor extendGenEnvF : GenEnvCat → GenEnvCat  
-- λ ρ → ρ [ φ :fv= F ]
extendmorph-idF : ∀  {k} (φ : FVar k) (F : Functor (C^ k) C)
              → (ρ ρ' : GenEnv)
              → GenEnvMorph ρ ρ'
              → GenEnvMorph (ρ  [ φ :fv= F ]) 
                            (ρ' [ φ :fv= F ]) 
extendmorph-idF {k} (φ ^F k) F ρ ρ' f = record { eqTC = GenEnvMorph.eqTC f ; fv = fvmap } 
          where fvmap : ∀ {j} (ψ : FVar j) 
                  → NaturalTransformation (GenEnv.fv (ρ  [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                                          (GenEnv.fv (ρ' [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                fvmap (ψ ^F j) with eqNat k j | φ ≟ ψ 
                ... | yes ≡.refl | yes ≡.refl = idnat -- mkIdNatTr' F
                ... | no _ | _ = GenEnvMorph.fv f (ψ ^F j)
                ... | yes ≡.refl | no _ = GenEnvMorph.fv f (ψ ^F j)



extendmorph2 : ∀ {k} (φ : FVar k)
                {F G : Functor (C^ k) C} 
              → (ρ ρ' : GenEnv)
              → GenEnvMorph ρ ρ'
              → NaturalTransformation F G 
              → GenEnvMorph (ρ  [ φ :fv= F ])
                            (ρ' [ φ :fv= G ])
extendmorph2 {k} φ {F} {G} ρ ρ' f η = extendmorph-η {k} {F} {G} ρ' φ η ∘GenEnv extendmorph-idF {k} φ F ρ ρ' f 

--------------------------------
-- Functor laws for extendGenEnv2
extendmorph2-identity : ∀ {k} (φ : FVar k) ρ
                        → (F : Category.Obj [C^ k ,C]) 
                        → GenEnvCat [ (extendmorph2 φ {F} {F} ρ ρ idGenEnv (Category.id [C^ k ,C]))
                          ≈ (Category.id GenEnvCat {ρ [ φ :fv= F ]}) ]
                        {-
                        → ∀ {j : ℕ} {ψ : FVar j} 
                        → ([C^ j ,C] Category.≈
                         GenEnvMorph.fv
                         (extendmorph2 φ {F} {F} ρ ρ (Category.id GenEnvCat) (Category.id [C^ k ,C]))
                         ψ)
                        (GenEnvMorph.fv (Category.id GenEnvCat {ρ [ φ :fv= F ]}) ψ)
                        -}
extendmorph2-identity (φ ^F k) ρ F {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = C.identityʳ 
... | yes ≡.refl | no _ = C.identityʳ
... | no _ | _ = C.identityʳ



extendmorph2-homomorphism : ∀ {k} (φ : FVar k) {F1 F2 F3 : Category.Obj [C^ k ,C]} 
                              {ρ1 ρ2 ρ3 : GenEnv}
                              → (f : GenEnvMorph ρ1 ρ2) (η : NaturalTransformation F1 F2)
                              → (g : GenEnvMorph ρ2 ρ3) (δ : NaturalTransformation F2 F3)
                              → GenEnvCat [ (extendmorph2 φ {F1} {F3} ρ1 ρ3 (g ∘GenEnv f) (δ ∘v η))
                                ≈ (extendmorph2 φ {F2} {F3} ρ2 ρ3 g δ) ∘GenEnv (extendmorph2 φ {F1} {F2} ρ1 ρ2 f η) ] 
                              {-
                              → ∀ {j : ℕ} {ψ : FVar j} 
                              → {Xs : Vec C.Obj j}
                              -- {x : Functor.F₀ (GenEnv.fv (ρ1 [ φ :fv= F1 ]) ψ) Xs} →
                              → C [
                                    NaturalTransformation.η
                                    (GenEnvMorph.fv (extendmorph2 φ {F1} {F3} ρ1 ρ3 (g ∘GenEnv f) (δ ∘v η)) ψ) Xs
                                  ≈ 
                                    NaturalTransformation.η
                                    (GenEnvMorph.fv ((extendmorph2 φ {F2} {F3} ρ2 ρ3 g δ) ∘GenEnv (extendmorph2 φ {F1} {F2} ρ1 ρ2 f η)) ψ) Xs
                                  ]
                                  -}
extendmorph2-homomorphism (φ ^F k) f η g δ {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = begin  ((δXs ∘ ηXs) ∘ id)
                                        ≈⟨ C.identityʳ ⟩
                                        ( δXs ∘ ηXs)
                                        ≈⟨ C.∘-resp-≈ (C.Equiv.sym C.identityʳ ) (C.Equiv.sym C.identityʳ) ⟩
                                        ((δXs ∘ id) ∘ (ηXs ∘ id)) ∎     
  where δXs = NaturalTransformation.η δ Xs
        ηXs = NaturalTransformation.η η Xs
-- Goal: (NaturalTransformation.η δ Xs C.∘
--        NaturalTransformation.η η Xs)
--       C.∘ C.id
--       C.≈
--       (NaturalTransformation.η δ Xs C.∘ C.id) C.∘
--       NaturalTransformation.η η Xs C.∘ C.id
... | yes ≡.refl | no _ = begin (id ∘ (gXs ∘ fXs))
                                ≈⟨ C.identityˡ ⟩
                                gXs ∘ fXs 
                                ≈⟨ C.∘-resp-≈ (C.Equiv.sym C.identityˡ) (  (C.Equiv.sym C.identityˡ)) ⟩
                                ((id ∘ gXs) ∘ (id ∘ fXs)) ∎ 
  where gXs = NaturalTransformation.η (GenEnvMorph.fv g (ψ ^F j)) Xs 
        fXs = NaturalTransformation.η (GenEnvMorph.fv f (ψ ^F j)) Xs
... | no _ | _ = begin (id ∘ (gXs ∘ fXs))
                                ≈⟨ C.identityˡ ⟩
                                gXs ∘ fXs 
                                ≈⟨ C.∘-resp-≈ (C.Equiv.sym C.identityˡ) (  (C.Equiv.sym C.identityˡ)) ⟩
                                ((id ∘ gXs) ∘ (id ∘ fXs)) ∎ 
  where gXs = NaturalTransformation.η (GenEnvMorph.fv g (ψ ^F j)) Xs 
        fXs = NaturalTransformation.η (GenEnvMorph.fv f (ψ ^F j)) Xs

extendmorph2-resp : ∀ {k} (φ : FVar k) {ρ ρ' : GenEnv} 
                      {f g : GenEnvMorph ρ ρ'}
                      {F G : Functor (C^ k) C}
                      {η δ : NaturalTransformation F G}
                      (f≈g : (GenEnvCat Category.≈ f) g)
                      (η≈δ : ([C^ k ,C] Category.≈ η) δ) 
                      → GenEnvCat [ (extendmorph2 φ {F} {G} ρ ρ' f η) ≈ (extendmorph2 φ  {F} {G} ρ ρ' g δ) ]
                      {-
                      → ∀ {j : ℕ} {ψ : FVar j} 
                      → ([C^ j ,C] Category.≈
                        GenEnvMorph.fv (extendmorph2 φ {F} {G} ρ ρ' f η) ψ)
                        (GenEnvMorph.fv (extendmorph2 φ  {F} {G} ρ ρ' g δ) ψ)
                        -}
extendmorph2-resp (φ ^F k) {η = η} {δ} f≈g η≈δ {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = C.∘-resp-≈ η≈δ C.Equiv.refl -- η≈δ 
... | yes ≡.refl | no _ = C.∘-resp-≈ C.Equiv.refl f≈g -- f≈g 
... | no _ | _ =  C.∘-resp-≈ C.Equiv.refl f≈g -- f≈g 



-- f [ φs :fvs= ηs ]
-- 
-- -- how does this decompose ? 
-- can we prove that 
--  f [ φs :fvs= ηs ] [ φ :fvs= η ]
-- ≈ f [ φs :fvs= ηs ] [ φ :fvs= η ]
extendmorph2-vec : ∀ {k n } (φs : Vec (FVar k) n)
                (Fs Gs : Vec (Functor (C^ k) C) n)
              → (ρ ρ' : GenEnv)
              → GenEnvMorph ρ ρ'
              → foreach2 (NaturalTransformation) Fs Gs
              → GenEnvMorph (ρ  [ φs :fvs= Fs ])
                            (ρ' [ φs :fvs= Gs ])
extendmorph2-vec {k} {zero} [] [] [] ρ ρ' f bigtt = f
extendmorph2-vec {k} {suc n} (φ ∷ φs) (F ∷ Fs) (G ∷ Gs) ρ ρ' f (η , ηs) = 
      record { eqTC = GenEnvMorph.eqTC f 
             ; fv = GenEnvMorph.fv 
                        (extendmorph2 {k} φ (ρ [ φs :fvs= Fs ]) (ρ' [ φs :fvs= Gs ]) 
                            (extendmorph2-vec {k} {n} φs Fs Gs ρ ρ' f ηs) η) }



-- a kind of natural condition
-- that says a morphism of environments
-- f [ φ := η ]
-- can be decomposed into
-- f [ φ := id_F ] ∘GenEnv id_ρ [ φ := η ] 
extendmorph2-nat : ∀ {k} (φ : FVar k)
                {F G : Functor (C^ k) C} 
              → (ρ ρ' : GenEnv)
              → (f : GenEnvMorph ρ ρ')
              → (η : NaturalTransformation F G)
              → GenEnvCat [
              extendmorph2 φ {F = G} {G = G} ρ ρ' f idnat 
              ∘GenEnv extendmorph2 φ ρ ρ idGenEnv η 
              ≈
              extendmorph2 φ ρ ρ' f η 
              ]
extendmorph2-nat {k} (φ ^F k) {F} {G} ρ ρ' f η {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = id-comm-id-idˡ (ηXs ∘ id)
  where ηXs = NaturalTransformation.η η Xs 
... | no _ | _ = id-comm-id-idʳ (id ∘ fXs)
  where fXs = NaturalTransformation.η (GenEnvMorph.fv f (ψ ^F j)) Xs
... | yes ≡.refl | no _ = id-comm-id-idʳ (id ∘ fXs)
  where fXs = NaturalTransformation.η (GenEnvMorph.fv f (ψ ^F j)) Xs




-- a kind of naturality condition
-- f [ φs := id_Fs ] ∘GenEnv id_ρ [ φs := ηs ]
-- ≈ f [ φs := ηs ]
extendmorph2-vec-nat : ∀ {k n } (φs : Vec (FVar k) n)
                   → (Fs Gs : Vec (Functor (C^ k) C) n)
                   → (ρ ρ' : GenEnv)
                   → (f : GenEnvMorph ρ ρ')
                   → (ηs : foreach2 (NaturalTransformation) Fs Gs)
                   → GenEnvCat [
                     extendmorph2-vec φs Gs Gs ρ ρ' f (make-foreach2-homg {As = Gs} idnat)
                     ∘GenEnv
                     extendmorph2-vec φs Fs Gs ρ ρ idGenEnv ηs
                     ≈ 
                     extendmorph2-vec φs Fs Gs ρ ρ' f ηs 
                     ]
extendmorph2-vec-nat [] [] [] ρ ρ' f bigtt = C.identityʳ
extendmorph2-vec-nat ((φ ^F k) ∷ φs) (F ∷ Fs) (G ∷ Gs) ρ ρ' f (η , ηs) {j} {ψ ^F j} {Zs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = id-comm-id-idˡ (ηZs ∘ id)
  where ηZs = NaturalTransformation.η η Zs 
... | no _       | _    = id-comm-1 ρηZs fZs fηZs (extendmorph2-vec-nat φs Fs Gs ρ ρ' f ηs)     
  where fZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs Gs Gs ρ ρ' f (make-foreach2-homg idnat)) (ψ ^F j)) Zs
        ρηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs Fs Gs ρ ρ idGenEnv ηs) (ψ ^F j)) Zs
        fηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs Fs Gs ρ ρ' f ηs) (ψ ^F j)) Zs
... | yes ≡.refl | no _ = id-comm-1 ρηZs fZs fηZs (extendmorph2-vec-nat φs Fs Gs ρ ρ' f ηs)     
  where fZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs Gs Gs ρ ρ' f (make-foreach2-homg idnat)) (ψ ^F j)) Zs
        ρηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs Fs Gs ρ ρ idGenEnv ηs) (ψ ^F j)) Zs
        fηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs Fs Gs ρ ρ' f ηs) (ψ ^F j)) Zs


open SetCats.0Functors C 

-- specifically for 0-ary variables 
extendmorph2-vec-nat-αs : ∀ {n} (φs : Vec (FVar 0) n)
                   → (Xs Ys : Vec C.Obj n)
                   → (ρ ρ' : GenEnv)
                   → (f : GenEnvMorph ρ ρ')
                   → (gs : (C^ n) [ Xs  , Ys ] )
                   → GenEnvCat [
                     extendmorph2-vec φs (to0FunctorsGen Ys) (to0FunctorsGen Ys) ρ ρ' f (toConstNatsGen (idVec Ys)) 
                     ∘GenEnv
                     extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ ρ idGenEnv (toConstNatsGen gs)
                     ≈ 
                     extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ ρ' f (toConstNatsGen gs)
                     ]
extendmorph2-vec-nat-αs [] [] [] ρ ρ' f bigtt = C.identityʳ 
extendmorph2-vec-nat-αs ((φ ^F k) ∷ φs) (X ∷ Xs) (Y ∷ Ys) ρ ρ' f (g , gs) {j} {ψ ^F j} {Zs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = id-comm-id-idˡ (g ∘ id)
... | no _       | _    = id-comm-1 ρηZs fZs fηZs (extendmorph2-vec-nat-αs φs Xs Ys ρ ρ' f gs) 
  where fZs  = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (to0FunctorsGen Ys) (to0FunctorsGen Ys) ρ ρ' f (toConstNatsGen (idVec Ys))) (ψ ^F j)) Zs
        ρηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ ρ idGenEnv (toConstNatsGen gs)) (ψ ^F j)) Zs
        fηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ ρ' f (toConstNatsGen gs)) (ψ ^F j)) Zs
... | yes ≡.refl | no _ = id-comm-1 ρηZs fZs fηZs (extendmorph2-vec-nat-αs φs Xs Ys ρ ρ' f gs) 
  where fZs  = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (to0FunctorsGen Ys) (to0FunctorsGen Ys) ρ ρ' f (toConstNatsGen (idVec Ys))) (ψ ^F j)) Zs
        ρηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ ρ idGenEnv (toConstNatsGen gs)) (ψ ^F j)) Zs
        fηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ ρ' f (toConstNatsGen gs)) (ψ ^F j)) Zs



-- other direction commutes as well 
extendmorph2-vec-nat-αs-sym : ∀ {n} (φs : Vec (FVar 0) n)
                   → (Xs Ys : Vec C.Obj n)
                   → (ρ ρ' : GenEnv)
                   → (f : GenEnvMorph ρ ρ')
                   → (gs : (C^ n) [ Xs ,  Ys ] )
                   → GenEnvCat [
                     extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ' ρ' idGenEnv (toConstNatsGen gs)
                     ∘GenEnv
                     extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Xs) ρ ρ' f (toConstNatsGen (idVec Xs)) 
                     ≈ 
                     extendmorph2-vec φs (to0FunctorsGen Xs) (to0FunctorsGen Ys) ρ ρ' f (toConstNatsGen gs)
                     ]
extendmorph2-vec-nat-αs-sym [] [] [] ρ ρ' f bigtt = C.identityˡ 
extendmorph2-vec-nat-αs-sym ((φ ^F k) ∷ φs) (X ∷ Xs) (Y ∷ Ys) ρ ρ' f (g , gs) {j} {ψ ^F j} {Zs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = id-comm-id-idʳ (g ∘ id)
... | no _       | _    = id-comm-1 ρηZs fZs fηZs (extendmorph2-vec-nat-αs-sym φs Xs Ys ρ ρ' f gs)  
  where fZs  = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (vmap const Xs) (vmap const Ys) ρ' ρ' idGenEnv (toConstNatsGen gs)) (ψ ^F j)) Zs
        ρηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (vmap const Xs) (vmap const Xs) ρ ρ' f (toConstNatsGen (idVec Xs))) (ψ ^F j)) Zs
        fηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (vmap const Xs) (vmap const Ys) ρ ρ' f (toConstNatsGen gs)) (ψ ^F j)) Zs
... | yes ≡.refl | no _ = id-comm-1 ρηZs fZs fηZs (extendmorph2-vec-nat-αs-sym φs Xs Ys ρ ρ' f gs)  
  where fZs  = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (vmap const Xs) (vmap const Ys) ρ' ρ' idGenEnv (toConstNatsGen gs)) (ψ ^F j)) Zs
        ρηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (vmap const Xs) (vmap const Xs) ρ ρ' f (toConstNatsGen (idVec Xs))) (ψ ^F j)) Zs
        fηZs = NaturalTransformation.η (GenEnvMorph.fv (extendmorph2-vec φs (vmap const Xs) (vmap const Ys) ρ ρ' f (toConstNatsGen gs)) (ψ ^F j)) Zs



extendmorph2-vec-identity : ∀ {k} (αs : Vec (FVar 0) k) (ρ : GenEnv)
                              (As : Vec C.Obj k)
                              → GenEnvCat [ 
                                  extendmorph2-vec αs (to0FunctorsGen As) (to0FunctorsGen As) ρ ρ (Category.id GenEnvCat) (toConstNatsGen (Category.id (C^ k)))
                                ≈ Category.id GenEnvCat {ρ [ αs :fvs= to0FunctorsGen As ]} ] 
extendmorph2-vec-identity {.0} [] ρ [] = C.Equiv.refl
-- extendmorph2-vec-identity {.0} {[]} ρ [] {j} {φ} {Xs} {x} = ≡.refl
extendmorph2-vec-identity {suc k} (α ∷ αs) ρ (A ∷ As) = 
  let id0 = Category.id [C^ 0 ,C]
      idAs = Category.id (C^ k)
      ρAs = ρ [ αs :fvs= to0FunctorsGen As ]
      -- 
      e2id : GenEnvCat [
            extendmorph2 α ρAs ρAs idGenEnv id0
            ≈ Category.id GenEnvCat ]
      e2id = extendmorph2-identity (α ) ρAs (ConstF A) 
      -- 
      e2vec-id : GenEnvCat [
            extendmorph2-vec αs (to0FunctorsGen As) (to0FunctorsGen As) ρ ρ idGenEnv (toConstNatsGen idAs)
            ≈ Category.id GenEnvCat ]
      e2vec-id = extendmorph2-vec-identity αs ρ As 

    in GEnvHR.begin
      extendmorph2 {0} α ρAs ρAs (extendmorph2-vec αs (to0FunctorsGen As) (to0FunctorsGen As) ρ ρ (idGenEnv {ρ}) (toConstNatsGen (idVec As))) (ConstNat id)
    GEnvHR.≈⟨ extendmorph2-resp α e2vec-id C.Equiv.refl ⟩
    extendmorph2 α ρAs ρAs (idGenEnv {ρAs}) (id0 {ConstF A})
    GEnvHR.≈⟨ e2id ⟩ 
      idGenEnv 
    GEnvHR.∎
    where module GEnvHR = Category.HomReasoning GenEnvCat 




extendmorph2-vec-resp : ∀ {k} (αs : Vec (FVar 0) k) (ρ ρ' : GenEnv)
                          (f g : GenEnvMorph ρ ρ')
                          (As Bs : Vec C.Obj k)
                          (hs is : (C^ k) [ As ,  Bs ] )
                          (f≈g : (GenEnvCat Category.≈ f) g)
                          (hs≈is : (C^ k) [ hs ≈ is ] ) 
                          → GenEnvCat [
                            extendmorph2-vec {0} {k} αs (to0FunctorsGen As) (to0FunctorsGen Bs) ρ ρ' f (toConstNatsGen hs)
                            ≈ extendmorph2-vec {0} {k} αs (to0FunctorsGen As) (to0FunctorsGen Bs) ρ ρ' g (toConstNatsGen is)
                          ] 
                          
extendmorph2-vec-resp {0} [] ρ ρ' f g [] [] bigtt bigtt f≈g bigtt {j} {φ} {Xs} = f≈g 
extendmorph2-vec-resp {suc k} (α ∷ αs) ρ ρ' f g (A ∷ As) (B ∷ Bs) (h , hs) (i , is) f≈g (h≈i , hs≈is) = 
  let ρAs = ρ [ αs :fvs= to0FunctorsGen As ]
      ρ'Bs = ρ' [ αs :fvs= to0FunctorsGen Bs ]
      As0 = to0FunctorsGen As
      Bs0 = to0FunctorsGen Bs
      -- 
      e2-vec-f-hs≈e2-vec-g-is  : GenEnvCat [
              extendmorph2-vec αs As0 Bs0 ρ ρ' f (toConstNatsGen hs)
              ≈ extendmorph2-vec αs As0 Bs0 ρ ρ' g (toConstNatsGen is) ]
      e2-vec-f-hs≈e2-vec-g-is = extendmorph2-vec-resp αs ρ ρ' f g As Bs hs is f≈g hs≈is
      --
    in GEnvHR.begin
      extendmorph2 α ρAs ρ'Bs (extendmorph2-vec αs As0 Bs0 ρ ρ' f (toConstNatsGen hs)) (ConstNat h)
    GEnvHR.≈⟨ extendmorph2-resp α e2-vec-f-hs≈e2-vec-g-is h≈i ⟩
      extendmorph2 α ρAs ρ'Bs (extendmorph2-vec αs As0 Bs0 ρ ρ' g (toConstNatsGen is)) (ConstNat i)
    GEnvHR.∎ 
    where module GEnvHR = Category.HomReasoning GenEnvCat 

extendmorph2-vec-homomorphism : ∀ {k} (αs : Vec (FVar 0) k) (ρ1 ρ2 ρ3 : GenEnv)
                                  (f : GenEnvMorph ρ1 ρ2) (g : GenEnvMorph ρ2 ρ3) 
                                  (As Bs Cs : Vec C.Obj k)
                                  (hs : (C^ k) [ As ,  Bs ] )
                                  (is : (C^ k) [ Bs ,  Cs ] )
                                  → GenEnvCat [ 
                                  extendmorph2-vec αs (to0FunctorsGen As) (to0FunctorsGen Cs) ρ1 ρ3 (g ∘GenEnv f) (toConstNatsGen (is ∘Vec hs))
                                  ≈ 
                                  extendmorph2-vec αs (to0FunctorsGen Bs) (to0FunctorsGen Cs) ρ2 ρ3 g (toConstNatsGen is)
                                  ∘GenEnv
                                  extendmorph2-vec αs (to0FunctorsGen As) (to0FunctorsGen Bs) ρ1 ρ2 f (toConstNatsGen hs)
                                  ]
extendmorph2-vec-homomorphism [] ρ1 ρ2 ρ3 f g [] [] [] bigtt bigtt = C.Equiv.refl
extendmorph2-vec-homomorphism (α ∷ αs) ρ1 ρ2 ρ3 f g (A ∷ As) (B ∷ Bs) (C ∷ Cs) (h , hs) (i , is) = 
  let As0 = to0FunctorsGen As
      Bs0 = to0FunctorsGen Bs
      Cs0 = to0FunctorsGen Cs
      ρ1As = ρ1 [ αs :fvs= As0 ]
      ρ2Bs = ρ2 [ αs :fvs= Bs0 ]
      ρ3Cs = ρ3 [ αs :fvs= Cs0 ]
      -- 
      e2-vec-hom : GenEnvCat [
          extendmorph2-vec αs As0 Cs0 ρ1 ρ3 (g ∘GenEnv f) (toConstNatsGen (is ∘Vec hs))
          ≈ extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNatsGen is)
            ∘GenEnv extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNatsGen hs) ]
      e2-vec-hom = extendmorph2-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is 
      -- 
  in GEnvHR.begin
      extendmorph2 α ρ1As ρ3Cs  
        (extendmorph2-vec αs As0 Cs0 ρ1 ρ3 (g ∘GenEnv f) (toConstNatsGen (is ∘Vec hs)))
        (ConstNat (i ∘ h))
    GEnvHR.≈⟨ extendmorph2-resp α e2-vec-hom C.Equiv.refl ⟩ 
      extendmorph2 α ρ1As ρ3Cs  
        (extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNatsGen is)
            ∘GenEnv extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNatsGen hs))
        (ConstNat i ∘v ConstNat h)
    GEnvHR.≈⟨ extendmorph2-homomorphism α (extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNatsGen hs)) (ConstNat h) 
                                   (extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNatsGen is)) (ConstNat i) ⟩ 
      (extendmorph2 α ρ2Bs ρ3Cs (extendmorph2-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNatsGen is)) (ConstNat i))
      ∘GenEnv 
      (extendmorph2 α ρ1As ρ2Bs (extendmorph2-vec αs As0 Bs0 ρ1 ρ2 f (toConstNatsGen hs)) (ConstNat h))
    GEnvHR.∎ 
    where module GEnvHR = Category.HomReasoning GenEnvCat 




-------------------------------------------------------
-- Environment extensinon functors 
-------------------------------------------------------


-- λ ρ F → ρ [ φ := F ])
extendGenEnv2 : ∀ {k} → (φ : FVar k) 
              → Functor (Product GenEnvCat [C^ k ,C]) GenEnvCat
extendGenEnv2 φ = record
  { F₀ = λ { (ρ , F) → ρ [ φ :fv= F ] } 
  ; F₁ = λ { {ρ , F} {ρ' , G} (f , η) → extendmorph2 φ  {F} {G} ρ ρ' f η }
  ; identity = λ { {ρ , F} → extendmorph2-identity φ ρ F }
  ; homomorphism = λ { {ρ1 , F1} {ρ2 , F2} {ρ3 , F3} {f , η} {g , δ} {Xs} → extendmorph2-homomorphism φ f η g δ } 
  ; F-resp-≈ = λ { (f≈g , η≈δ) {j} {ψ} → extendmorph2-resp φ f≈g η≈δ }
  }


-- -- 0-ary version of extendGenEnv2 that uses category C instead of [C^ 0 , C] 
-- used to define 'semantic substitution' and prove that syntactic substitution
-- interacts nicely with semantic substitution 
extendGenEnv-α : ∀ (α : FVar 0) 
                → Functor (Product GenEnvCat C) GenEnvCat
extendGenEnv-α α = extendGenEnv2 α ∘F (idF ⁂  C⇒0Functors ) 



-- inline definition for faster type-checking of TEnv, etc. 
-- 
-- -- it's also easier to prove that this version doesn't alter the non-functorial part of environment 
-- 
-- -- previously called extendGenEnv-ρ×As-inline 
extendGenEnv-ρ×As : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product GenEnvCat (C^ k)) GenEnvCat
extendGenEnv-ρ×As αs = record
  { F₀ = λ { (ρ , As) → ρ [ αs :fvs= to0FunctorsGen As ] } 
  ; F₁ = λ { {ρ , As} {ρ' , Bs} (f , gs) → extendmorph2-vec αs (to0FunctorsGen As) (to0FunctorsGen Bs) ρ ρ' f (toConstNatsGen gs) }
  ; identity = λ { {ρ , As} {j} {φ} {Xs} → extendmorph2-vec-identity αs ρ As {j} {φ} {Xs} }
  ; homomorphism = λ { {ρ1 , As} {ρ2 , Bs} {ρ3 , Cs} {f , hs} {g , is} → extendmorph2-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is }
  ; F-resp-≈ = λ { {ρ , As} {ρ' , Bs} {f , hs} {g , ks} (f≈g , hs≈ks) → extendmorph2-vec-resp αs ρ ρ' f g As Bs hs ks f≈g hs≈ks }
  } 



extendGenEnv-ρ×As-noinline : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product GenEnvCat (C^ k)) GenEnvCat
extendGenEnv-ρ×As-noinline [] = πˡ 
extendGenEnv-ρ×As-noinline {suc k} (α ∷ αs) = 
    let r : Functor (Product GenEnvCat (C^ k)) GenEnvCat
        r = extendGenEnv-ρ×As-noinline αs 
        -- 
        extend-α : Functor (Product GenEnvCat [C^ 0 ,C]) GenEnvCat
        extend-α = extendGenEnv2 α
        -- change [C^0 , C] to C in extend-α
        extend-α-C : Functor (Product GenEnvCat C) GenEnvCat
        extend-α-C = extendGenEnv2 α ∘F (idF ⁂ C⇒0Functors ) -- C→0Functors)
        -- 
        decswap : Functor (C^ (suc k)) (Product (C^ k) C)
        decswap = Swap ∘F C^decompose k 
        -- 
        decompose : Functor (Product GenEnvCat (C^ (suc k))) (Product (Product GenEnvCat (C^ k)) C)
        decompose = assocʳ GenEnvCat (C^ k) C ∘F (idF ⁂ decswap)
        -- 
        extend-αs : Functor (Product GenEnvCat (C^ (suc k))) (Product GenEnvCat C)
        extend-αs = (r ⁂ idF) ∘F decompose 

        in extend-α-C ∘F extend-αs 


module test-extend where
    postulate
        A B D : C.Obj
        a b d : FVar 0 
        env : GenEnv 

    test-extend : Vec (FVar 0) 3 → GenEnv → GenEnv
    test-extend αs ρ = Functor.F₀ (extendGenEnv-ρ×As-noinline αs) (ρ , (A  ∷ B ∷ (D ∷ [])))  

    test-extend-test : GenEnv
    test-extend-test = test-extend (a ∷ b ∷ (d ∷ [])) env  


-- extendGenEnv-As×ρ : ∀ {k} → (αs : Vec (FVar 0) k) 
--                 → Functor (Product (C^ k) GenEnvCat) GenEnvCat
-- extendGenEnv-As×ρ αs = extendGenEnv-ρ×As αs ∘F Swap


-- used to define semantic analogue of second order subst 
-- 
-- sends ρ to ρ [ αs := _ ] 
extendGenEnv-αs-curry : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor GenEnvCat (Functors (C^ k) GenEnvCat)
extendGenEnv-αs-curry αs = curry.F₀ (extendGenEnv-ρ×As αs)


-- need this to define semantics of natural transformations 
extendGenEnv-αs : ∀ {k} → (αs : Vec (FVar 0) k) → GenEnv
                → Functor (C^ k) GenEnvCat
extendGenEnv-αs αs ρ = Functor.F₀ (curry.F₀ (extendGenEnv-ρ×As αs)) ρ 




extendTEnv2 : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
            → Functor (Product (Product GenEnvCat [C^ k ,C]) (C^ k)) GenEnvCat
extendTEnv2 φ αs = (extendGenEnv-ρ×As αs) ∘F ((extendGenEnv2 φ ∘F πˡ) ※ πʳ)



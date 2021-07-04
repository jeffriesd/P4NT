

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
open import Syntax.NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
open import Utils


module RTEnvironments.EnvironmentExtension {o l e o' l' e' : Level}
  {R : Category o' l' e'} 
  {D : ℕ → Category o l e}
  {D⊤ : (k : ℕ) → Terminal (D k)}
  {toD0 : Functor R (D 0)}
  where 
-- About this file: 
-- In this file we generalize the environment extension constructions 
-- to work for any categories D and R.
--
-- D is a family of categories indexed by natural numbers, while R is 
-- a category whose objects can be turned into objects of D 0 
--
-- For our purposes, we will use D = RTCat and R = Rels 
-- 
-- The objects of D k are used to interpret functor variables of arity k. 
-- Morphism of D are used to represent morphisms of environments. 
-- Dt and Dtm are used to define trivFVEnv. 


open import RTEnvironments.Core {o} {l} {e} {D} {D⊤}

module R = Category R



-- some useful identities that appear in functoriality proofs below 
module IdComm {o l e : Level} (C : Category o l e) where 
    private module C = Category C 
    open C
    open C.HomReasoning
  
    -- used in extendfv-morph-vec-nat 
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

open IdComm 



-------------------------------------------------------
-- extend morphisms of environments 
-------------------------------------------------------

-- TODO maybe rename this to identity-rho or something? 
-- 
-- this gives rise to a functor extendEnv : [C^k ,C] → EnvCat
-- λ F → ρ [ φ :fv= F ]
extendmorph-η : ∀ {k} 
                {F G : DObj k} 
              → (ρ : Env)
              → (φ : FVar k)
              → (D k) [ F ,  G ] 
              → EnvMorph (ρ [ φ ∷ Vec.[] :fvs= F ∷ Vec.[] ])
                            (ρ [ φ ∷ Vec.[] :fvs= G ∷ Vec.[] ])
extendmorph-η {k} {F} {G} record { tc = tc ; fv = fv } (φ ^F k) η = record { eqTC = ≡.refl ; fv = λ ψ → mapfv ψ }
  where mapfv : ∀ {j} (ψ : FVar j) 
          → (D j) [ (Env.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ) 
                  , (Env.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= G ∷ Vec.[] ]) ψ) ]
        mapfv (ψ ^F j) with eqNat k j | φ ≟ ψ 
        ... | yes ≡.refl | yes ≡.refl = η 
        ... | no _ | _ = Did j 
        ... | yes ≡.refl | no _ = Did j 



-- this gives rise to a functor extendEnvF : EnvCat → EnvCat  
-- λ ρ → ρ [ φ :fv= F ]
extendmorph-idF : ∀  {k} (φ : FVar k) (F : DObj k)
              → (ρ ρ' : Env)
              → EnvMorph ρ ρ'
              → EnvMorph (ρ  [ φ :fv= F ]) 
                            (ρ' [ φ :fv= F ]) 
extendmorph-idF {k} (φ ^F k) F ρ ρ' f = record { eqTC = EnvMorph.eqTC f ; fv = fvmap } 
          where fvmap : ∀ {j} (ψ : FVar j) 
                  → (D j) [ (Env.fv (ρ  [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                          , (Env.fv (ρ' [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ) ] 
                fvmap (ψ ^F j) with eqNat k j | φ ≟ ψ 
                ... | yes ≡.refl | yes ≡.refl = Did j -- mkIdNatTr' F
                ... | no _ | _ = EnvMorph.fv f (ψ ^F j)
                ... | yes ≡.refl | no _ = EnvMorph.fv f (ψ ^F j)



extendfv-morph : ∀ {k} (φ : FVar k)
                {F G : DObj k} 
              → (ρ ρ' : Env)
              → EnvMorph ρ ρ'
              → (D k) [ F ,  G ] 
              → EnvMorph (ρ  [ φ :fv= F ])
                            (ρ' [ φ :fv= G ])
extendfv-morph {k} φ {F} {G} ρ ρ' f η = extendmorph-η {k} {F} {G} ρ' φ η ∘Env extendmorph-idF {k} φ F ρ ρ' f 

--------------------------------
-- Functor laws for extendEnv2
extendfv-morph-identity : ∀ {k} (φ : FVar k) (ρ : Env)
                        → (F : Category.Obj (D k)) 
                        → EnvCat [ (extendfv-morph φ {F} {F} ρ ρ idEnv (Category.id (D k)))
                          ≈ (Category.id EnvCat {ρ [ φ :fv= F ]}) ]
                        {-
                        → ∀ {j : ℕ} {ψ : FVar j} 
                        → ([C^ j ,C] Category.≈
                         EnvMorph.fv
                         (extendfv-morph φ {F} {F} ρ ρ (Category.id EnvCat) (Category.id (D k)))
                         ψ)
                        (EnvMorph.fv (Category.id EnvCat {ρ [ φ :fv= F ]}) ψ)
                        -}
extendfv-morph-identity (φ ^F k) ρ F {j} {ψ ^F j} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = Category.identityʳ  (D k)
... | yes ≡.refl | no _ = Category.identityʳ (D k)
... | no _ | _ = Category.identityʳ (D j)



extendfv-morph-homomorphism : ∀ {k} (φ : FVar k) {F1 F2 F3 : Category.Obj (D k)} 
                              {ρ1 ρ2 ρ3 : Env}
                              → (f : EnvMorph ρ1 ρ2) (η : (D k) [ F1 ,  F2 ])
                              → (g : EnvMorph ρ2 ρ3) (δ : (D k) [ F2 ,  F3 ] )
                              → EnvCat [ (extendfv-morph φ {F1} {F3} ρ1 ρ3 (g ∘Env f) ((D k) [ δ ∘ η ] ))
                                ≈ (extendfv-morph φ {F2} {F3} ρ2 ρ3 g δ) ∘Env (extendfv-morph φ {F1} {F2} ρ1 ρ2 f η) ] 
extendfv-morph-homomorphism (φ ^F k) f η g δ {j} {ψ ^F j} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl =  begin (δ ∘ η) ∘ id
                                       ≈⟨ identityʳ  ⟩
                                       δ ∘ η 
                                       ≈˘⟨ ∘-resp-≈ identityʳ identityʳ  ⟩
                                       (δ ∘ id) ∘ η ∘ id ∎  
  where open Category (D k)
        open Category.HomReasoning (D k)
... | yes ≡.refl | no _ = begin (id ∘ (gψ ∘ fψ))
                                ≈⟨ identityˡ ⟩
                                gψ ∘ fψ
                                ≈˘⟨ ∘-resp-≈ identityˡ identityˡ ⟩
                                (id ∘ gψ) ∘ (id ∘ fψ) ∎ 
  where gψ = EnvMorph.fv g (ψ ^F j)
        fψ = EnvMorph.fv f (ψ ^F j)
        open Category (D j)
        open Category.HomReasoning (D j)
... | no _ | _ = begin (id ∘ (gψ ∘ fψ))
                        ≈⟨ identityˡ ⟩
                        gψ ∘ fψ
                        ≈˘⟨ ∘-resp-≈ identityˡ identityˡ ⟩
                        (id ∘ gψ) ∘ (id ∘ fψ) ∎ 
  where gψ = EnvMorph.fv g (ψ ^F j)
        fψ = EnvMorph.fv f (ψ ^F j)
        open Category (D j)
        open Category.HomReasoning (D j)


extendfv-morph-resp : ∀ {k} (φ : FVar k) {ρ ρ' : Env} 
                      {f g : EnvMorph ρ ρ'}
                      {F G : DObj k}
                      {η δ : (D k) [ F ,  G ] }
                      (f≈g : (EnvCat Category.≈ f) g)
                      (η≈δ : ((D k) Category.≈ η) δ) 
                      → EnvCat [ (extendfv-morph φ {F} {G} ρ ρ' f η) ≈ (extendfv-morph φ  {F} {G} ρ ρ' g δ) ]
extendfv-morph-resp (φ ^F k) {η = η} {δ} f≈g η≈δ {j} {ψ ^F j} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = Category.∘-resp-≈ (D k) η≈δ (Category.Equiv.refl (D k))
... | yes ≡.refl | no _ = Category.∘-resp-≈ (D j) (Category.Equiv.refl (D j)) f≈g 
... | no _ | _ =  Category.∘-resp-≈ (D j) (Category.Equiv.refl (D j)) f≈g 



-- f [ φs :fvs= ηs ]
-- 
-- -- how does this decompose ? 
-- can we prove that 
--  f [ φs :fvs= ηs ] [ φ :fvs= η ]
-- ≈ f [ φs :fvs= ηs ] [ φ :fvs= η ]
extendfv-morph-vec : ∀ {k n } (φs : Vec (FVar k) n)
                (Fs Gs : Vec (DObj k) n)
              → (ρ ρ' : Env)
              → EnvMorph ρ ρ'
              → foreach2 (Category._⇒_ (D k)) Fs Gs
              → EnvMorph (ρ  [ φs :fvs= Fs ])
                            (ρ' [ φs :fvs= Gs ])
extendfv-morph-vec {k} {zero} [] [] [] ρ ρ' f bigtt = f
extendfv-morph-vec {k} {suc n} (φ ∷ φs) (F ∷ Fs) (G ∷ Gs) ρ ρ' f (η , ηs) = 
      record { eqTC = EnvMorph.eqTC f 
             ; fv = EnvMorph.fv 
                        (extendfv-morph {k} φ (ρ [ φs :fvs= Fs ]) (ρ' [ φs :fvs= Gs ]) 
                            (extendfv-morph-vec {k} {n} φs Fs Gs ρ ρ' f ηs) η) }



-- a kind of natural condition
-- that says a morphism of environments
-- f [ φ := η ]
-- can be decomposed into
-- f [ φ := id_F ] ∘Env id_ρ [ φ := η ] 
extendfv-morph-nat : ∀ {k} (φ : FVar k)
                {F G : DObj k} 
              → (ρ ρ' : Env)
              → (f : EnvMorph ρ ρ')
              → (η : (D k) [ F ,  G ])
              → EnvCat [
              extendfv-morph φ {F = G} {G = G} ρ ρ' f (Did k)
              ∘Env extendfv-morph φ ρ ρ idEnv η 
              ≈
              extendfv-morph φ ρ ρ' f η 
              ]
extendfv-morph-nat {k} (φ ^F k) {F} {G} ρ ρ' f η {j} {ψ ^F j} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = id-comm-id-idˡ (D k) ((D k) [ η ∘ (Did k) ])
... | no _ | _ = id-comm-id-idʳ (D j) ((D j) [ (Did j) ∘ fψ ])
  where fψ = EnvMorph.fv f (ψ ^F j)
... | yes ≡.refl | no _ = id-comm-id-idʳ (D j) ((D j) [ (Did j) ∘ fψ ])
  where fψ = EnvMorph.fv f (ψ ^F j)




-- a kind of naturality condition
-- f [ φs := id_Fs ] ∘Env id_ρ [ φs := ηs ]
-- ≈ f [ φs := ηs ]
extendfv-morph-vec-nat : ∀ {k n } (φs : Vec (FVar k) n)
                   → (Fs Gs : Vec (DObj k) n)
                   → (ρ ρ' : Env)
                   → (f : EnvMorph ρ ρ')
                   → (ηs : foreach2 (Category._⇒_ (D k))  Fs Gs)
                   → EnvCat [
                     extendfv-morph-vec φs Gs Gs ρ ρ' f (make-foreach2-homg {As = Gs} (Did k))
                     ∘Env
                     extendfv-morph-vec φs Fs Gs ρ ρ idEnv ηs
                     ≈ 
                     extendfv-morph-vec φs Fs Gs ρ ρ' f ηs 
                     ]
extendfv-morph-vec-nat {k} [] [] [] ρ ρ' f bigtt {j} = Category.identityʳ (D j)
extendfv-morph-vec-nat ((φ ^F k) ∷ φs) (F ∷ Fs) (G ∷ Gs) ρ ρ' f (η , ηs) {j} {ψ ^F j} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = id-comm-id-idˡ (D k) ((D k) [ η ∘ (Did k) ])

... | no _       | _    = id-comm-1 (D j) ρη fψ fη (extendfv-morph-vec-nat φs Fs Gs ρ ρ' f ηs)     
  where fψ = (EnvMorph.fv (extendfv-morph-vec φs Gs Gs ρ ρ' f (make-foreach2-homg (Did k))) (ψ ^F j))
        ρη = EnvMorph.fv (extendfv-morph-vec φs Fs Gs ρ ρ idEnv ηs) (ψ ^F j)
        fη = EnvMorph.fv (extendfv-morph-vec φs Fs Gs ρ ρ' f ηs) (ψ ^F j)
... | yes ≡.refl | no _ = id-comm-1 (D j) ρη fψ fη (extendfv-morph-vec-nat φs Fs Gs ρ ρ' f ηs)     
  where fψ = EnvMorph.fv (extendfv-morph-vec φs Gs Gs ρ ρ' f (make-foreach2-homg (Did k))) (ψ ^F j)
        ρη = EnvMorph.fv (extendfv-morph-vec φs Fs Gs ρ ρ idEnv ηs) (ψ ^F j)
        fη = EnvMorph.fv (extendfv-morph-vec φs Fs Gs ρ ρ' f ηs) (ψ ^F j)



-- use D0 for what would be RT 0 /Sets 
D0 : Category o l e 
D0 = D 0

module D0 = Category D0 

open VecCat R
R^ : ℕ → Category o' l' e'
R^ k = Cat^ k 

toRT0 : R.Obj → D0.Obj
toRT0 = Functor.F₀ toD0 

toRT0-map : ∀ {S S' : R.Obj} → R [ S , S' ] → D0 [ toRT0 S , toRT0 S' ] 
toRT0-map = Functor.F₁ toD0 

toRT0Vec : ∀ {n : ℕ} → Vec (R.Obj) n → Vec D0.Obj n 
toRT0Vec = vmap toRT0 

toRT0Vec-map : ∀ {n : ℕ} → {Rs Ss : Vec R.Obj n} → foreach2 R._⇒_ Rs Ss → foreach2 D0._⇒_ (toRT0Vec Rs) (toRT0Vec Ss) 
toRT0Vec-map {Rs = []} {[]} gs = bigtt
toRT0Vec-map {Rs = r ∷ rs} {s ∷ ss} (g , gs) = (Functor.F₁ toD0 g) , (toRT0Vec-map gs)

-- want to send vector of Rels 
-- to vector of RT0 
-- specifically for 0-ary variables 
extendfv-morph-vec-nat-αs : ∀ {n} (φs : Vec (FVar 0) n)
                   → (Xs Ys : Vec R.Obj n)
                   → (ρ ρ' : Env)
                   → (f : EnvMorph ρ ρ')
                   → (gs : (R^ n) [ Xs  , Ys ] )
                   → EnvCat [
                     extendfv-morph-vec φs (toRT0Vec Ys) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map (idVec Ys))
                     ∘Env
                     extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ idEnv (toRT0Vec-map gs)
                     ≈ 
                     extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map gs)
                     ]
extendfv-morph-vec-nat-αs [] [] [] ρ ρ' f bigtt {k} = Category.identityʳ (D k)
extendfv-morph-vec-nat-αs ((φ ^F k) ∷ φs) (X ∷ Xs) (Y ∷ Ys) ρ ρ' f (g , gs) {j} {ψ ^F j} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = begin (D0Rid ∘ id) ∘ D0g ∘ id
                                      ≈⟨ D0.∘-resp-≈ (D0.∘-resp-≈ (Functor.identity toD0) (D0.Equiv.refl)) (D0.Equiv.refl)  ⟩
                                      (id ∘ id) ∘ D0g ∘ id
                                      ≈⟨  id-comm-id-idˡ D0 (D0g ∘ id) ⟩
                                      D0g ∘ id ∎  
  where D0Rid = Functor.F₁ toD0 R.id
        D0g   = Functor.F₁ toD0 g 
        open Category D0
        open Category.HomReasoning D0
  
... | no _       | _    = id-comm-1 EnvCat ρη fψ fη (extendfv-morph-vec-nat-αs φs Xs Ys ρ ρ' f gs) 
  where fψ = extendfv-morph-vec φs (toRT0Vec Ys) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map (idVec Ys))
        ρη = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ idEnv (toRT0Vec-map gs)
        fη = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map gs)
... | yes ≡.refl | no _ = id-comm-1 EnvCat ρη fψ fη (extendfv-morph-vec-nat-αs φs Xs Ys ρ ρ' f gs) 
  where fψ = extendfv-morph-vec φs (toRT0Vec Ys) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map (idVec Ys))
        ρη = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ idEnv (toRT0Vec-map gs)
        fη = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map gs)




-- other direction commutes as well 
extendfv-morph-vec-nat-αs-sym : ∀ {n} (φs : Vec (FVar 0) n)
                   → (Xs Ys : Vec R.Obj n)
                   → (ρ ρ' : Env)
                   → (f : EnvMorph ρ ρ')
                   → (gs : (R^ n) [ Xs ,  Ys ] )
                   → EnvCat [
                     extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ' ρ' idEnv (toRT0Vec-map gs)
                     ∘Env
                     extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Xs) ρ ρ' f (toRT0Vec-map (idVec Xs)) 
                     ≈ 
                     extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map gs)
                     ]
extendfv-morph-vec-nat-αs-sym [] [] [] ρ ρ' f bigtt {k} = Category.identityˡ (D k) 
extendfv-morph-vec-nat-αs-sym ((φ ^F k) ∷ φs) (X ∷ Xs) (Y ∷ Ys) ρ ρ' f (g , gs) {j} {ψ ^F j} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = begin (D0g ∘ id) ∘ D0Rid ∘ id
                                      ≈⟨  D0.∘-resp-≈ (D0.Equiv.refl) (D0.∘-resp-≈ (Functor.identity toD0) D0.Equiv.refl)  ⟩
                                      (D0g ∘ id) ∘ id ∘ id
                                      ≈⟨ id-comm-id-idʳ D0 (D0g ∘ id) ⟩
                                      D0g ∘ id ∎  
  where D0Rid = Functor.F₁ toD0 R.id
        D0g   = Functor.F₁ toD0 g 
        open Category D0
        open Category.HomReasoning D0
  
... | no _       | _    = id-comm-1 EnvCat fψ ρ'η fη (extendfv-morph-vec-nat-αs-sym φs Xs Ys ρ ρ' f gs) 
  where fψ = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Xs) ρ ρ' f (toRT0Vec-map (idVec Xs))
        ρ'η = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ' ρ' idEnv (toRT0Vec-map gs)
        fη = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map gs)
... | yes ≡.refl | no _ = id-comm-1 EnvCat fψ ρ'η fη ( (extendfv-morph-vec-nat-αs-sym φs Xs Ys ρ ρ' f gs)) 
  where fψ = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Xs) ρ ρ' f (toRT0Vec-map (idVec Xs))
        ρ'η = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ' ρ' idEnv (toRT0Vec-map gs)
        fη = extendfv-morph-vec φs (toRT0Vec Xs) (toRT0Vec Ys) ρ ρ' f (toRT0Vec-map gs)






extendfv-morph-vec-identity : ∀ {k} (αs : Vec (FVar 0) k) (ρ : Env)
                              (As : Vec R.Obj k)
                              → EnvCat [ 
                                  extendfv-morph-vec αs (toRT0Vec As) (toRT0Vec As) ρ ρ (Category.id EnvCat) (toRT0Vec-map (Category.id (C^ k)))
                                ≈ Category.id EnvCat {ρ [ αs :fvs= toRT0Vec As ]} ] 
extendfv-morph-vec-identity {.0} [] ρ [] {k} = Category.Equiv.refl (D k) 
-- extendfv-morph-vec-identity {.0} {[]} ρ [] {j} {φ} {Xs} {x} = ≡.refl
extendfv-morph-vec-identity {suc k} (α ∷ αs) ρ (A ∷ As) = 
  let id0 = Category.id D0
      idAs = Category.id (R^ k)
      ρAs = ρ [ αs :fvs= toRT0Vec As ]
      -- 
      e2id : EnvCat [
            extendfv-morph α ρAs ρAs idEnv id0
            ≈ Category.id EnvCat ]
      e2id = extendfv-morph-identity (α ) ρAs (toRT0 A )
      -- 
      e2vec-id : EnvCat [
            extendfv-morph-vec αs (toRT0Vec As) (toRT0Vec As) ρ ρ idEnv (toRT0Vec-map idAs)
            ≈ Category.id EnvCat ]
      e2vec-id = extendfv-morph-vec-identity αs ρ As 

    in GEnvHR.begin
      extendfv-morph {0} α ρAs ρAs (extendfv-morph-vec αs (toRT0Vec As) (toRT0Vec As) ρ ρ (idEnv {ρ}) (toRT0Vec-map (idVec As))) (toRT0-map R.id)
    GEnvHR.≈⟨ extendfv-morph-resp α e2vec-id (Functor.identity toD0) ⟩ 
    extendfv-morph α ρAs ρAs (idEnv {ρAs}) (id0 {toRT0 A})
    GEnvHR.≈⟨ e2id ⟩ 
      idEnv 
    GEnvHR.∎
    where module GEnvHR = Category.HomReasoning EnvCat 

extendfv-morph-vec-resp : ∀ {k} (αs : Vec (FVar 0) k) (ρ ρ' : Env)
                          (f g : EnvMorph ρ ρ')
                          (As Bs : Vec R.Obj k)
                          (hs is : (C^ k) [ As ,  Bs ] )
                          (f≈g : (EnvCat Category.≈ f) g)
                          (hs≈is : (C^ k) [ hs ≈ is ] ) 
                          → EnvCat [
                            extendfv-morph-vec {0} {k} αs (toRT0Vec As) (toRT0Vec Bs) ρ ρ' f (toRT0Vec-map hs)
                            ≈ extendfv-morph-vec {0} {k} αs (toRT0Vec As) (toRT0Vec Bs) ρ ρ' g (toRT0Vec-map is)
                          ] 
                          
extendfv-morph-vec-resp {0} [] ρ ρ' f g [] [] bigtt bigtt f≈g bigtt {j} = f≈g 
extendfv-morph-vec-resp {suc k} (α ∷ αs) ρ ρ' f g (A ∷ As) (B ∷ Bs) (h , hs) (i , is) f≈g (h≈i , hs≈is) = 
  let ρAs = ρ [ αs :fvs= toRT0Vec As ]
      ρ'Bs = ρ' [ αs :fvs= toRT0Vec Bs ]
      As0 = toRT0Vec As
      Bs0 = toRT0Vec Bs
      -- 
      e2-vec-f-hs≈e2-vec-g-is  : EnvCat [
              extendfv-morph-vec αs As0 Bs0 ρ ρ' f (toRT0Vec-map hs)
              ≈ extendfv-morph-vec αs As0 Bs0 ρ ρ' g (toRT0Vec-map is) ]
      e2-vec-f-hs≈e2-vec-g-is = extendfv-morph-vec-resp αs ρ ρ' f g As Bs hs is f≈g hs≈is
      --
    in GEnvHR.begin
      extendfv-morph α ρAs ρ'Bs (extendfv-morph-vec αs As0 Bs0 ρ ρ' f (toRT0Vec-map hs)) (toRT0-map h)
    GEnvHR.≈⟨ extendfv-morph-resp α e2-vec-f-hs≈e2-vec-g-is (Functor.F-resp-≈ toD0 h≈i ) ⟩ 
      extendfv-morph α ρAs ρ'Bs (extendfv-morph-vec αs As0 Bs0 ρ ρ' g (toRT0Vec-map is)) (toRT0-map i)
    GEnvHR.∎ 
    where module GEnvHR = Category.HomReasoning EnvCat 

extendfv-morph-vec-homomorphism : ∀ {k} (αs : Vec (FVar 0) k) (ρ1 ρ2 ρ3 : Env)
                                  (f : EnvMorph ρ1 ρ2) (g : EnvMorph ρ2 ρ3) 
                                  (As Bs Cs : Vec R.Obj k)
                                  (hs : (C^ k) [ As ,  Bs ] )
                                  (is : (C^ k) [ Bs ,  Cs ] )
                                  → EnvCat [ 
                                  extendfv-morph-vec αs (toRT0Vec As) (toRT0Vec Cs) ρ1 ρ3 (g ∘Env f) (toRT0Vec-map (is ∘Vec hs))
                                  ≈ 
                                  extendfv-morph-vec αs (toRT0Vec Bs) (toRT0Vec Cs) ρ2 ρ3 g (toRT0Vec-map is)
                                  ∘Env
                                  extendfv-morph-vec αs (toRT0Vec As) (toRT0Vec Bs) ρ1 ρ2 f (toRT0Vec-map hs)
                                  ]
extendfv-morph-vec-homomorphism [] ρ1 ρ2 ρ3 f g [] [] [] bigtt bigtt {k} = Category.Equiv.refl (D k)
extendfv-morph-vec-homomorphism (α ∷ αs) ρ1 ρ2 ρ3 f g (A ∷ As) (B ∷ Bs) (C ∷ Cs) (h , hs) (i , is) = 
  let As0 = toRT0Vec As
      Bs0 = toRT0Vec Bs
      Cs0 = toRT0Vec Cs
      ρ1As = ρ1 [ αs :fvs= As0 ]
      ρ2Bs = ρ2 [ αs :fvs= Bs0 ]
      ρ3Cs = ρ3 [ αs :fvs= Cs0 ]
      -- 
      e2-vec-hom : EnvCat [
          extendfv-morph-vec αs As0 Cs0 ρ1 ρ3 (g ∘Env f) (toRT0Vec-map (is ∘Vec hs))
          ≈ extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toRT0Vec-map is)
            ∘Env extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toRT0Vec-map hs) ]
      e2-vec-hom = extendfv-morph-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is 
      -- 
  in GEnvHR.begin
      extendfv-morph α ρ1As ρ3Cs  
        (extendfv-morph-vec αs As0 Cs0 ρ1 ρ3 (g ∘Env f) (toRT0Vec-map (is ∘Vec hs)))
        (toRT0-map (R [ i ∘ h ] ))
    GEnvHR.≈⟨ extendfv-morph-resp α e2-vec-hom (Functor.homomorphism toD0 ) ⟩ 
      extendfv-morph α ρ1As ρ3Cs  
        (extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toRT0Vec-map is)
            ∘Env extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toRT0Vec-map hs))
        (D0 [ toRT0-map i ∘ toRT0-map h ] )
    GEnvHR.≈⟨ extendfv-morph-homomorphism α (extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toRT0Vec-map hs)) (toRT0-map h) 
                                   (extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toRT0Vec-map is)) (toRT0-map i) ⟩ 
      (extendfv-morph α ρ2Bs ρ3Cs (extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toRT0Vec-map is)) (toRT0-map i))
      ∘Env 
      (extendfv-morph α ρ1As ρ2Bs (extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toRT0Vec-map hs)) (toRT0-map h))
    GEnvHR.∎ 
    where module GEnvHR = Category.HomReasoning EnvCat 


-------------------------------------------------------
-- Environment extensinon functors 
-------------------------------------------------------


-- λ ρ F → ρ [ φ := F ])
extendEnv2 : ∀ {k} → (φ : FVar k) 
              → Functor (Product EnvCat (D k)) EnvCat
extendEnv2 φ = record
  { F₀ = λ { (ρ , F) → ρ [ φ :fv= F ] } 
  ; F₁ = λ { {ρ , F} {ρ' , G} (f , η) → extendfv-morph φ  {F} {G} ρ ρ' f η }
  ; identity = λ { {ρ , F} → extendfv-morph-identity φ ρ F }
  ; homomorphism = λ { {ρ1 , F1} {ρ2 , F2} {ρ3 , F3} {f , η} {g , δ} {Xs} → extendfv-morph-homomorphism φ f η g δ } 
  ; F-resp-≈ = λ { (f≈g , η≈δ) {j} {ψ} → extendfv-morph-resp φ f≈g η≈δ }
  }


-- -- 0-ary version of extendEnv2 that uses category C instead of [C^ 0 , C] 
-- used to define 'semantic substitution' and prove that syntactic substitution
-- interacts nicely with semantic substitution 
extendEnv-α : ∀ (α : FVar 0) → Functor (Product EnvCat R) EnvCat
extendEnv-α α = extendEnv2 α ∘F (idF ⁂  toD0) 



-- inline definition for faster type-checking of TEnv, etc. 
-- 
-- -- it's also easier to prove that this version doesn't alter the non-functorial part of environment 
-- 
-- -- previously called extendEnv-ρ×As-inline 
extendEnv-ρ×As : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product EnvCat (R^ k)) EnvCat
extendEnv-ρ×As αs = record
  { F₀ = λ { (ρ , As) → ρ [ αs :fvs= toRT0Vec As ] } 
  ; F₁ = λ { {ρ , As} {ρ' , Bs} (f , gs) → extendfv-morph-vec αs (toRT0Vec As) (toRT0Vec Bs) ρ ρ' f (toRT0Vec-map gs) }
  ; identity = λ { {ρ , As} {j} {φ} → extendfv-morph-vec-identity αs ρ As {j} {φ} }
  ; homomorphism = λ { {ρ1 , As} {ρ2 , Bs} {ρ3 , Cs} {f , hs} {g , is} → extendfv-morph-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is }
  ; F-resp-≈ = λ { {ρ , As} {ρ' , Bs} {f , hs} {g , ks} (f≈g , hs≈ks) → extendfv-morph-vec-resp αs ρ ρ' f g As Bs hs ks f≈g hs≈ks }
  } 



extendEnv-ρ×As-noinline : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product EnvCat (R^ k)) EnvCat
extendEnv-ρ×As-noinline [] = πˡ 
extendEnv-ρ×As-noinline {suc k} (α ∷ αs) = 
    let r : Functor (Product EnvCat (C^ k)) EnvCat
        r = extendEnv-ρ×As-noinline αs 
        -- 
        extend-α : Functor (Product EnvCat D0) EnvCat
        extend-α = extendEnv2 α
        -- change [C^0 , C] to C in extend-α
        extend-α-C : Functor (Product EnvCat R) EnvCat
        extend-α-C = extendEnv2 α ∘F (idF ⁂ toD0 ) -- C→0Functors)
        -- 
        decswap : Functor (R^ (suc k)) (Product (R^ k) R)
        decswap = Swap ∘F C^decompose k 
        -- 
        decompose : Functor (Product EnvCat (R^ (suc k))) (Product (Product EnvCat (R^ k)) R)
        decompose = assocʳ EnvCat (R^ k) R ∘F (idF ⁂ decswap)
        -- 
        extend-αs : Functor (Product EnvCat (R^ (suc k))) (Product EnvCat R)
        extend-αs = (r ⁂ idF) ∘F decompose 

        in extend-α-C ∘F extend-αs 



module test-extend where
    postulate
        A B E : R.Obj
        a b d : FVar 0 
        env : Env 

    test-extend : Vec (FVar 0) 3 → Env → Env
    test-extend αs ρ = Functor.F₀ (extendEnv-ρ×As-noinline αs) (ρ , (A  ∷ B ∷ (E ∷ [])))  

    test-extend-test : Env
    test-extend-test = test-extend (a ∷ b ∷ (d ∷ [])) env  


-- used to define semantic analogue of second order subst 
-- 
-- sends ρ to ρ [ αs := _ ] 
extendEnv-αs-curry : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor EnvCat (Functors (R^ k) EnvCat)
extendEnv-αs-curry αs = curry.F₀ (extendEnv-ρ×As αs)

-- need this to define semantics of natural transformations 
extendEnv-αs : ∀ {k} → (αs : Vec (FVar 0) k) → Env
                → Functor (R^ k) EnvCat
extendEnv-αs αs ρ = Functor.F₀ (curry.F₀ (extendEnv-ρ×As αs)) ρ 

extendTEnv2 : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
            → Functor (Product (Product EnvCat (D k)) (R^ k)) EnvCat
-- extendTEnv2 φ αs = (extendEnv-ρ×As αs) ∘F ((extendEnv2 φ ∘F πˡ) ※ πʳ)

-- could also define extendTEnv2 as 
extendTEnv2 φ αs = (extendEnv-ρ×As αs) ∘F (extendEnv2 φ ⁂ idF)




-- extendEnv-ρ×As : ∀ {k} → (αs : Vec (FVar 0) k) 
--                 → Functor (Product EnvCat (R^ k)) EnvCat
{-

WTS

π₁Env ∘F extendTEnv2
=
π₁Env ∘F ((extendEnv-ρ×As αs) ∘F ((extendEnv2 φ ∘F πˡ) ※ πʳ))

=
?? 

-}



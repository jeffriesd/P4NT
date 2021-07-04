module SetEnvironments-preRT.EnvironmentExtension where 


-- import core 
open import SetEnvironments-preRT.Core


open import Categories.Category using (Category)
-- open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)

open import Categories.Category.Product using (Product ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_ ; assocʳ)
open import Categories.Category.Construction.Functors using (Functors; module curry ; evalF)
open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)

open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec ; _∷_ ; []) renaming (map to vmap)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
import Relation.Binary.PropositionalEquality as ≡ 
open import Relation.Binary.PropositionalEquality using (_≡_)
open ≡.≡-Reasoning


open import SetCats
  using
  (Sets ; Sets^ ; [Sets^_,Sets] ; VecMorph
  ; to0Functors ; toConstNats ; ConstF ; ConstNat
  ; makeIdTuple ; _∘SetVec_ ; Sets→0Functors ; Sets^decompose)
open import Syntax.NestedTypeSyntax using (Id ; TCCtx ; FunCtx ; TCVar ; FVar ; TypeExpr ; _,++_ ; _,,_ ; _^T_ ; _^F_ ; eqNat ; _≟_ )
open import Utils


-------------------------------------------------------
-- extend morphisms of environments 
-------------------------------------------------------

-- TODO maybe rename this to identity-rho or something? 
-- 
-- this gives rise to a functor extendSetEnv : [Sets^k ,Sets] → SetEnvCat
-- λ F → ρ [ φ :fv= F ]
extendmorph-η : ∀ {k} 
                {F G : Functor (Sets^ k) Sets} 
              → (ρ : SetEnv)
              → (φ : FVar k)
              → NaturalTransformation F G 
              → SetEnvMorph (ρ [ (φ ∷ []) :fvs= (F ∷ []) ])
                            (ρ [ (φ ∷ []) :fvs= (G ∷ []) ])
extendmorph-η {k} {F} {G} record { tc = tc ; fv = fv } (φ ^F k) η = record { eqTC = ≡.refl ; fv = λ ψ → mapfv ψ }
  where mapfv : ∀ {j} (ψ : FVar j) 
          → NaturalTransformation (SetEnv.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ) 
                                  (SetEnv.fv (record { tc = tc ; fv = fv } [ φ ^F k ∷ Vec.[] :fvs= G ∷ Vec.[] ]) ψ)
        mapfv (ψ ^F j) with eqNat k j | φ ≟ ψ 
        ... | yes ≡.refl | yes ≡.refl = η 
        ... | no _ | _ = idnat -- (fv (ψ ^F j))
        ... | yes ≡.refl | no _ = idnat -- (fv (ψ ^F j)) 

-- this gives rise to a functor extendSetEnvF : SetEnvCat → SetEnvCat  
-- λ ρ → ρ [ φ :fv= F ]
extendmorph-idF : ∀  {k} (φ : FVar k) (F : Functor (Sets^ k) Sets)
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → SetEnvMorph (ρ  [ φ :fv= F ]) 
                            (ρ' [ φ :fv= F ]) 
extendmorph-idF {k} (φ ^F k) F ρ ρ' f = record { eqTC = SetEnvMorph.eqTC f ; fv = fvmap } 
          where fvmap : ∀ {j} (ψ : FVar j) 
                  → NaturalTransformation (SetEnv.fv (ρ  [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                                          (SetEnv.fv (ρ' [ φ ^F k ∷ Vec.[] :fvs= F ∷ Vec.[] ]) ψ)
                fvmap (ψ ^F j) with eqNat k j | φ ≟ ψ 
                ... | yes ≡.refl | yes ≡.refl = idnat -- mkIdNatTr' F
                ... | no _ | _ = SetEnvMorph.fv f (ψ ^F j)
                ... | yes ≡.refl | no _ = SetEnvMorph.fv f (ψ ^F j)



extendfv-morph : ∀ {k} (φ : FVar k)
                {F G : Functor (Sets^ k) Sets} 
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → NaturalTransformation F G 
              → SetEnvMorph (ρ  [ φ :fv= F ])
                            (ρ' [ φ :fv= G ])
extendfv-morph (φ ^F k) {F} {G} ρ ρ' f η = record { eqTC = (SetEnvMorph.eqTC f) ; fv = fvmap } 
    where fvmap : ∀ {j} (ψ : FVar j)
                  → NaturalTransformation (SetEnv.fv (ρ  [ (φ ^F k) :fv= F ]) ψ)
                                          (SetEnv.fv (ρ' [ (φ ^F k) :fv= G ]) ψ)
          fvmap (ψ ^F j) with eqNat k j | φ ≟ ψ 
          ... | yes ≡.refl | yes ≡.refl = η 
          ... | no _ | _ = SetEnvMorph.fv f (ψ ^F j)
          ... | yes ≡.refl | no _ = SetEnvMorph.fv f (ψ ^F j)

--------------------------------
-- Functor laws for extendSetEnv2
extendfv-morph-identity : ∀ {k} (φ : FVar k) ρ
                        → (F : Category.Obj [Sets^ k ,Sets]) 
                        → ∀ {j : ℕ} {ψ : FVar j} 
                        → ([Sets^ j ,Sets] Category.≈
                         SetEnvMorph.fv
                         (extendfv-morph φ {F} {F} ρ ρ (Category.id SetEnvCat) (Category.id [Sets^ k ,Sets]))
                         ψ)
                        (SetEnvMorph.fv (Category.id SetEnvCat {ρ [ φ :fv= F ]}) ψ)
extendfv-morph-identity (φ ^F k) ρ F {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl 
... | yes ≡.refl | no _ = ≡.refl 
... | no _ | _ = ≡.refl 

extendfv-morph-homomorphism : ∀ {k} (φ : FVar k) {F1 F2 F3 : Category.Obj [Sets^ k ,Sets]} 
                              {ρ1 ρ2 ρ3 : SetEnv}
                              → (f : SetEnvMorph ρ1 ρ2) (η : NaturalTransformation F1 F2)
                              → (g : SetEnvMorph ρ2 ρ3) (δ : NaturalTransformation F2 F3)
                              → ∀ {j : ℕ} {ψ : FVar j} 
                              → {Xs : Vec Set j}
                              {x : Functor.F₀ (SetEnv.fv (ρ1 [ φ :fv= F1 ]) ψ) Xs} →
                            NaturalTransformation.η
                            (SetEnvMorph.fv
                              (extendfv-morph φ {F1} {F3} ρ1 ρ3 (g ∘SetEnv f) (δ ∘v η))
                             ψ)
                            Xs x
                            ≡
                            NaturalTransformation.η
                            (SetEnvMorph.fv 
                              ((extendfv-morph φ {F2} {F3} ρ2 ρ3 g δ)
                              ∘SetEnv (extendfv-morph φ {F1} {F2} ρ1 ρ2 f η))
                             ψ)
                            Xs x
extendfv-morph-homomorphism (φ ^F k) f η g δ {j} {ψ ^F j}  with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | yes ≡.refl | no _ = ≡.refl
... | no _ | _ = ≡.refl

extendfv-morph-resp : ∀ {k} (φ : FVar k) {ρ ρ' : SetEnv} 
                      {f g : SetEnvMorph ρ ρ'}
                      {F G : Functor (Sets^ k) Sets}
                      {η δ : NaturalTransformation F G}
                      (f≈g : (SetEnvCat Category.≈ f) g)
                      (η≈δ : ([Sets^ k ,Sets] Category.≈ η) δ) 
                      → ∀ {j : ℕ} {ψ : FVar j} 
                      → ([Sets^ j ,Sets] Category.≈
                        SetEnvMorph.fv (extendfv-morph φ {F} {G} ρ ρ' f η) ψ)
                        (SetEnvMorph.fv (extendfv-morph φ  {F} {G} ρ ρ' g δ) ψ)
extendfv-morph-resp (φ ^F k) f≈g η≈δ {j} {ψ ^F j} {Xs} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = η≈δ 
... | yes ≡.refl | no _ = f≈g 
... | no _ | _ = f≈g 





-- f [ φs :fvs= ηs ]
-- 
-- -- how does this decompose ? 
-- can we prove that 
--  f [ φs :fvs= ηs ] [ φ :fvs= η ]
-- ≈ f [ φs :fvs= ηs ] [ φ :fvs= η ]
extendfv-morph-vec : ∀ {k n } (φs : Vec (FVar k) n)
                (Fs Gs : Vec (Functor (Sets^ k) Sets) n)
              → (ρ ρ' : SetEnv)
              → SetEnvMorph ρ ρ'
              → foreach2 (NaturalTransformation) Fs Gs
              → SetEnvMorph (ρ  [ φs :fvs= Fs ])
                            (ρ' [ φs :fvs= Gs ])
extendfv-morph-vec {k} {zero} [] [] [] ρ ρ' f bigtt = f
extendfv-morph-vec {k} {suc n} (φ ∷ φs) (F ∷ Fs) (G ∷ Gs) ρ ρ' f (η , ηs) = 
      record { eqTC = SetEnvMorph.eqTC f 
             ; fv = SetEnvMorph.fv 
                        (extendfv-morph {k} φ (ρ [ φs :fvs= Fs ]) (ρ' [ φs :fvs= Gs ]) 
                            (extendfv-morph-vec {k} {n} φs Fs Gs ρ ρ' f ηs) η) }



-- a kind of natural condition
-- that says a morphism of environments
-- f [ φ := η ]
-- can be decomposed into
-- f [ φ := id_F ] ∘SetEnv id_ρ [ φ := η ] 
extendfv-morph-nat : ∀ {k} (φ : FVar k)
                {F G : Functor (Sets^ k) Sets} 
              → (ρ ρ' : SetEnv)
              → (f : SetEnvMorph ρ ρ')
              → (η : NaturalTransformation F G)
              → SetEnvCat Categories.Category.[
              extendfv-morph φ {F = G} {G = G} ρ ρ' f idnat 
              ∘SetEnv extendfv-morph φ ρ ρ idSetEnv η 
              ≈
              extendfv-morph φ ρ ρ' f η 
              ]
extendfv-morph-nat {k} (φ ^F k) {F} {G} ρ ρ' f η {j} {ψ ^F j} {Xs} {x} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | no _ | _ = ≡.refl
... | yes ≡.refl | no _ = ≡.refl



-- a kind of naturality condition
-- f [ φs := id_Fs ] ∘SetEnv id_ρ [ φs := ηs ]
-- ≈ f [ φs := ηs ]
extendfv-morph-vec-nat : ∀ {k n } (φs : Vec (FVar k) n)
                   → (Fs Gs : Vec (Functor (Sets^ k) Sets) n)
                   → (ρ ρ' : SetEnv)
                   → (f : SetEnvMorph ρ ρ')
                   → (ηs : foreach2 (NaturalTransformation) Fs Gs)
                   → SetEnvCat Categories.Category.[
                     extendfv-morph-vec φs Gs Gs ρ ρ' f (make-foreach2-homg {As = Gs} idnat)
                     ∘SetEnv
                     extendfv-morph-vec φs Fs Gs ρ ρ idSetEnv ηs
                     ≈ 
                     extendfv-morph-vec φs Fs Gs ρ ρ' f ηs 
                     ]
extendfv-morph-vec-nat [] [] [] ρ ρ' f bigtt = ≡.refl
extendfv-morph-vec-nat ((φ ^F k) ∷ φs) (F ∷ Fs) (G ∷ Gs) ρ ρ' f (η , ηs) {j} {ψ ^F j} {Zs} {x} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | no _       | _    = extendfv-morph-vec-nat φs Fs Gs ρ ρ' f ηs 
... | yes ≡.refl | no _ = extendfv-morph-vec-nat φs Fs Gs ρ ρ' f ηs 


-- specifically for 0-ary variables 
extendfv-morph-vec-nat-αs : ∀ {n} (φs : Vec (FVar 0) n)
                   → (Xs Ys : Vec Set n)
                   → (ρ ρ' : SetEnv)
                   → (f : SetEnvMorph ρ ρ')
                   → (gs : VecMorph Xs Ys)
                   → SetEnvCat Categories.Category.[
                     extendfv-morph-vec φs (to0Functors Ys) (to0Functors Ys) ρ ρ' f (toConstNats (makeIdTuple Ys)) 
                     ∘SetEnv
                     extendfv-morph-vec φs (to0Functors Xs) (to0Functors Ys) ρ ρ idSetEnv (toConstNats gs)
                     ≈ 
                     extendfv-morph-vec φs (to0Functors Xs) (to0Functors Ys) ρ ρ' f (toConstNats gs)
                     ]
extendfv-morph-vec-nat-αs [] [] [] ρ ρ' f bigtt = ≡.refl
extendfv-morph-vec-nat-αs ((φ ^F k) ∷ φs) (X ∷ Xs) (Y ∷ Ys) ρ ρ' f (g , gs) {j} {ψ ^F j} {Zs} {x} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | no _       | _    = extendfv-morph-vec-nat-αs φs Xs Ys ρ ρ' f gs
... | yes ≡.refl | no _ = extendfv-morph-vec-nat-αs φs Xs Ys ρ ρ' f gs 

-- other direction commutes as well 
extendfv-morph-vec-nat-αs-sym : ∀ {n} (φs : Vec (FVar 0) n)
                   → (Xs Ys : Vec Set n)
                   → (ρ ρ' : SetEnv)
                   → (f : SetEnvMorph ρ ρ')
                   → (gs : VecMorph Xs Ys)
                   → SetEnvCat Categories.Category.[
                     extendfv-morph-vec φs (to0Functors Xs) (to0Functors Ys) ρ' ρ' idSetEnv (toConstNats gs)
                     ∘SetEnv
                     extendfv-morph-vec φs (to0Functors Xs) (to0Functors Xs) ρ ρ' f (toConstNats (makeIdTuple Xs)) 
                     ≈ 
                     extendfv-morph-vec φs (to0Functors Xs) (to0Functors Ys) ρ ρ' f (toConstNats gs)
                     ]
extendfv-morph-vec-nat-αs-sym [] [] [] ρ ρ' f bigtt = ≡.refl
extendfv-morph-vec-nat-αs-sym ((φ ^F k) ∷ φs) (X ∷ Xs) (Y ∷ Ys) ρ ρ' f (g , gs) {j} {ψ ^F j} {Zs} {x} with eqNat k j | φ ≟ ψ 
... | yes ≡.refl | yes ≡.refl = ≡.refl
... | no _       | _    = extendfv-morph-vec-nat-αs-sym φs Xs Ys ρ ρ' f gs
... | yes ≡.refl | no _ = extendfv-morph-vec-nat-αs-sym φs Xs Ys ρ ρ' f gs 



extendfv-morph-vec-identity : ∀ {k} (αs : Vec (FVar 0) k) ρ
                              (As : Vec Set k)
                              → SetEnvCat Categories.Category.[ 
                                  extendfv-morph-vec αs (to0Functors As) (to0Functors As) ρ ρ (Category.id SetEnvCat) (toConstNats (Category.id (Sets^ k)))
                                ≈ Category.id SetEnvCat {ρ [ αs :fvs= to0Functors As ]} ] 
extendfv-morph-vec-identity {.0} [] ρ [] = ≡.refl 
-- extendfv-morph-vec-identity {.0} {[]} ρ [] {j} {φ} {Xs} {x} = ≡.refl
extendfv-morph-vec-identity {suc k} (α ∷ αs) ρ (A ∷ As) = 
  let id0 = Category.id [Sets^ 0 ,Sets]
      idAs = Category.id (Sets^ k)
      ρAs = ρ [ αs :fvs= vmap ConstF As ]
      -- 
      e2id : SetEnvCat Categories.Category.[
            extendfv-morph α ρAs ρAs idSetEnv id0
            ≈ Category.id SetEnvCat ]
      e2id = extendfv-morph-identity (α ) ρAs (ConstF A) 
      -- 
      e2vec-id : SetEnvCat Categories.Category.[
            extendfv-morph-vec αs (to0Functors As) (to0Functors As) ρ ρ idSetEnv (toConstNats idAs)
            ≈ Category.id SetEnvCat ]
      e2vec-id = extendfv-morph-vec-identity αs ρ As 

    in begin≈
      extendfv-morph {0} α ρAs ρAs (extendfv-morph-vec αs (to0Functors As) (to0Functors As) ρ ρ (idSetEnv {ρ}) (toConstNats (makeIdTuple As))) (ConstNat (idf {A = A}))
    ≈⟨ extendfv-morph-resp α e2vec-id ≡.refl ⟩
    extendfv-morph α ρAs ρAs (idSetEnv {ρAs}) (id0 {ConstF A})
    ≈⟨ e2id ⟩ 
      idSetEnv 
    ≈∎
    where module SEC = Category SetEnvCat
          open SEC.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)




extendfv-morph-vec-resp : ∀ {k} (αs : Vec (FVar 0) k) (ρ ρ' : SetEnv)
                          (f g : SetEnvMorph ρ ρ')
                          (As Bs : Vec Set k)
                          (hs is : VecMorph As Bs)
                          (f≈g : (SetEnvCat Category.≈ f) g)
                          (hs≈is : (Sets^ k Category.≈ hs) is) 
                          → SetEnvCat Categories.Category.[
                            extendfv-morph-vec {0} {k} αs (to0Functors As) (to0Functors Bs) ρ ρ' f (toConstNats hs)
                            ≈ extendfv-morph-vec {0} {k} αs (to0Functors As) (to0Functors Bs) ρ ρ' g (toConstNats is)
                          ] 
                          
extendfv-morph-vec-resp {0} [] ρ ρ' f g [] [] bigtt bigtt f≈g bigtt {j} {φ} {Xs} {x} = f≈g
extendfv-morph-vec-resp {suc k} (α ∷ αs) ρ ρ' f g (A ∷ As) (B ∷ Bs) (h , hs) (i , is) f≈g (h≈i , hs≈is) = 
  let ρAs = ρ [ αs :fvs= vmap ConstF As ]
      ρ'Bs = ρ' [ αs :fvs= vmap ConstF Bs ]
      As0 = to0Functors As
      Bs0 = to0Functors Bs
      -- 
      e2-vec-f-hs≈e2-vec-g-is  : SetEnvCat Categories.Category.[
              extendfv-morph-vec αs As0 Bs0 ρ ρ' f (toConstNats hs)
              ≈ extendfv-morph-vec αs As0 Bs0 ρ ρ' g (toConstNats is) ]
      e2-vec-f-hs≈e2-vec-g-is = extendfv-morph-vec-resp αs ρ ρ' f g As Bs hs is f≈g hs≈is
      --
    in begin≈
      extendfv-morph α ρAs ρ'Bs (extendfv-morph-vec αs As0 Bs0 ρ ρ' f (toConstNats hs)) (ConstNat h)
    ≈⟨ extendfv-morph-resp α e2-vec-f-hs≈e2-vec-g-is h≈i ⟩
      extendfv-morph α ρAs ρ'Bs (extendfv-morph-vec αs As0 Bs0 ρ ρ' g (toConstNats is)) (ConstNat i)
    ≈∎ 
    where module SEC = Category SetEnvCat
          open SEC.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)

extendfv-morph-vec-homomorphism : ∀ {k} (αs : Vec (FVar 0) k) (ρ1 ρ2 ρ3 : SetEnv)
                                  (f : SetEnvMorph ρ1 ρ2) (g : SetEnvMorph ρ2 ρ3) 
                                  (As Bs Cs : Vec Set k)
                                  (hs : VecMorph As Bs)
                                  (is : VecMorph Bs Cs)
                                  → SetEnvCat Categories.Category.[ 
                                  extendfv-morph-vec αs (to0Functors As) (to0Functors Cs) ρ1 ρ3 (g ∘SetEnv f) (toConstNats (is ∘SetVec hs))
                                  ≈ 
                                  extendfv-morph-vec αs (to0Functors Bs) (to0Functors Cs) ρ2 ρ3 g (toConstNats is)
                                  ∘SetEnv
                                  extendfv-morph-vec αs (to0Functors As) (to0Functors Bs) ρ1 ρ2 f (toConstNats hs)
                                  ]
extendfv-morph-vec-homomorphism [] ρ1 ρ2 ρ3 f g [] [] [] bigtt bigtt = ≡.refl
extendfv-morph-vec-homomorphism (α ∷ αs) ρ1 ρ2 ρ3 f g (A ∷ As) (B ∷ Bs) (C ∷ Cs) (h , hs) (i , is) = 
  let As0 = to0Functors As
      Bs0 = to0Functors Bs
      Cs0 = to0Functors Cs
      ρ1As = ρ1 [ αs :fvs= As0 ]
      ρ2Bs = ρ2 [ αs :fvs= Bs0 ]
      ρ3Cs = ρ3 [ αs :fvs= Cs0 ]
      -- 
      e2-vec-hom : SetEnvCat Categories.Category.[
          extendfv-morph-vec αs As0 Cs0 ρ1 ρ3 (g ∘SetEnv f) (toConstNats (is ∘SetVec hs))
          ≈ extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)
            ∘SetEnv extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs) ]
      e2-vec-hom = extendfv-morph-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is 
      -- 
  in begin≈
      extendfv-morph α ρ1As ρ3Cs  
        (extendfv-morph-vec αs As0 Cs0 ρ1 ρ3 (g ∘SetEnv f) (toConstNats (is ∘SetVec hs)))
        (ConstNat (i ∘' h))
    ≈⟨ extendfv-morph-resp α e2-vec-hom ≡.refl ⟩ 
      extendfv-morph α ρ1As ρ3Cs  
        (extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)
            ∘SetEnv extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs))
        (ConstNat i ∘v ConstNat h)
    ≈⟨ extendfv-morph-homomorphism α (extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs)) (ConstNat h) 
                                   (extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)) (ConstNat i) ⟩ 
      (extendfv-morph α ρ2Bs ρ3Cs (extendfv-morph-vec αs Bs0 Cs0 ρ2 ρ3 g (toConstNats is)) (ConstNat i))
      ∘SetEnv 
      (extendfv-morph α ρ1As ρ2Bs (extendfv-morph-vec αs As0 Bs0 ρ1 ρ2 f (toConstNats hs)) (ConstNat h))
    ≈∎ 
    where module SEC = Category SetEnvCat
          open SEC.HomReasoning renaming (begin_ to begin≈_ ; _∎ to _≈∎)




-------------------------------------------------------
-- Environment extensinon functors 
-------------------------------------------------------


-- λ ρ F → ρ [ φ := F ])
extendSetEnv2 : ∀ {k} → (φ : FVar k) 
              → Functor (Product SetEnvCat [Sets^ k ,Sets]) SetEnvCat
extendSetEnv2 φ = record
  { F₀ = λ { (ρ , F) → ρ [ φ :fv= F ] } 
  ; F₁ = λ { {ρ , F} {ρ' , G} (f , η) → extendfv-morph φ  {F} {G} ρ ρ' f η }
  ; identity = λ { {ρ , F} → extendfv-morph-identity φ ρ F }
  ; homomorphism = λ { {ρ1 , F1} {ρ2 , F2} {ρ3 , F3} {f , η} {g , δ} {Xs} → extendfv-morph-homomorphism φ f η g δ } 
  ; F-resp-≈ = λ { (f≈g , η≈δ) {j} {ψ} → extendfv-morph-resp φ f≈g η≈δ }
  }


-- -- 0-ary version of extendSetEnv2 that uses category Sets instead of [Sets^ 0 , Sets] 
-- used to define 'semantic substitution' and prove that syntactic substitution
-- interacts nicely with semantic substitution 
extendSetEnv-α : ∀ (α : FVar 0) 
                → Functor (Product SetEnvCat Sets) SetEnvCat
extendSetEnv-α α = extendSetEnv2 α ∘F (idF ⁂ Sets→0Functors) 



-- inline definition for faster type-checking of TEnv, etc. 
-- 
-- -- it's also easier to prove that this version doesn't alter the non-functorial part of environment 
-- 
-- -- previously called extendSetEnv-ρ×As-inline 
extendSetEnv-ρ×As : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
extendSetEnv-ρ×As αs = record
  { F₀ = λ { (ρ , As) → ρ [ αs :fvs= to0Functors As ] } 
  ; F₁ = λ { {ρ , As} {ρ' , Bs} (f , gs) → extendfv-morph-vec αs (to0Functors As) (to0Functors Bs) ρ ρ' f (toConstNats gs) }
  ; identity = λ { {ρ , As} {j} {φ} {Xs} {x} → extendfv-morph-vec-identity αs ρ As {j} {φ} {Xs} {x} }
  ; homomorphism = λ { {ρ1 , As} {ρ2 , Bs} {ρ3 , Cs} {f , hs} {g , is} → extendfv-morph-vec-homomorphism αs ρ1 ρ2 ρ3 f g As Bs Cs hs is }
  ; F-resp-≈ = λ { {ρ , As} {ρ' , Bs} {f , hs} {g , ks} (f≈g , hs≈ks) → extendfv-morph-vec-resp αs ρ ρ' f g As Bs hs ks f≈g hs≈ks }
  } 



extendSetEnv-ρ×As-noinline : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
extendSetEnv-ρ×As-noinline [] = πˡ 
extendSetEnv-ρ×As-noinline {suc k} (α ∷ αs) = 
    let r : Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
        r = extendSetEnv-ρ×As-noinline αs 
        -- 
        extend-α : Functor (Product SetEnvCat [Sets^ 0 ,Sets]) SetEnvCat
        extend-α = extendSetEnv2 α
        -- change [Sets^0 , Sets] to Sets in extend-α
        extend-α-Sets : Functor (Product SetEnvCat Sets) SetEnvCat
        extend-α-Sets = extendSetEnv2 α ∘F (idF ⁂ Sets→0Functors)
        -- 
        decswap : Functor (Sets^ (suc k)) (Product (Sets^ k) Sets)
        decswap = Swap ∘F Sets^decompose k
        -- 
        decompose : Functor (Product SetEnvCat (Sets^ (suc k))) (Product (Product SetEnvCat (Sets^ k)) Sets)
        decompose = assocʳ SetEnvCat (Sets^ k) Sets ∘F (idF ⁂ decswap)
        -- 
        extend-αs : Functor (Product SetEnvCat (Sets^ (suc k))) (Product SetEnvCat Sets)
        extend-αs = (r ⁂ idF) ∘F decompose 

        in extend-α-Sets ∘F extend-αs 


module test-extend where
    postulate
        A B C : Set 
        a b c : FVar 0 
        env : SetEnv 

    test-extend : Vec (FVar 0) 3 → SetEnv → SetEnv
    test-extend αs ρ = Functor.F₀ (extendSetEnv-ρ×As-noinline αs) (ρ , (A  ∷ B ∷ (C ∷ [])))  

    test-extend-test : SetEnv
    test-extend-test = test-extend (a ∷ b ∷ (c ∷ [])) env  


-- extendSetEnv-As×ρ : ∀ {k} → (αs : Vec (FVar 0) k) 
--                 → Functor (Product (Sets^ k) SetEnvCat) SetEnvCat
-- extendSetEnv-As×ρ αs = extendSetEnv-ρ×As αs ∘F Swap


-- used to define semantic analogue of second order subst 
-- 
-- sends ρ to ρ [ αs := _ ] 
extendSetEnv-αs-curry : ∀ {k} → (αs : Vec (FVar 0) k) 
                → Functor SetEnvCat (Functors (Sets^ k) SetEnvCat)
extendSetEnv-αs-curry αs = curry.F₀ (extendSetEnv-ρ×As αs)


-- need this to define semantics of natural transformations 
extendSetEnv-αs : ∀ {k} → (αs : Vec (FVar 0) k) → SetEnv
                → Functor (Sets^ k) SetEnvCat
extendSetEnv-αs αs ρ = Functor.F₀ (curry.F₀ (extendSetEnv-ρ×As αs)) ρ 




extendTEnv2 : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
            → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) SetEnvCat
extendTEnv2 φ αs = (extendSetEnv-ρ×As αs) ∘F ((extendSetEnv2 φ ∘F πˡ) ※ πʳ)




{-
-- no longer used 
module extendSetEnv-ρ×As-noinline where 

  -- environment extension functor used to define extendTEnv used in TEnv. 
  -- this version is defined recursively on αs in terms of other environment extension functors 
  -- and functor combinators. this means it is a bit harder to see that this functor doesn't 
  -- alter the tc part of environment, which is useful for some proofs 
  -- 
  -- so instead, we use an equivalent functor extendSetEnv-ρ×As whose action on objects, etc. is given directly 

  -- λ ρ As → ρ [ αs := As ]
  -- 
  -- we can define this inductively in terms of extendSetEnv2 and functor operations 
  extendSetEnv-ρ×As-noinline : ∀ {k} → (αs : Vec (FVar 0) k) 
                  → Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
  extendSetEnv-ρ×As-noinline [] = πˡ 
  extendSetEnv-ρ×As-noinline {suc k} (α ∷ αs) = 
        let r : Functor (Product SetEnvCat (Sets^ k)) SetEnvCat
            r = extendSetEnv-ρ×As-noinline αs 
            -- 
            extend-α : Functor (Product SetEnvCat [Sets^ 0 ,Sets]) SetEnvCat
            extend-α = extendSetEnv2 α
            -- change [Sets^0 , Sets] to Sets in extend-α
            extend-α-Sets : Functor (Product SetEnvCat Sets) SetEnvCat
            extend-α-Sets = extendSetEnv2 α ∘F (idF ⁂ Sets→0Functors)
            -- 
            decswap : Functor (Sets^ (suc k)) (Product (Sets^ k) Sets)
            decswap = Swap ∘F Sets^decompose k
            -- 
            decompose : Functor (Product SetEnvCat (Sets^ (suc k))) (Product (Product SetEnvCat (Sets^ k)) Sets)
            decompose = assocʳ SetEnvCat (Sets^ k) Sets ∘F (idF ⁂ decswap)
            -- 
            extend-αs : Functor (Product SetEnvCat (Sets^ (suc k))) (Product SetEnvCat Sets)
            extend-αs = (r ⁂ idF) ∘F decompose 

          in extend-α-Sets ∘F extend-αs 


  -- uses non-inlined version of (extendSetEnv-ρ×As αs)
  extendTEnv : ∀ {k} → (φ : FVar k) → (αs : Vec (FVar 0) k) 
              → Functor (Product (Product SetEnvCat [Sets^ k ,Sets]) (Sets^ k)) SetEnvCat
  extendTEnv φ αs = (extendSetEnv-ρ×As-noinline αs) ∘F (extendSetEnv2 φ ∘F πˡ ※ πʳ) 


  -- testextend : ∀ {k} → (αs : Vec (FVar 0) k) → SetEnv → Vec Set k → SetEnv
  -- testextend αs ρ As = Functor.F₀ (extendSetEnv-ρ×As αs) (ρ , As) 

  -- testextend2 : (αs : Vec (FVar 0) 3) → SetEnv → Vec Set 3 → SetEnv
  -- testextend2 (a1 ∷ a2 ∷ a3 ∷ Vec.[]) ρ (A1 ∷ A2 ∷ A3 ∷ Vec.[]) = {!  ρ [ (a1 ∷ a2 ∷ a3 ∷ Vec.[]) :fvs= (ConstF A1 ∷ ConstF A2 ∷ ConstF A3 ∷ Vec.[]) ]  !} 

  -- testextend (a1 ∷ a2 ∷ a3 ∷ Vec.[]) ρ (A1 ∷ A2 ∷ A3 ∷ Vec.[])
  -- gives 
  -- ((ρ [ a3 :fv= ConstF A3 ]) [ a2 :fv= ConstF A2 ]) [ a1 :fv= ConstF A1 ]
  -- 
  -- which corresponds to the recursive definition of :fvs= 

  -- extendfv-morph-vec : ∀ {k} {αs : Vec (FVar 0) k} (ρ ρ' : SetEnv) (f : SetEnvMorph ρ ρ')                    
  --                       (As Bs : Vec Set k) (gs : VecMorph As Bs) 
  --                      → SetEnvMorph (ρ  [ αs :fvs= to0Functors As ])
  --                                    (ρ' [ αs :fvs= to0Functors Bs ])
  -- extendfv-morph-vec : ∀ {k} {αs : Vec (FVar 0) k} (ρ ρ' : SetEnv) (f : SetEnvMorph ρ ρ')                    
-}





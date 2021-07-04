

open import Relation.Binary.HeterogeneousEquality using (_≅_)
import Relation.Binary.HeterogeneousEquality as Het 
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as ≡
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)

open import Categories.Functor using (Functor ; _∘F_)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category 

open import Function renaming (id to idf; _∘_ to _∘'_)
open import SetCats 
open import Data.Vec using (Vec)
open Vec 
open import Agda.Builtin.Unit
open import Data.Product renaming (_×_ to _×'_)
open import Utils 


open import Level 

open import HetEquality.Core 

module HetEquality.HetFunctors {o l e : Level} (C : Category o l e) where 


module VecHetEquality where 
    -- two morphisms of vectors are het-equal 
    pointwise-het-≈ : ∀ {k} → {Xs Ys Zs Ws : Vec Set k} → (fs : VecMorph Xs Ys) → (gs : VecMorph Zs Ws) → Set 
    pointwise-het-≈ {zero} {[]} {[]} {[]} {[]} _ _  = big⊤
    pointwise-het-≈ {suc _ } {X ∷ Xs} {Y ∷ Ys} {Z ∷ Zs} {W ∷ Ws} (f , fs) (g , gs) = f het-≈ g  ×' pointwise-het-≈ fs gs

    pointwise-het-eq⇒pointwise-≈ : ∀ {j} {As Bs : Vec Set j} {fs gs : VecMorph As Bs} → pointwise-het-≈ fs gs → (Sets^ j) [ fs ≈ gs ]
    pointwise-het-eq⇒pointwise-≈ {zero} {[]} {[]} _ = bigtt 
    pointwise-het-eq⇒pointwise-≈ {suc j} {A ∷ As} {B ∷ Bs} {f , fs} {g , gs} (f≈g , fs≈gs) = (het-eq⇒eq f≈g) , (pointwise-het-eq⇒pointwise-≈ fs≈gs) 

    pointwise-het-id : ∀ {k} → {Xs Ys : Vec Set k} → (f : VecMorph Xs Ys) → Set 
    pointwise-het-id {zero} {[]} {[]} bigtt = big⊤
    pointwise-het-id {suc _ } {X ∷ Xs} {Y ∷ Ys} (f , fs) = (∀ {x} → f x ≅ x) ×' pointwise-het-id fs 

    pointwise-het-id⇒pointwise-≈ : ∀ {j} {As : Vec Set j} (gs : VecMorph As As) → pointwise-het-id gs → (Sets^ j) Categories.Category.[ gs ≈ Category.id (Sets^ j) ] 
    pointwise-het-id⇒pointwise-≈ {zero} {[]}  bigtt bigtt = bigtt
    pointwise-het-id⇒pointwise-≈ {suc j} {A ∷ As} (g , gs) (gx≅x , gseq) = (Het.≅-to-≡ gx≅x) , (pointwise-het-id⇒pointwise-≈  gs gseq) 

open VecHetEquality 






private module C = Category C 
-- -- in this file, we have various submodules
-- for propagating heterogeneous equalities through functors
-- and natural transformations 

-- maybe we can generalize this to any category C such that
-- f Het.≅ g implies C [ f ≈ g ] 
-- -- but usually we are interested in extensional equalities of f and g 
-- -- and how can we talk about extensional equality for morphisms in an arbitrary category? 
--
-- in Set we can use ∀ {x} {y} → x ≅ y → f x ≅ g y 
--
-- we can use a similar notion in Sets^ k 
--
-- but it isn't clear how to extend this to an arbitrary category 


-- HetNaturalIso-identity-maps produces a natural isomorphism between F and G 
-- from
-- 1) proof that F and G are equal on objects 
-- 2) proof that functorial actions of F and G always behave as identities (maybe F and G are constant functors) 
-- 
-- used in TermSemantics.NatTermSemantics.agda  
module HetNaturalIso-identity-maps (F G : Functor C Sets) 
    (eqFG : ∀ X → Functor.F₀ F X ≡ Functor.F₀ G X)
    (eqFmap : ∀ {X Y : Category.Obj C} (f : C Categories.Category.[ X , Y ]) {x} → Functor.F₁ F f x ≅ x)
    (eqGmap : ∀ {X Y : Category.Obj C} (f : C Categories.Category.[ X , Y ]) {x} → Functor.F₁ G f x ≅ x)
  where 

  private 
    module F = Functor F 
    module G = Functor G 
  open Het.≅-Reasoning

  f-η : ∀ (X : Category.Obj C) 
        → Functor.F₀ F X →  Functor.F₀ G X 
  f-η X = ≡.subst (λ x → x) (eqFG X) 

  eqnat-comp : ∀ {X : Category.Obj C} {x} → f-η X x ≅ x
  eqnat-comp {X} rewrite eqFG X = Het.refl 

  -- then we can prove naturality still 
  f-commute-het : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x}
              → f-η Y (Functor.F₁ F f x)
              ≅ Functor.F₁ G f (f-η X x)
  f-commute-het {X} {Y} f {x} = begin
      f-η Y (Functor.F₁ F f x)
    ≅⟨ eqnat-comp {Y} ⟩ 
      (Functor.F₁ F f x)
    ≅⟨ eqFmap f ⟩ 
      x 
    ≅⟨ Het.sym (eqnat-comp {X}) ⟩
      f-η X x
    ≅⟨ Het.sym (eqGmap f) ⟩
      Functor.F₁ G f (f-η X x)
    ∎ 


  F⇒G : NaturalTransformation F G 
  F⇒G = ntHelper (record { η = f-η ; commute = λ f → Het.≅-to-≡ (f-commute-het f) })


  g-η : ∀ (X : Category.Obj C) 
        → Functor.F₀ G X →  Functor.F₀ F X 
  g-η X = ≡.subst (λ x → x) (≡.sym (eqFG X))

  g-eqnat-comp : ∀ {X : Category.Obj C} {x} → g-η X x ≅ x
  g-eqnat-comp {X} rewrite (≡.sym (eqFG X)) = Het.refl 

  -- then we can prove naturality still 
  g-commute-het : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x}
              → g-η Y (Functor.F₁ G f x)
              ≅ Functor.F₁ F f (g-η X x)
  g-commute-het {X} {Y} f {x} = begin
      g-η Y (Functor.F₁ G f x)
    ≅⟨ g-eqnat-comp ⟩ 
      (Functor.F₁ G f x)
    ≅⟨ eqGmap f ⟩ 
      x 
    ≅⟨ Het.sym g-eqnat-comp ⟩ 
      g-η X x
    ≅⟨ Het.sym (eqFmap f) ⟩ 
      Functor.F₁ F f (g-η X x)
    ∎ 



  G⇒F : NaturalTransformation G F 
  G⇒F = ntHelper (record { η = g-η ; commute = λ f → Het.≅-to-≡ (g-commute-het f) })


  f-η∘g-η : ∀ {X : Category.Obj C} → ∀ {x} 
            → f-η X (g-η X x)
            ≡ x 
  f-η∘g-η {X} {x} rewrite (eqFG X) = ≡.refl 

  g-η∘f-η : ∀ {X : Category.Obj C} → ∀ {x} 
            → g-η X (f-η X x)
            ≡ x 
  g-η∘f-η {X} {x} rewrite (eqFG X) = ≡.refl 


  F≃G : NaturalIsomorphism F G 
  F≃G = record { F⇒G = F⇒G ; F⇐G = G⇒F ; iso = λ X → record { isoˡ = g-η∘f-η ; isoʳ = f-η∘g-η } } 


-- functorial actions of F and G dont have to be identities,
-- they just have to be equal to each other on equal arguments 
-- -- should be able to define identity-map version as a special case of this one 
module HetNaturality-equal-maps (F G : Functor C Sets) 
    (eqFG : ∀ X → Functor.F₀ F X ≡ Functor.F₀ G X)
    (eqmap : ∀ {X Y : Category.Obj C} (f : C Categories.Category.[ X , Y ])
             → ∀ {x} {y} → x ≅ y → Functor.F₁ F f x ≅ Functor.F₁ G f y)
  where 

  private 
    module F = Functor F 
    module G = Functor G 
  open Het.≅-Reasoning

  f-η : ∀ (X : Category.Obj C) 
        → Functor.F₀ F X →  Functor.F₀ G X 
  f-η X = ≡.subst (λ x → x) (eqFG X) 

  eqnat-comp : ∀ {X : Category.Obj C} {x} → f-η X x ≅ x
  eqnat-comp {X} rewrite eqFG X = Het.refl 


  subst-lem : ∀ {A B : Set} {x : A} → (e : A ≡ B)
              → x ≅ ≡.subst idf e x 
  subst-lem ≡.refl = _≅_.refl

  -- then we can prove naturality still 
  f-commute-het : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x}
              → f-η Y (Functor.F₁ F f x)
              ≅ Functor.F₁ G f (f-η X x)
  f-commute-het {X} {Y} f {x} = 
    let p : x ≅ (f-η X x)
        p = subst-lem (eqFG X)  
     in 
        begin
            f-η Y (Functor.F₁ F f x)
            ≅⟨ eqnat-comp {Y} ⟩ 
            (Functor.F₁ F f x)
            ≅⟨ eqmap f p ⟩ 
            Functor.F₁ G f (f-η X x)
            ∎ 


  F⇒G : NaturalTransformation F G 
  F⇒G = ntHelper (record { η = f-η ; commute = λ f → Het.≅-to-≡ (f-commute-het f) })


  g-η : ∀ (X : Category.Obj C) 
        → Functor.F₀ G X →  Functor.F₀ F X 
  g-η X = ≡.subst (λ x → x) (≡.sym (eqFG X))

  g-eqnat-comp : ∀ {X : Category.Obj C} {x} → g-η X x ≅ x
  g-eqnat-comp {X} rewrite (≡.sym (eqFG X)) = Het.refl 

  -- then we can prove naturality still 
  g-commute-het : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x}
              → g-η Y (Functor.F₁ G f x)
              ≅ Functor.F₁ F f (g-η X x)
  g-commute-het {X} {Y} f {x} = 
    begin
        g-η Y (Functor.F₁ G f x)
        ≅⟨ g-eqnat-comp ⟩ 
        (Functor.F₁ G f x)
        ≅˘⟨ eqmap f (Het.sym (subst-lem (≡.sym (eqFG X)))) ⟩ 
        Functor.F₁ F f (g-η X x)
        ∎ 



  G⇒F : NaturalTransformation G F 
  G⇒F = ntHelper (record { η = g-η ; commute = λ f → Het.≅-to-≡ (g-commute-het f) })


  f-η∘g-η : ∀ {X : Category.Obj C} → ∀ {x} 
            → f-η X (g-η X x)
            ≡ x 
  f-η∘g-η {X} {x} rewrite (eqFG X) = ≡.refl 

  g-η∘f-η : ∀ {X : Category.Obj C} → ∀ {x} 
            → g-η X (f-η X x)
            ≡ x 
  g-η∘f-η {X} {x} rewrite (eqFG X) = ≡.refl 


  F≃G : NaturalIsomorphism F G 
  F≃G = record { F⇒G = F⇒G ; F⇐G = G⇒F ; iso = λ X → record { isoˡ = g-η∘f-η ; isoʳ = f-η∘g-η } } 




-- Functor respects (in the sense of Functor.F-resp-≈) heterogeneous equality
-- of morphisms of vectors 
module HetFuncRespVec {k : ℕ} {Xs Ys Zs Ws : Vec Set k}
   (F : Functor (Sets^ k) Sets) 
   {fs : (Sets^ k) Categories.Category.[ Xs , Ys ]} {gs : (Sets^ k) Categories.Category.[ Zs , Ws ]}
   (fs≈gs : pointwise-het-≈ fs gs )
   where
   
   private module F = Functor F 
   open F 
   
   -- if we have proofs that the domain/codomain of fs and gs are equal,
   -- we can propagate the het-equality of fs ≈ gs to F fs ≈ F gs
   Fmap-resp : (e1 : Xs ≡ Zs) (e2 : Ys ≡ Ws) → F₁ fs het-≈ F₁ gs 
   Fmap-resp ≡.refl ≡.refl Het.refl = Het.≡-to-≅ (F-resp-≈ (pointwise-het-eq⇒pointwise-≈ fs≈gs))


-- two components of natural transformation on Xs, Ys with Xs ≡ Ys
-- means the two components are equal 
module HetNatResp {k : ℕ} {Xs Ys : Vec Set k}
   {F G : Functor (Sets^ k) Sets} (η : NaturalTransformation F G) 
   where
   
   Nat-resp : ∀ (e1 : Xs ≡ Ys) 
               → NaturalTransformation.η η Xs 
           het-≈ NaturalTransformation.η η Ys
   Nat-resp ≡.refl Het.refl = Het.refl

-- Functors preserve het identities 
module HetFuncIdentityVec {k : ℕ} {Xs Ys : Vec Set k}
   (F : Functor (Sets^ k) Sets) 
   (fs : (Sets^ k) Categories.Category.[ Xs , Ys ]) (fid : pointwise-het-id fs)
  where 

  private 
    idXs : VecMorph Xs Xs
    idXs = makeIdTuple Xs

  Fmap-id : (e : Xs ≡ Ys) → ∀ {x} → Functor.F₁ F fs x ≅ x
  Fmap-id ≡.refl {x} = 
    let fs≈id : (Sets^ k) Categories.Category.[ fs ≈ idXs ]
        fs≈id = pointwise-het-id⇒pointwise-≈  fs fid

        Ff≈Fid : Sets Categories.Category.[ Functor.F₁ F fs ≈ Functor.F₁ F idXs ]
        Ff≈Fid {x} = Functor.F-resp-≈ F fs≈id

        Ff≈id : Sets Categories.Category.[ Functor.F₁ F idXs ≈ idf ] 
        Ff≈id {x} = Functor.identity F 

      in Het.≡-to-≅ (≡.trans Ff≈Fid Ff≈id)



-- actually this is just a special case of
-- HetFuncIdentityVec for F = KH 
module HetFuncId-Functors {k : ℕ} {Xs Ys : Vec Set k}
   (K : Functor [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] [Sets^ k ,Sets] )
   (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
   (fs : (Sets^ k) Categories.Category.[ Xs , Ys ]) (fid : pointwise-het-id fs)
  where 
  

  private 
    idXs : VecMorph Xs Xs 
    idXs = Category.id (Sets^ k) {A = Xs}

    KH : Functor (Sets^ k) Sets
    KH = Functor.F₀ K H 

    -- action on objects in (Sets^ k)
    KH₀ : Vec Set k → Set 
    KH₀ = Functor.F₀ KH

    -- action on morphisms in (Sets^ k)
    KH₁ : ∀ {Xs Ys : Vec Set k} → (fs : VecMorph Xs Ys) → (KH₀ Xs) → (KH₀ Ys)
    KH₁ = Functor.F₁ KH

  open HetFuncIdentityVec
  -- don't need proof of (e : KH₀ Xs ≡ KH₀ Ys)
  -- as long as we have proof of Xs ≡ Ys 
  HFix-fmap-het-id : ∀ (es : Xs ≡ Ys) -- (e : KH₀ Xs ≡ KH₀ Ys)
                     → ∀ {x : KH₀ Xs} → KH₁ fs x ≅ x 
  HFix-fmap-het-id e {x} = Fmap-id KH fs fid e {x}


module HetFuncResp-Functors {k : ℕ} {Xs Ys Zs Ws : Vec Set k}
   (K : Functor [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] [Sets^ k ,Sets] )
   (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
   (fs : (Sets^ k) Categories.Category.[ Xs , Ys ])
   (gs : (Sets^ k) Categories.Category.[ Zs , Ws ])
   (fs≈gs : pointwise-het-≈ fs gs )
  where 
  
  private 
    KH : Functor (Sets^ k) Sets
    KH = Functor.F₀ K H 

    module KH = Functor KH 

  open HetFuncRespVec 

  HFix-fmap-resp : Xs ≡ Zs → Ys ≡ Ws 
                     → KH.₁ fs het-≈ KH.₁ gs 
  HFix-fmap-resp e1 e2 = Fmap-resp KH fs≈gs e1 e2 


{-
lhs2 = fixH₁-component (Functor.F₁ (TSet ⊢F) (Functor.F₁ ForgetFVSetEnv (Functor.F₁ π₁Env f)))
                    (Functor.F₀ (SetSemVec ⊢Gs) ρ'1)  

rhs2 = fixH₁-component (Functor.F₁ (TSet ⊢F) (Functor.F₁ π₁Env (Functor.F₁ ForgetFVRelEnv f)))
            (vecfst (Functor.F₀ (RelSemVec ⊢Gs) ρ'))  
            

WTS
hmap η  Xs 
≈ 
hmap η' Ys

when Xs ≡ Ys 
and η ≡ η' 

well really we WTS 

hmap (F₁ f) Xs 
≈ 
hmap (F₁ g) Ys 

when f ≡ g and Xs ≡ Ys 

-}



module HetFuncResp-HFunctors {k : ℕ} {Xs Ys : Vec Set k}
   (K : Functor [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] [Sets^ k ,Sets] )
   {ρ ρ' : C.Obj} {f g : ρ C.⇒ ρ'}
   (f≈g : f C.≈ g) 
   (T : Functor C  [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
  where 

  private 
    module T = Functor T
    module K = Functor K

  Tf≈Tg : [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] [ T.₁ f ≈ T.₁ g ] 
  Tf≈Tg = T.F-resp-≈ f≈g

  fixH₁-resp : (Xs ≡ Ys)
       → NaturalTransformation.η (K.₁ (T.₁ f)) Xs
         het-≈
         NaturalTransformation.η (K.₁ (T.₁ g)) Ys
  fixH₁-resp ≡.refl Het.refl = Het.≡-to-≅ (K.F-resp-≈ Tf≈Tg)
  

open import Categories.Category

module HRTFunctors {o' ℓ' e'} (D : Category o' ℓ' e') (F G : Functor C (Functors D Sets))
                   (eq-obj : ∀ c d → Functor.F₀ (Functor.F₀ F c) d
                                   ≡ Functor.F₀ (Functor.F₀ G c) d)
                   (eq-morph-nat : ∀ (c c' : Category.Obj C) d (f : C [ c , c' ]) →
                     NaturalTransformation.η (Functor.F₁ F f) d
                     het-≈
                     NaturalTransformation.η (Functor.F₁ G f) d)
                   (eq-morph : ∀ c (d d' : Category.Obj D) (g : D [ d , d' ]) →
                     Functor.F₁ (Functor.F₀ F c) g
                     het-≈
                     Functor.F₁ (Functor.F₀ G c) g)
                   where 

  open Het.≅-Reasoning

  private module D = Category D 

  f-η-η : ∀ c d → Functor.F₀ (Functor.F₀ F c) d → Functor.F₀ (Functor.F₀ G c) d
  f-η-η c d = ≡.subst idf (eq-obj c d)  

  f-η-η-id : ∀ c d {x} → f-η-η c d x ≅ x 
  f-η-η-id c d {x} rewrite (eq-obj c d) = Het.refl

  f-η-η-commute : ∀ {c} {d d' : Category.Obj D} (f : D [ d , d' ])
                  → ∀ {x}
                  → ((f-η-η c d') (Functor.F₁ (Functor.F₀ F c) f x))
                  ≅ ((Functor.F₁ (Functor.F₀ G c) f) ((f-η-η c d) x))
  f-η-η-commute {c} {d} {d'} f {x} = begin
                 ((f-η-η c d') (Functor.F₁ (Functor.F₀ F c) f x))
                ≅⟨ f-η-η-id c d' ⟩
                 ((Functor.F₁ (Functor.F₀ F c) f x))
                ≅⟨ eq-morph c d d' f (Het.sym (f-η-η-id c d)) ⟩
                 ((Functor.F₁ (Functor.F₀ G c) f) ((f-η-η c d) x)) ∎  

  f-η : ∀ c → NaturalTransformation (Functor.F₀ F c)  (Functor.F₀ G c)
  f-η c = ntHelper (record { η = λ d → f-η-η c d ; commute = λ f → Het.≅-to-≡ (f-η-η-commute f) })


  f-commute-het : ∀ {c c' : C.Obj} (f : C [ c , c' ])
              → ∀ {d : D.Obj} {x} 
              → NaturalTransformation.η (
                  (Functors D Sets) [ f-η c' ∘ Functor.F₁ F f ]) d x
              ≅ NaturalTransformation.η (
                  (Functors D Sets) [ Functor.F₁ G f  ∘ f-η c ]) d x
  f-commute-het {c} {c'} f {d} {x} = begin
        NaturalTransformation.η (f-η c') d (NaturalTransformation.η (Functor.F₁ F f) d x)
        ≅⟨ f-η-η-id c' d ⟩
        NaturalTransformation.η (Functor.F₁ F f) d x
        ≅⟨ eq-morph-nat c c' d f (Het.sym (f-η-η-id c d)) ⟩
        NaturalTransformation.η (Functor.F₁ G f) d (NaturalTransformation.η (f-η c) d x)
        ∎  

  nat : NaturalTransformation F G 
  nat = ntHelper (record { η = f-η ; commute = λ f → Het.≅-to-≡ (f-commute-het f)  })

open HRTFunctors public 

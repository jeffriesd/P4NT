{-# OPTIONS --rewriting --confluence-check #-}
open import Agda.Builtin.Equality.Rewrite


open import Categories.Category 
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.Unit using (⊤ ; tt )
open import Data.Empty using (⊥) 
open import Function using (const ; flip) renaming (id to idf; _∘_ to _∘'_)
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Binary using (IsEquivalence ; Reflexive ; Transitive ; Symmetric)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec ; [] ; _∷_; replicate) renaming (map to vmap)
open import Data.Product renaming (_×_ to _×'_)
open import Data.Bool
open import SetCats 
open VecCat 

open import Utils

module RelCats where 

-- proof irrelevant relation (subset of product)...
REL0 : ∀ {l} → Set l → Set l → Set l
REL0 A B = A → B → Bool

{-
_implies_ : Bool → Bool → Bool
false implies _ = true
true  implies q = q
-}


data isTrue : Bool → Set where
  istrue : isTrue true

private
    variable
      a a' : Level
      A : Set a
      B : Set a'
      b b1 b2 : Bool 


[inj₁,inj₂]-id : ∀ {x : A ⊎ B} → Data.Sum.[ inj₁ , inj₂ ] x ≡ x 
[inj₁,inj₂]-id {x = inj₁ x} = ≡.refl
[inj₁,inj₂]-id {x = inj₂ y} = ≡.refl
{-# REWRITE [inj₁,inj₂]-id #-}



∧-false : b ∧ false ≡ false
∧-false {false} = ≡.refl
∧-false {true} = ≡.refl
{-# REWRITE ∧-false #-}

∨-true : b ∨ true ≡ true 
∨-true {true} = ≡.refl
∨-true {false} = ≡.refl
{-# REWRITE ∨-true #-}


∧-isTrue : isTrue (b1 ∧ b2) → isTrue b1 ×' isTrue b2
∧-isTrue {true} {true} p = istrue , istrue

∧-isTrue-, : isTrue b1 ×' isTrue b2 → isTrue (b1 ∧ b2) 
∧-isTrue-, (istrue , istrue) = istrue

∨-isTrue : isTrue (b1 ∨ b2) → isTrue b1 ⊎ isTrue b2
∨-isTrue {false} {true}  p = inj₂ istrue
∨-isTrue {true}  {false} p = inj₁ istrue
∨-isTrue {true}  {true}  p = inj₁ istrue

∨-isTrue-inj : isTrue b1 ⊎ isTrue b2 → isTrue (b1 ∨ b2) 
∨-isTrue-inj (inj₁ istrue) = istrue
∨-isTrue-inj (inj₂ istrue) = istrue

-- map-isTrue : ∀ {A} → (f : A → Bool) → isTrue b → isTrue (f b) 




preservesRel : ∀ {A B A' B' : Set} → (R : REL0 A B) → (R' : REL0 A' B')
               → (f : A → A') → (g : B → B') → Set 
preservesRel R R' f g = ∀ {x y} → isTrue (R x y) → isTrue (R' (f x) (g y))

preservesRel-comp : ∀ {A B A' B' A'' B'' : Set} → (R : REL0 A B) → (R' : REL0 A' B') → (R'' : REL0 A'' B'')
               → (f : A → A') → (g : B → B') → (f' : A' → A'') → (g' : B' → B'') 
               → preservesRel R R' f g
               → preservesRel R' R'' f' g'
               → preservesRel R R'' (f' ∘' f) (g' ∘' g)
preservesRel-comp R R' R'' f g f' g' pfg pf'g' = pf'g' ∘' pfg  

record RelObj : Set (lsuc lzero) where
  constructor R[_,_,_]
  field
    fst : Set 
    snd : Set 
    rel : REL0 fst snd
open RelObj 

preservesRelObj : ∀ (R R' : RelObj)
               → (f : RelObj.fst R → RelObj.fst R') → (g : RelObj.snd R → RelObj.snd R') → Set 
preservesRelObj R R' f g = preservesRel (RelObj.rel R) (RelObj.rel R') f g 
-- ∀ {x y} → isTrue (RelObj.rel R x y) → isTrue (RelObj.rel R' (f x) (g y))

preservesRelObj-comp : ∀ (R R' R'' : RelObj)
               → (f : fst R → fst R') → (g : snd R → snd R') → (f' : fst R' → fst R'') → (g' : snd R' → snd R'') 
               → preservesRelObj R R' f g
               → preservesRelObj R' R'' f' g'
               → preservesRelObj R R'' (f' ∘' f) (g' ∘' g)
preservesRelObj-comp R R' R'' f g f' g' pfg pf'g' = pf'g' ∘' pfg  




record RelMorph (R S : RelObj) : Set (lsuc lzero) where
  constructor RM[_,_,_]
  open RelObj
  field
    mfst : fst R → fst S
    msnd : snd R → snd S
    preserves : preservesRelObj R S mfst msnd 

idRelMorph : ∀ {R} → RelMorph R R 
idRelMorph = record { mfst = idf ; msnd = idf ; preserves = idf } 


Rels : Category (lsuc lzero) (lsuc lzero) lzero
Rels = record
  { Obj = RelObj
  ; _⇒_ = RelMorph
  ; _≈_ = λ f g → (mfst f Sets.≈ mfst g) ×' (msnd f Sets.≈ msnd g)
  ; id = idRelMorph
  ; _∘_ = λ f g → record { mfst = mfst f Sets.∘ mfst g ; msnd = msnd f Sets.∘ msnd g
                         ; preserves =  preserves f ∘' preserves g }
  ; assoc = λ { {f = f} {g} {h} → Sets.assoc {f = mfst f} {mfst g} {mfst h}
                                  , Sets.assoc {f = msnd f} {msnd g} {msnd h} }
  ; sym-assoc = λ { {f = f} {g} {h} → Sets.sym-assoc {f = mfst f} {mfst g} {mfst h}
                      , Sets.sym-assoc {f = msnd f} {msnd g} {msnd h} }
  ; identityˡ = λ { {f = f} → Sets.identityˡ {f = mfst f} , Sets.identityˡ {f = msnd f}}
  ; identityʳ = λ { {f = f} → Sets.identityʳ {f = mfst f} , Sets.identityʳ {f = msnd f}}
  ; identity² = Sets.identity² , Sets.identity²
  ; equiv = record { refl = ≡.refl , ≡.refl
                   ; sym = λ { (e1 , e2) →  SetsEq.sym (λ {x} → e1 {x}) , SetsEq.sym (λ {x} → e2 {x}) }
                   ; trans = λ { (e1 , e2) (h1 , h2) → (SetsEq.trans (λ {x} → e1 {x}) λ {x} → h1 {x} )
                                , (SetsEq.trans (λ {x} → e2 {x}) λ {x} → h2 {x} ) } }
  ; ∘-resp-≈ = λ (f1≡h1 , f2≡h2) (g1≡i1 , g2≡i2) →
            (Sets.∘-resp-≈ (λ {x} → f1≡h1 {x}) λ {x} → g1≡i1 {x})
              , (Sets.∘-resp-≈ (λ {x} → f2≡h2 {x}) λ {x} → g2≡i2 {x})
  }
  where open RelObj
        open RelMorph
        module Sets   = Category Sets
        module SetsEq = Category.Equiv Sets



-- function space between vector of relations 
{-
-- don't need these, we can just use Cat^ Rels 

RelVecFSpace : ∀ {k : ℕ} → Vec RelObj k → Vec RelObj k → Set (lsuc lzero)
RelVecFSpace {k} = foreach2 RelMorph

idRelMorphVec : ∀ {k : ℕ} {Rs : Vec RelObj k} → RelVecFSpace Rs Rs
idRelMorphVec {.0} {[]} = lift Data.Unit.tt
idRelMorphVec {.(suc _)} {x ∷ Rs} = idRelMorph , idRelMorphVec


pointwise-rel-≈ : ∀ {k} {Rs Ss : Vec RelObj k} → (gs gs' : RelVecFSpace Rs Ss) → Set 
pointwise-rel-≈ {zero} {[]} {[]} (lift Data.Unit.tt) (lift Data.Unit.tt) = ⊤
pointwise-rel-≈ {suc k} {R ∷ Rs} {S ∷ Ss} (g , gs) (g' , gs') = g Rels.≈ g' ×' pointwise-rel-≈ gs gs'
  where module Rels = Category Rels
-}

Rels^ : ℕ → Category (lsuc lzero) (lsuc lzero) lzero
Rels^ k = Cat^ Rels k

[Rels^_,Rels] : ∀ k → Category (lsuc lzero) (lsuc lzero) (lsuc lzero) 
[Rels^ k ,Rels] = [[ Rels^ k , Rels ]] 

vecfst : ∀ {k} → Vec RelObj k → Vec Set k
vecfst = vmap RelObj.fst

vecsnd : ∀ {k} → Vec RelObj k → Vec Set k
vecsnd = vmap RelObj.snd


record RTObj (k : ℕ) : Set (lsuc lzero) where 
  open RelObj
  field 
    F1 : Functor (Sets^ k) Sets
    F2 : Functor (Sets^ k) Sets
    F* : Functor (Rels^ k) Rels 

    F*-preserves-1 : ∀ (Rs : Vec RelObj k) → fst (Functor.F₀ F* Rs) ≡ Functor.F₀ F1 (vecfst Rs)
    F*-preserves-2 : ∀ (Rs : Vec RelObj k) → snd (Functor.F₀ F* Rs) ≡ Functor.F₀ F2 (vecsnd Rs)
    
    -- F*-preserves-1 : ∀ (R : Vec RelObj k) → Functor.F₀ F1 (vecfst R) ≡ fst (Functor.F₀ F* R) 
    -- F*-preserves-2 : ∀ (R : Vec RelObj k) → Functor.F₀ F2 (vecsnd R) ≡ snd (Functor.F₀ F* R) 

  -- -- this still doesn't work because fst is 'neither a defined symbol nor a constructor'... 
  -- F*-p-1 : ∀ (Rs : Vec RelObj k) → fst (Functor.F₀ F* Rs) ≡ Functor.F₀ F1 (vecfst Rs)
  -- F*-p-1 Rs = F*-preserves-1 Rs 
  -- {-# REWRITE F*-p-1 #-}


{- 
try to add rewrite rules for RTObj.F*-preserves-1, 
but it seems to fail because RelObj.fst is not a normally-defined function
(it is a record field) 
module test {k : ℕ} (RT : RTObj k) (Rs : Vec RelObj k) where 

    abstract
      F0 = Functor.F₀ (RTObj.F1 RT)
      fst' = RelObj.fst 

      RTObj-resp-1 : fst' (Functor.F₀ (RTObj.F* RT) Rs)
                   ≡ Functor.F₀ (RTObj.F1 RT) (vecfst Rs)
      RTObj-resp-1 = RTObj.F*-preserves-1 RT Rs 

      RTObj-resp-2 :  Functor.F₀ (RTObj.F1 RT) (vecfst Rs)
                    ≡ fst' (Functor.F₀ (RTObj.F* RT) Rs)
      RTObj-resp-2 = ≡.sym (RTObj.F*-preserves-1 RT Rs )
      -- {-# REWRITE RTObj-resp-2 #-}


      F0-equiv : F0 ≡ Functor.F₀ (RTObj.F1 RT) 
      F0-equiv = ≡.refl 
      {-# REWRITE F0-equiv #-}

      fst-equiv : fst' ≡ RelObj.fst 
      fst-equiv = ≡.refl 

open test     

rfst : RelObj → Set 
rfst R[ fst , _ , _ ] = fst

rfst-ext : RelObj.fst ≡ rfst 
rfst-ext = ≡.refl 

-- not a valid rewrite rule because rfst reduces to RelObj.fst 
RTObj-resp-rfst : ∀ {k} (RT : RTObj k) (Rs : Vec RelObj k)
                → rfst (Functor.F₀ (RTObj.F* RT) Rs)
                ≡ Functor.F₀ (RTObj.F1 RT) (vecfst Rs)
RTObj-resp-rfst RT Rs = RTObj.F*-preserves-1 RT Rs
-- {-# REWRITE RTObj-resp-rfst #-}




-- fst'-equiv : ∀ {k} (RT : RTObj k) (Rs : Vec RelObj k) → fst' RT Rs ≡ RelObj.fst 
-- fst'-equiv = fst-equiv
-- {-# REWRITE fst'-equiv #-}

-- this works but only because fst' is abstract ...
-- if we add a rewrite rule to compute fst' (fst'-equiv) then this no longer is a valid rewrite rule 
RTObj-resp-1' : ∀ {k} (RT : RTObj k) (Rs : Vec RelObj k) → fst' RT Rs (Functor.F₀ (RTObj.F* RT) Rs)
                ≡ Functor.F₀ (RTObj.F1 RT) (vecfst Rs)
RTObj-resp-1' = RTObj-resp-1 
{-# REWRITE RTObj-resp-1' #-}
-- 
-- -- RTObj-resp-1'' : ∀ {k} (RT : RTObj k) (Rs : Vec RelObj k) → RelObj.fst (Functor.F₀ (RTObj.F* RT) Rs)
-- --                 ≡ Functor.F₀ (RTObj.F1 RT) (vecfst Rs)
-- -- RTObj-resp-1'' = RTObj-resp-1 
-- -- {-# REWRITE RTObj-resp-1'' #-}

-}




fcong : ∀ {A B C D : Set} → A ≡ C → B ≡ D → (C → D) → A → B
fcong ≡.refl ≡.refl = idf 

get-comp-1 : ∀ {k : ℕ} → (H K : RTObj k) → (d1 : NaturalTransformation (RTObj.F1 H) (RTObj.F1 K)) 
         → (Rs : Vec RelObj k)
         → RelObj.fst (Functor.F₀ (RTObj.F* H) Rs)
         → RelObj.fst (Functor.F₀ (RTObj.F* K) Rs)
-- get-comp-1 H K d1 Rs rewrite (RTObj.F*-preserves-1 H Rs) | (RTObj.F*-preserves-1 K Rs) = NaturalTransformation.η d1 (vecfst Rs) 
get-comp-1 H K d1 Rs  = fcong (RTObj.F*-preserves-1 H Rs) (RTObj.F*-preserves-1 K Rs) (NaturalTransformation.η d1 (vecfst Rs)) 

-- get-comp-1 H K d1 Rs with (RTObj.F*-preserves-1 H Rs) | (RTObj.F*-preserves-1 K Rs)
-- ... | p | r = {!p!} 
-- NaturalTransformation.η d1 (vecfst Rs) 


-- this works using fcong in get-comp-1 but not when
-- a rewrite is used in get-comp-1 
get-comp-1-id : ∀ {k : ℕ} → (H : RTObj k) 
         → (Rs : Vec RelObj k)
         → ∀ {x} 
         → get-comp-1 H H idnat Rs x ≡ x 
get-comp-1-id H Rs rewrite (RTObj.F*-preserves-1 H Rs) = ≡.refl 


get-comp-1-compose : ∀ {k : ℕ} → (H K L : RTObj k)
         → (d1  : NaturalTransformation (RTObj.F1 K) (RTObj.F1 L)) 
         → (d1' : NaturalTransformation (RTObj.F1 H) (RTObj.F1 K)) 
         → (Rs : Vec RelObj k)
         → get-comp-1 H L (d1 ∘v d1') Rs
         ≡ get-comp-1 K L d1 Rs ∘' get-comp-1 H K d1' Rs 
get-comp-1-compose H K L d1 d1' Rs rewrite (RTObj.F*-preserves-1 H Rs) | (RTObj.F*-preserves-1 K Rs) | (RTObj.F*-preserves-1 L Rs) = ≡.refl



get-comp-2 : ∀ {k : ℕ} → (H K : RTObj k) → (d2 : NaturalTransformation (RTObj.F2 H) (RTObj.F2 K)) 
         → (Rs : Vec RelObj k)
         → RelObj.snd (Functor.F₀ (RTObj.F* H) Rs)
         → RelObj.snd (Functor.F₀ (RTObj.F* K) Rs)
-- get-comp-2 H K d2 Rs rewrite (RTObj.F*-preserves-2 H Rs) | (RTObj.F*-preserves-2 K Rs) = NaturalTransformation.η d2 (vecsnd Rs) 
get-comp-2 H K d2 Rs  = fcong (RTObj.F*-preserves-2 H Rs) (RTObj.F*-preserves-2 K Rs) (NaturalTransformation.η d2 (vecsnd Rs)) 

get-comp-2-id : ∀ {k : ℕ} → (H : RTObj k) 
         → (Rs : Vec RelObj k)
         → ∀ {x} 
         → get-comp-2 H H idnat Rs x ≡ x 
get-comp-2-id H Rs rewrite (RTObj.F*-preserves-2 H Rs) = ≡.refl 


get-comp-2-compose : ∀ {k : ℕ} → (H K L : RTObj k)
         → (d2  : NaturalTransformation (RTObj.F2 K) (RTObj.F2 L)) 
         → (d2' : NaturalTransformation (RTObj.F2 H) (RTObj.F2 K)) 
         → (Rs : Vec RelObj k)
         → get-comp-2 H L (d2 ∘v d2') Rs
         ≡ get-comp-2 K L d2 Rs ∘' get-comp-2 H K d2' Rs 
get-comp-2-compose H K L d2 d2' Rs rewrite (RTObj.F*-preserves-2 H Rs) | (RTObj.F*-preserves-2 K Rs) | (RTObj.F*-preserves-2 L Rs) = ≡.refl


RTMorph-resp : ∀ {k : ℕ} → (H K : RTObj k) → (d1 : NaturalTransformation (RTObj.F1 H) (RTObj.F1 K)) 
         → (d2 : NaturalTransformation (RTObj.F2 H) (RTObj.F2 K)) 
         → (Rs : Vec RelObj k) → Set 
RTMorph-resp H K d1 d2 Rs = preservesRelObj (Functor.F₀ (RTObj.F* H) Rs) (Functor.F₀ (RTObj.F* K) Rs) (get-comp-1 H K d1 Rs) (get-comp-2 H K d2 Rs) 
--   where open RelObj
--         module H = RTObj H 
--         module K = RTObj K 
--         d1As = NaturalTransformation.η d1 (vecfst Rs)
--         d2Bs = NaturalTransformation.η d2 (vecsnd Rs)
--         -- K*d1Asx,d2Bsy = isTrue (rel (Functor.F₀ K.F* Rs) (d1As x) (d2Bs y))
--         HRs = Functor.F₀ H.F* Rs
--         KRs = Functor.F₀ K.F* Rs
--         d1As* : fst HRs → fst KRs
--         d1As* rewrite (RTObj.F*-preserves-1 H Rs) | (RTObj.F*-preserves-1 K Rs) = d1As
--         d2Bs* : snd HRs → snd KRs
--         d2Bs* rewrite (RTObj.F*-preserves-2 H Rs) | (RTObj.F*-preserves-2 K Rs) = d2Bs



-- rewrite (RTObj.F*-preserves-1 H Rs) | (RTObj.F*-preserves-1 K Rs) | (RTObj.F*-preserves-2 H Rs) | (RTObj.F*-preserves-2 K Rs)
    -- = preservesRelObj (Functor.F₀ H.F* Rs) (Functor.F₀ K.F* Rs)  {! NaturalTransformation.η d1 (vecfst Rs)  !} {!   !} 
    --   where module H = RTObj H
    --         module K = RTObj K 
    --         open RelObj
    --         p = (RTObj.F*-preserves-1 H Rs)


record RTMorph {k : ℕ} (H K : RTObj k) : Set (lsuc lzero) where 
  constructor RTM[_,_,_] 
  module H = RTObj H
  module K = RTObj K 

  field 
    d1 : NaturalTransformation H.F1 K.F1
    d2 : NaturalTransformation H.F2 K.F2


    d-resp : ∀ (Rs : Vec RelObj k) → RTMorph-resp H K d1 d2 Rs 
    -- d-resp : ∀ (Rs : Vec RelObj k) → preservesRelObj (Functor.F₀ H.F* Rs) (Functor.F₀ K.F* Rs)  {! NaturalTransformation.η d1 (vecfst Rs)  !} {!   !} 
    --                                   -- (NaturalTransformation.η d1 (vecfst Rs))
    --                                   -- (NaturalTransformation.η d2 (vecsnd Rs))


idRTMorph : ∀ {k : ℕ} → (H : RTObj k) → RTMorph H H
idRTMorph {k} H = record { d1 = idnat ; d2 = idnat ; d-resp = id-resp  } 
          where id-resp : ∀ (Rs : Vec RelObj k) → RTMorph-resp H H idnat idnat Rs
                id-resp Rs {x} {y} p rewrite get-comp-1-id H Rs {x} | get-comp-2-id H Rs {y} = p  

compose-RTMorph : ∀ {k} {J K L : RTObj k} → RTMorph K L → RTMorph J K → RTMorph J L
compose-RTMorph {k} {J} {K} {L} record { d1 = d1 ; d2 = d2 ; d-resp = d-resp } record { d1 = d1' ; d2 = d2' ; d-resp = d-resp' } =
    record { d1 = d1 ∘v d1'  ; d2 = d2 ∘v d2' ; d-resp = d-resp-comp  } 
            where d-resp-comp : ∀ (Rs : Vec RelObj k) → RTMorph-resp J L (d1 ∘v d1') (d2 ∘v d2') Rs
                  d-resp-comp Rs {x} {y} rewrite (get-comp-1-compose J K L d1 d1' Rs) | (get-comp-2-compose J K L d2 d2' Rs) = 
                    let
                        -- x : fst (Functor.F₀ (RTObj.F* J) Rs)
                        -- y : snd (Functor.F₀ (RTObj.F* J) Rs)
                        JRs = Functor.F₀ (RTObj.F* J) Rs
                        KRs = Functor.F₀ (RTObj.F* K) Rs
                        LRs = Functor.F₀ (RTObj.F* L) Rs

                        dresp : preservesRelObj KRs LRs (get-comp-1 K L d1 Rs) (get-comp-2 K L d2 Rs)
                        dresp = d-resp Rs
                        dresp' : preservesRelObj JRs KRs (get-comp-1 J K d1' Rs) (get-comp-2 J K d2' Rs)
                        dresp' = d-resp' Rs
                    in preservesRelObj-comp  JRs  KRs LRs (get-comp-1 J K d1' Rs) (get-comp-2 J K d2' Rs) (get-comp-1 K L d1 Rs) (get-comp-2 K L d2 Rs) dresp' dresp    


RTMorph-≈ : ∀ {k} {H K : RTObj k} → (m1 m2 : RTMorph H K) → Set₁ 
RTMorph-≈ {k} m m' = [Sets^ k ,Sets] [ RTMorph.d1 m ≈ RTMorph.d1 m' ]
                     ×' [Sets^ k ,Sets] [ RTMorph.d2 m ≈ RTMorph.d2 m' ]  

RTMorph-≈-Equiv : ∀ {k} {A B : RTObj k} → IsEquivalence (RTMorph-≈ {k} {A} {B})
RTMorph-≈-Equiv = record { refl = ≡.refl , ≡.refl ; sym = λ { (p1 , p2)  → ≡.sym p1 , ≡.sym p2  } ; trans = λ { (p1 , p2) (r1 , r2) → (≡.trans p1 r1) , (≡.trans p2 r2) }  } 


RT : ℕ → Category (lsuc lzero) (lsuc lzero) (lsuc lzero) 
RT k =  record
  { Obj = RTObj k
  ; _⇒_ = RTMorph 
  ; _≈_ = RTMorph-≈  
  ; id = λ {H} → idRTMorph H   
  ; _∘_ =   compose-RTMorph 
  ; assoc =  ≡.refl , ≡.refl 
  ; sym-assoc =  ≡.refl , ≡.refl
  ; identityˡ = ≡.refl , ≡.refl
  ; identityʳ = ≡.refl , ≡.refl
  ; identity² = ≡.refl , ≡.refl
  ; equiv = RTMorph-≈-Equiv  
  ; ∘-resp-≈ = λ { {f = f} {g} {h} {i} (f1≈h1 , f2≈h2) (g1≈i1 , g2≈i2) → SetFuncs.∘-resp-≈ {f = RTMorph.d1 f} {RTMorph.d1 g} {RTMorph.d1 h} {RTMorph.d1 i} f1≈h1 g1≈i1
                                                                       , SetFuncs.∘-resp-≈ {f = RTMorph.d2 f} {RTMorph.d2 g} {RTMorph.d2 h} {RTMorph.d2 i} f2≈h2 g2≈i2 } 
  }
  where module SetFuncs = Category [Sets^ k ,Sets]
        






module PolynomialRels where 

    open import Categories.Object.Terminal 

    -- first we have the actual relations (subsets) for initial and terminal relation 
    Rel0⊤ : REL0 ⊤ ⊤
    Rel0⊤ _ _ = true

    Rel⊤ : RelObj
    Rel⊤ = R[ ⊤ , ⊤ , Rel0⊤ ]

    Rel⊤! : ∀ {R : RelObj} → RelMorph R Rel⊤ 
    Rel⊤! = RM[ const tt , const tt , const istrue ]

    Rel⊤-IsTerminal : IsTerminal Rels Rel⊤
    Rel⊤-IsTerminal = record { ! = Rel⊤! ; !-unique = λ _ → ≡.refl , ≡.refl } 

    RelTerminal : Terminal Rels
    RelTerminal = record { ⊤ = Rel⊤ ; ⊤-is-terminal = Rel⊤-IsTerminal } 

    -- there are two possible choices here 
    -- either the constantly false relation 
    Rel⊥0 : REL0 ⊥ ⊥ 
    Rel⊥0 _ _ = false 

    -- or we can use bottom-elimination (absurd pattern) 
    Rel⊥0-elim : REL0 ⊥ ⊥ 
    Rel⊥0-elim () 

    Rel⊥ : RelObj 
    Rel⊥ = R[ ⊥ , ⊥ , Rel⊥0 ] 

    Rel⊥! : ∀ {R : RelObj} → RelMorph Rel⊥ R
    Rel⊥! = RM[ exFalso , exFalso , (λ()) ] 
    


    -- product of REL0 objects
    _×Rel0_ : ∀ {A B A' B' : Set} → REL0 A B → REL0 A' B' → REL0 (A ×' A') (B ×' B')
    (R0 ×Rel0 S0) (x , x') (y , y') = R0 x y ∧ S0 x' y'  

    -- sum of RelObj objects 
    _×Rel_ : RelObj → RelObj → RelObj
    R ×Rel S = R[ (fst R ×' fst S) , (snd R ×' snd S) , (rel R ×Rel0 rel S) ] 



    -- sum of REL0 objects
    _+Rel0_ : ∀ {A B A' B' : Set} → REL0 A B → REL0 A' B' → REL0 (A ⊎ A') (B ⊎ B')
    (R0 +Rel0 S0) (inj₁ x) (inj₁ y) = R0 x y 
    -- (R0 +Rel0 S0) (inj₁ x) (inj₂ y) = {!!}
    -- (R0 +Rel0 S0) (inj₂ y) (inj₁ x) = {!!}
    (R0 +Rel0 S0) (inj₂ x') (inj₂ y') = S0 x' y'
    {-# CATCHALL #-}
    (R0 +Rel0 S0) _ _ = false


    -- sum of RelObj objects 
    _+Rel_ : RelObj → RelObj → RelObj
    R +Rel S = R[ (fst R ⊎ fst S) , (snd R ⊎ snd S) , (rel R +Rel0 rel S) ] 


    -- TODO need actions on morphisms as well 

    _×RelM_ : ∀ {R S R' S' : RelObj} → RelMorph R S → RelMorph R' S' → RelMorph (R ×Rel R') (S ×Rel S')
    _×RelM_ {R} {S} {R'} {S'} RM[ f , g , fg-preserves ] RM[ f' , g' , f'g'-preserves ]  =
        RM[ funcprod (f , f')  , funcprod (g , g') , prod-preserves ] 
            where prod-preserves : preservesRelObj (R ×Rel R') (S ×Rel S') (funcprod (f , f')) (funcprod (g , g'))
                  prod-preserves {x , x'} {y , y'} p  = ∧-isTrue-, ( Sfxgy , S'f'x'g'y' ) 
                        where fgp : isTrue (rel R x y) → isTrue (rel S (f x) (g y))
                              fgp = fg-preserves {x} {y} 

                              f'g'p : isTrue (rel R' x' y') → isTrue (rel S' (f' x') (g' y'))
                              f'g'p = f'g'-preserves {x'} {y'} 

                              isTrue-prod : isTrue (rel R x y) ×' isTrue (rel R' x' y') 
                              isTrue-prod = ∧-isTrue p

                              Sfxgy : isTrue (rel S (f x) (g y))
                              Sfxgy = fgp (proj₁ isTrue-prod)
                              S'f'x'g'y' : isTrue (rel S' (f' x') (g' y'))
                              S'f'x'g'y' = f'g'p (proj₂ isTrue-prod)

    _+RelM_ : ∀ {R S R' S' : RelObj} → RelMorph R S → RelMorph R' S' → RelMorph (R +Rel R') (S +Rel S')
    _+RelM_ {R} {S} {R'} {S'} RM[ f , g , fg-preserves ] RM[ f' , g' , f'g'-preserves ]  =
                RM[ Data.Sum.map f f' , Data.Sum.map g g' , (λ { {x} {y} → sum-preserves {x} {y} }) ] 
                    where sum-preserves : preservesRelObj (R +Rel R') (S +Rel S') (Data.Sum.map f f') (Data.Sum.map g g')
                          sum-preserves {inj₁ x}  {inj₁ y}  p  = fg-preserves p
                          sum-preserves {inj₂ x'} {inj₂ y'} p' = f'g'-preserves p'



open PolynomialRels public




module PolynomialRelFunctors where 
  private
    variable 
      o l e o' l' e' : Level
      C : Category o l e 
      C' : Category o' l' e' 
      F : Functor C C' 

  open import Categories.Category.Product using (Product ; _※_) -- ; Swap ; πˡ ; πʳ ; _⁂_ ; _※_) 
  open import Categories.Functor using (Functor ; _∘F_ ) renaming (id to idF)
  open import Categories.NaturalTransformation
  
    
  RelsProd : Functor (Product Rels Rels) Rels
  RelsProd = record
               { F₀ = uncurry _×Rel_
               ; F₁ = uncurry _×RelM_
               ; identity = ≡.refl , ≡.refl
               ; homomorphism = ≡.refl , ≡.refl
               ; F-resp-≈ = λ { ((f1≈h1 , f2≈h2) , (g1≈i1 , g2≈i2)) → ×'-cong f1≈h1 g1≈i1 , ×'-cong f2≈h2  g2≈i2 } 
               } 

  RelsSum : Functor (Product Rels Rels) Rels
  RelsSum = record
               { F₀ = uncurry _+Rel_
               ; F₁ = uncurry _+RelM_
               -- identity is immediate because of [inj₁,inj₂]-id rewrite rule 
               ; identity = ≡.refl , ≡.refl 
               ; homomorphism = (λ { {inj₁ x} → ≡.refl ; {inj₂ y} → ≡.refl }) , λ { {inj₁ x} → ≡.refl ; {inj₂ y} → ≡.refl }  
               ; F-resp-≈ = λ { ((f1≈h1 , f2≈h2) , (g1≈i1 , g2≈i2))
                              → (λ { {inj₁ x} → ≡.cong inj₁ f1≈h1 ; {inj₂ y} → ≡.cong inj₂ g1≈i1 } )
                                , λ { {inj₁ x} → ≡.cong inj₁ f2≈h2 ; {inj₂ y} → ≡.cong inj₂ g2≈i2 }  } 
               } 

  RelsK⊤ : Functor C Rels
  RelsK⊤ = ConstF Rel⊤

  RelsK⊤! : NaturalTransformation F RelsK⊤
  RelsK⊤! = record { η = λ _ → Rel⊤!  ; commute = λ _ → ≡.refl , ≡.refl ; sym-commute = λ _ → ≡.refl , ≡.refl } 


  _+Rels_ : ∀ (F G : Functor C Rels) → Functor C Rels
  F +Rels G = RelsSum ∘F (F ※ G) 

  _×Rels_ : ∀ (F G : Functor C Rels) → Functor C Rels
  F ×Rels G = RelsProd ∘F (F ※ G) 


open PolynomialRelFunctors public 

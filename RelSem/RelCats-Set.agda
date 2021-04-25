{-# OPTIONS --allow-unsolved-metas --rewriting --confluence-check --irrelevant-projections #-}
open import Agda.Builtin.Equality.Rewrite


open import Categories.Category 
open import Categories.Functor using (Functor ; Endofunctor ; _∘F_ )
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.Unit using (⊤ ; tt )
open import Data.Empty using (⊥) 
open import Function using (const ; flip) renaming (id to idf; _∘_ to _∘'_)
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Relation.Binary using (IsEquivalence ; Reflexive ; Transitive ; Symmetric)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec ; [] ; _∷_) renaming (map to vmap)
open import Data.Product renaming (_×_ to _×'_ ; map to ×'-map)
open import Data.Product.Properties using (,-injectiveˡ ; ,-injectiveʳ) 
open import Data.Bool
open import SetCats 
open VecCat 


open import Utils

module RelSem.RelCats-Set where 


-- proof irrelevant relation
record IRREL0 (A B : Set) : Set₁ where 
  field 
    R : A → B → Set
    irrelevant : ∀ {x : A} {y : B} → (p p' : R x y) → p ≡ p'

-- proof relevant relation 
-- REL0 : Set → Set → Set₁ 
-- REL0 = IRREL0
  
-- _,_∈_ : ∀ {A B : Set} → A → B → REL0 A B → Set
-- x , y ∈ R = IRREL0.R R x y 

-- irrel : ∀ {A B : Set} → (R : IRREL0 A B) → ∀ {x : A} {y : B} → (p p' : x , y ∈ R ) → p ≡ p'
-- irrel R = IRREL0.irrelevant R 

REL0 : Set → Set → Set₁ 
REL0 A B = A → B → Set
  
_,_∈_ : ∀ {A B : Set} → A → B → REL0 A B → Set
x , y ∈ R = R x y 


private
    variable
      a b : Level
      A : Set a
      B : Set b




record RelObj : Set (lsuc lzero) where
  constructor R[_,_,_]
  field
    fst : Set 
    snd : Set 
    rel : REL0 fst snd

    -- irrelevant : ∀ {x y} → (p p' : rel x y) → p ≡ p'
  

open RelObj 



preservesRel : ∀ {A B A' B' : Set} → (R : REL0 A B) → (R' : REL0 A' B')
               → (f : A → A') → (g : B → B') → Set 
preservesRel R R' f g = ∀ {x y} → x , y ∈ R → (f x) , (g y) ∈ R'


preservesRel-comp : ∀ {A B A' B' A'' B'' : Set} → (R : REL0 A B) → (R' : REL0 A' B') → (R'' : REL0 A'' B'')
               → (f : A → A') → (g : B → B') → (f' : A' → A'') → (g' : B' → B'') 
               → preservesRel R R' f g
               → preservesRel R' R'' f' g'
               → preservesRel R R'' (f' ∘' f) (g' ∘' g)
preservesRel-comp R R' R'' f g f' g' pfg pf'g' = pf'g' ∘' pfg  


preservesRelObj : ∀ (R R' : RelObj)
               → (f : RelObj.fst R → RelObj.fst R') → (g : RelObj.snd R → RelObj.snd R') → Set 
preservesRelObj R R' f g = preservesRel (RelObj.rel R) (RelObj.rel R') f g 

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

open RelMorph using (mfst ; msnd)

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


Rels^ : ℕ → Category (lsuc lzero) (lsuc lzero) lzero
Rels^ k = Cat^ Rels k

[Rels^_,Rels] : ∀ k → Category (lsuc lzero) (lsuc lzero) (lsuc lzero) 
[Rels^ k ,Rels] = [[ Rels^ k , Rels ]] 

vecfst : ∀ {k} → Vec RelObj k → Vec Set k
vecfst = vmap RelObj.fst

vecsnd : ∀ {k} → Vec RelObj k → Vec Set k
vecsnd = vmap RelObj.snd

π₁ : Functor Rels Sets
π₁ = record
       { F₀ = fst
       ; F₁ = mfst
       ; identity = ≡.refl
       ; homomorphism = ≡.refl
       ; F-resp-≈ = λ f1≈g1,f2≈g2 → proj₁ f1≈g1,f2≈g2
       } 

π₂ : Functor Rels Sets
π₂ = record
       { F₀ = snd
       ; F₁ = msnd
       ; identity = ≡.refl
       ; homomorphism = ≡.refl
       ; F-resp-≈ = λ f1≈g1,f2≈g2 → proj₂ f1≈g1,f2≈g2
       } 

EqRelObj : Set → RelObj
EqRelObj X = R[ X , X , _≡_ ] 

EqRel-map : ∀ {X Y : Set} → (X → Y) → RelMorph (EqRelObj X) (EqRelObj Y)
EqRel-map f = RM[ f , f , (λ x≡y → ≡.cong f x≡y) ]

Eq : Functor Sets Rels 
Eq = record
       { F₀ = EqRelObj
       ; F₁ = EqRel-map
       ; identity = ≡.refl , ≡.refl
       ; homomorphism = ≡.refl , ≡.refl
       ; F-resp-≈ = λ f≈g → f≈g , f≈g 
       } 

open VecFunc 
π₁Vec : ∀ (k : ℕ) → Functor (Rels^ k) (Sets^ k)
π₁Vec = Func^ Rels Sets π₁ 

π₂Vec : ∀ (k : ℕ) → Functor (Rels^ k) (Sets^ k)
π₂Vec = Func^ Rels Sets π₂

vecmfst : ∀ {k} {Rs Ss : Vec RelObj k} → (Rels^ k) [ Rs , Ss ] → (Sets^ k) [ vecfst Rs , vecfst Ss ]
--vecmfst {Rs = []} {[]} _ = bigtt 
--vecmfst {Rs = R ∷ Rs} {S ∷ Ss} (m , ms) = (mfst m) , (vecmfst ms) 
vecmfst {k} {Rs = Rs} {S } ms = Functor.F₁ (π₁Vec k) ms 

vecmsnd : ∀ {k} {Rs Ss : Vec RelObj k} → (Rels^ k) [ Rs , Ss ] → (Sets^ k) [ vecsnd Rs , vecsnd Ss ]
-- vecmsnd {Rs = R ∷ Rs} {S ∷ Ss} (m , ms) = (msnd m) , (vecmsnd ms) 
-- vecmsnd {Rs = []} {[]} _ = bigtt 
vecmsnd {k} {Rs = Rs} {Ss} ms = Functor.F₁ (π₂Vec k) ms



EqVec : ∀ (k : ℕ) → Functor (Sets^ k) (Rels^ k)
EqVec = Func^ Sets Rels Eq




-- need heterogeneous equality to express equality of morphisms 
import Relation.Binary.HeterogeneousEquality as Het



-- instead of asking for a functor of type [Rels^ k ,Rels] and then asserting
-- a bunch of (non-definitional) equalities, we can just ask for the minimal
-- pieces needed to define such a functor, and then define the functor
-- so that these equalities hold definitionally 
record RTObj*Components {k : ℕ} (F1 F2 : Functor (Sets^ k) Sets) : Set₁ where 
  open RelObj
  module F1 = Functor F1
  module F2 = Functor F2
  field 
    -- all we need is the action on objects (relations) 
    F*Rel : ∀ (Rs : Vec RelObj k) → REL0 (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))
    -- and a proof that the functions F1.₁ (vecmfst ms) and F2.₁ (vecmsnd ms)
    -- preserves the relations given by F*Rel 
    F*Rel-preserves : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ])
                      → preservesRel (F*Rel Rs) (F*Rel Ss) (F1.₁ (vecmfst ms)) (F2.₁ (vecmsnd ms))

  -- given F*Rel and F*Rel-preserves, we can define the functor F* 
  
  F*RelObj : ∀ (Rs : Vec RelObj k) → RelObj
  F*RelObj Rs = R[ (F1.₀ (vecfst Rs)) , (F2.₀ (vecsnd Rs)) , (F*Rel Rs) ] 

  F*RelMap : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ]) → Rels [ F*RelObj Rs , F*RelObj Ss ]
  F*RelMap {Rs} {Ss} ms = RM[ (F1.₁ (vecmfst ms)) , (F2.₁ (vecmsnd ms)) , F*Rel-preserves ms ]

  F* : Functor (Rels^ k) Rels
  F* =
    let F1∘π₁ : Functor (Rels^ k) Sets
        F1∘π₁ = (F1 ∘F Func^ Rels Sets π₁ k)
        F2∘π₂ : Functor (Rels^ k) Sets
        F2∘π₂ = (F2 ∘F Func^ Rels Sets π₂ k)
     in 
     record
         { F₀ = F*RelObj
         ; F₁ = F*RelMap
         ; identity = Functor.identity F1∘π₁ , Functor.identity F2∘π₂ 
         ; homomorphism = Functor.homomorphism F1∘π₁ , Functor.homomorphism F2∘π₂
         ; F-resp-≈ = λ f≈g → Functor.F-resp-≈ F1∘π₁ f≈g , Functor.F-resp-≈ F2∘π₂ f≈g
         } 


record RTObj (k : ℕ) : Set (lsuc lzero) where 
  constructor RT[_,_,_]
  open RelObj
  field 
    F1 : Functor (Sets^ k) Sets
    F2 : Functor (Sets^ k) Sets
    F*Components : RTObj*Components F1 F2 

  F* : Functor (Rels^ k) Rels 
  F* = RTObj*Components.F* F*Components 

RTMorph-resp : ∀ {k : ℕ} → (H K : RTObj k) → (d1 : NaturalTransformation (RTObj.F1 H) (RTObj.F1 K)) 
         → (d2 : NaturalTransformation (RTObj.F2 H) (RTObj.F2 K)) 
         → (Rs : Vec RelObj k) → Set 
RTMorph-resp H K d1 d2 Rs = preservesRelObj (Functor.F₀ (RTObj.F* H) Rs)
                                            (Functor.F₀ (RTObj.F* K) Rs)
                                            (NaturalTransformation.η d1 (vecfst Rs))
                                            (NaturalTransformation.η d2 (vecsnd Rs)) 

record RTMorph {k : ℕ} (H K : RTObj k) : Set (lsuc lzero) where 
  constructor RTM[_,_,_] 
  private module H = RTObj H
  private module K = RTObj K 

  field 
    d1 : NaturalTransformation H.F1 K.F1
    d2 : NaturalTransformation H.F2 K.F2


    d-resp : ∀ {Rs : Vec RelObj k} → RTMorph-resp H K d1 d2 Rs 

  -- we can define a natural transformation
  -- from H.F* to K.F* in terms of d1 and d2.
  -- Naturality follows componentwise from naturality of d1 and d2,
  -- and the fact that each component of d* preserves relations follows
  -- directly from d-resp 
  d* : NaturalTransformation (RTObj.F* H) (RTObj.F* K)
  d* = record { η = λ Rs → RM[ (NaturalTransformation.η d1 (vecfst Rs)) , (NaturalTransformation.η d2 (vecsnd Rs)) , d-resp ]
              ; commute = λ fs → (NaturalTransformation.commute d1 (vecmfst fs)) , NaturalTransformation.commute d2 (vecmsnd fs)
              ; sym-commute = λ fs → ( (NaturalTransformation.sym-commute d1 (vecmfst fs))) , (NaturalTransformation.sym-commute d2 (vecmsnd fs))  }


idRTMorph : ∀ {k : ℕ} → (H : RTObj k) → RTMorph H H
idRTMorph {k} H = record { d1 = idnat ; d2 = idnat ; d-resp = λ xy∈H*R → xy∈H*R } 

compose-RTMorph : ∀ {k} {J K L : RTObj k} → RTMorph K L → RTMorph J K → RTMorph J L
compose-RTMorph RTM[ f1 , f2 , f-resp ] RTM[ g1 , g2 , g-resp ] = RTM[ f1 ∘v g1 , f2 ∘v g2 , f-resp ∘' g-resp ] 


RTMorph-≈ : ∀ {k} {H K : RTObj k} → (m1 m2 : RTMorph H K) → Set₁ 
RTMorph-≈ {k} m m' = [Sets^ k ,Sets] [ RTMorph.d1 m ≈ RTMorph.d1 m' ]
                     ×' [Sets^ k ,Sets] [ RTMorph.d2 m ≈ RTMorph.d2 m' ]  

RTMorph-≈-Equiv : ∀ {k} {A B : RTObj k} → IsEquivalence (RTMorph-≈ {k} {A} {B})
RTMorph-≈-Equiv = record { refl = ≡.refl , ≡.refl ; sym = λ { (p1 , p2)  → ≡.sym p1 , ≡.sym p2  } ; trans = λ { (p1 , p2) (r1 , r2) → (≡.trans p1 r1) , (≡.trans p2 r2) }  } 


RTCat : ℕ → Category (lsuc lzero) (lsuc lzero) (lsuc lzero) 
RTCat k =  record
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
        
π₁RT : ∀ {k} → Functor (RTCat k) [Sets^ k ,Sets]
π₁RT {k} = record
             { F₀ = RTObj.F1
             ; F₁ = RTMorph.d1
             ; identity = ≡.refl
             ; homomorphism = ≡.refl
             ; F-resp-≈ = λ f≈g → proj₁ f≈g
             } 

π₂RT : ∀ {k} → Functor (RTCat k) [Sets^ k ,Sets]
π₂RT {k} = record
             { F₀ = RTObj.F2
             ; F₁ = RTMorph.d2
             ; identity = ≡.refl
             ; homomorphism = ≡.refl
             ; F-resp-≈ = λ f≈g → proj₂ f≈g
             } 

-- should be able to embed RT k into Rels functor category
embedRT : ∀ {k} → Functor (RTCat k) [Rels^ k ,Rels] 
embedRT = record
            { F₀ = λ Rt → RTObj.F* Rt 
            -- need to define natural transformation in [Rels^ k ,Rels] in terms
            -- of RTMorph.
            ; F₁ = λ d → RTMorph.d* d  
            ; identity = ≡.refl , ≡.refl
            ; homomorphism = ≡.refl , ≡.refl
            ; F-resp-≈ = λ f≈g → proj₁ f≈g  , proj₂ f≈g
            } 

{- 
-- was using this version of RelSet, but it requires additional assumptions (about relations being irrelevant)
-- but even with these added assumptions, it is tedious 

   
RelSet : ∀ (R : RelObj) → Set
RelSet R[ X , Y , R* ] = Σ[ x ∈ X ] (Σ[ y ∈ Y ] (x , y ∈ R* ))

RelSet-map : ∀ {R S : RelObj} → RelMorph R S → RelSet R → RelSet S
RelSet-map RM[ ffst , fsnd , preserves ] (x , y , rxy) = ffst x , fsnd y , preserves rxy

RelSet-cong : ∀ (R : RelObj) (x x' : fst R) (y y' : snd R) → (x ≡ x') → (y ≡ y')
              → (p : x , y ∈ (rel R)) → (p' : x' , y' ∈ (rel R))
              → (x , (y , p)) ≡ (x' , (y' , p'))
RelSet-cong R x .x y .y ≡.refl ≡.refl p p' = ≡.cong (_,_ x) (≡.cong (_,_ y) {!    !})
-- (≡.cong (_,_ y) (irrel (rel R)  p p'))



RelSet-resp : ∀ (R S : RelObj) (f g : Rels [ R , S ]) (f1≈g1 : (Sets Category.≈ mfst f) (mfst g))
                → (f2≈g2 : (Sets Category.≈ msnd f) (msnd g)) (x : fst R) (y : snd R)
                → (rxy : x , y ∈ rel R )
                → RelSet-map f (x , y , rxy) ≡ RelSet-map g (x , y , rxy)
RelSet-resp R S f g f1≈g1 f2≈g2 x y rxy =
    let 
        fx = mfst f x ; fy = msnd f y
        gx = mfst g x ; gy = msnd g y 

        pf : fx , fy ∈ rel S 
        pf = RelMorph.preserves f rxy

        pg : gx , gy ∈ rel S
        pg = RelMorph.preserves g rxy

        fx≡gx = f1≈g1 {x}
        fy≡gy = f2≈g2 {y}
    in RelSet-cong S fx gx fy gy fx≡gx fy≡gy pf pg 


RelSetF : Functor Rels Sets
RelSetF = record
            { F₀ = RelSet
            ; F₁ = RelSet-map
            ; identity = ≡.refl
            ; homomorphism = ≡.refl
            ; F-resp-≈ = λ { {A = R} {B = S} {f = f} {g = g} (f₁≈g₁ , f₂≈g₂) {x , y , rxy} → RelSet-resp R S f g f₁≈g₁ f₂≈g₂ x y } 
            }
            

-- function from the relation seen as an object to the underlying product 
incl : ∀ (R : RelObj) → RelSet R → RelUProd R
incl R (x , y , _) = x , y

inclNat : NaturalTransformation RelSetF RelUProdF 
inclNat = ntHelper (record { η = incl ; commute = λ f → ≡.refl }) 
-}



-- this version of RelSet makes the irrelevance of
-- relatedness proof explicit. 
record RelSet (R : RelObj) : Set where
  constructor RI[_,_,_]
  field
    x : fst R
    y : snd R 
    -- make proof of relatedness irrelevant here.
    -- we care that x and y are related when constructing
    -- RelSetirr but we don't care about p for equality 
    .p : x , y ∈ rel R 


-- note . preceding p and p' for irrelevance 
RelSet-eq : ∀ {R : RelObj} {x x' : fst R} {y y' : snd R} .{p : x , y ∈ rel R} .{p' : x' , y' ∈ rel R} → x ≡ x' → y ≡ y' → RI[ x , y , p ] ≡ RI[ x' , y' , p' ] 
-- RelSet-eq : ∀ {R : RelObj} {x x' : fst R} {y y' : snd R} → x ≡ x' → y ≡ y' → RI[ x , y , _ ] ≡ RI[ x' , y' , _ ] 
RelSet-eq ≡.refl ≡.refl = ≡.refl

RelSet-map : ∀ {R S : RelObj} → Rels [ R , S ] → Sets [ RelSet R , RelSet S ]
RelSet-map {R} {S} RM[ f1 , f2 , p ] Ri = RI[ f1 (RelSet.x Ri) , f2 (RelSet.y Ri) , p (RelSet.p Ri) ]



RelSetF : Functor Rels Sets
RelSetF = record
             { F₀ = RelSet
             ; F₁ = RelSet-map 
             ; identity = ≡.refl
             ; homomorphism = ≡.refl
             ; F-resp-≈ = λ { (f1≈g1 , f2≈g2) {RI[ x , y , p ]} → RelSet-eq (f1≈g1 {x}) (f2≈g2 {y})  } 
             } 

-- get the underlying product  of a relation 
RelUProd : ∀ (R : RelObj) → Set
RelUProd R[ X , Y , _ ] = X ×' Y

RelUProdF : Functor Rels Sets
RelUProdF = record
                { F₀ = RelUProd
                ; F₁ = λ f → ×'-map (mfst f) (msnd f)
                ; identity = ≡.refl
                ; homomorphism = ≡.refl
                ; F-resp-≈ = λ { (f1≈g1 , f2≈g2) → ×'-cong f1≈g1 f2≈g2 } 
                } 

RelUProd⇒π₁ : NaturalTransformation RelUProdF π₁
RelUProd⇒π₁ = ntHelper (record { η = λ R → proj₁ ;  commute = λ f → ≡.refl }) 

RelUProd⇒π₂ : NaturalTransformation RelUProdF π₂
RelUProd⇒π₂ = ntHelper (record { η = λ R → proj₂ ;  commute = λ f → ≡.refl }) 

-- inclusion of related elements into underlying product 
incl : ∀ (R : RelObj) → RelSet R → RelUProd R
incl R RI[ x , y , _ ] = x , y

-- this inclusion is natural in R 
inclNat : NaturalTransformation RelSetF RelUProdF 
inclNat = ntHelper (record { η = incl ; commute = λ f → ≡.refl }) 






module Identities {k : ℕ} (F : Functor (Sets^ k) Sets) where 
    private module F = Functor F 
    open F using (F₀ ; F₁) 


    factor-subset : ∀ {A B C : Set} → (f : A → B ×' C) → REL0 B C 
    factor-subset {A} f b c = Σ[ x ∈ A ] f x ≡ (b , c)  

    vmap-foreach : ∀ {o l e} {C : Category o l e} (F G : Functor C Sets)
                    → (nat : NaturalTransformation F G)
                    → ∀ xs → Sets^ k [ vmap (Functor.F₀ F) xs , vmap (Functor.F₀ G) xs ] 
    vmap-foreach {C = C} F G nat = NaturalTransformation.η (VecFuncH.HFunc^-map C Sets nat) 

    vmap-foreach-commute : ∀ {o l e} {C : Category o l e} (F G : Functor C Sets)
                    → (nat : NaturalTransformation F G)
                    → ∀ {xs} {ys} (fs : (Cat^ C k) [ xs , ys ])
                    → Sets^ k [ vmap-foreach F G nat ys ∘SetVec (Func^-map C Sets F fs)
                              ≈ (Func^-map C Sets G fs) ∘SetVec vmap-foreach F G nat xs ]
    vmap-foreach-commute {C = C} F G nat = NaturalTransformation.commute (VecFuncH.HFunc^-map C Sets nat)  

    h-A×B-R : ∀ (Rs : Vec RelObj k)
            → F₀ (vmap RelUProd Rs) → F₀ (vecfst Rs) ×' F₀ (vecsnd Rs)
    h-A×B-R Rs = < F₁ (vmap-foreach RelUProdF π₁ RelUProd⇒π₁ Rs) , F₁ ( (vmap-foreach RelUProdF π₂  RelUProd⇒π₂ Rs)) >  

    vmap-incl : ∀ (Rs : Vec RelObj k) → Sets^ k [ vmap RelSet Rs , vmap RelUProd Rs ] 
    vmap-incl = vmap-foreach RelSetF RelUProdF inclNat 

    -- Goal: Sets^ k [ vmap RelSet Rs , vmap (λ R → fst R × snd R) Rs ]
    Fincl :  ∀ (Rs : Vec RelObj k)  
            → F₀ (vmap RelSet Rs) → F₀ (vmap RelUProd Rs)
    Fincl Rs FRs = F₁ ( vmap-incl Rs ) FRs

    idRT** : ∀ (Rs : Category.Obj (Rels^ k)) → REL0 (F₀ (vecfst Rs)) (F₀ (vecsnd Rs))
    idRT** Rs = factor-subset {A = F₀ (vmap RelSet Rs)} (h-A×B-R Rs ∘' Fincl Rs)

    idRT**-preserves : ∀ {Rs Ss : Vec RelObj k} (ms : Rels^ k [ Rs , Ss ])
                       → preservesRel (idRT** Rs) (idRT** Ss) (Functor.₁ F (vecmfst ms))
                                                              (Functor.₁ F (vecmsnd ms))
    idRT**-preserves {Rs} {Ss} ms {x} {y} (F-SetRs , h∘Fincl-Rs≡x,y ) =
      let map-ms : F₀ (vmap RelSet Rs) → F₀ (vmap RelSet Ss) 
          map-ms = F₁ (Functor.F₁ (Func^ Rels Sets RelSetF k) ms)

          vmapfst = vmap-foreach RelUProdF π₁ RelUProd⇒π₁ 
          vmapsnd  = vmap-foreach RelUProdF π₂ RelUProd⇒π₂ 

          vmapRelSet = Func^-map Rels Sets RelSetF 
          vmapRelUProd  = Func^-map Rels Sets RelUProdF

          have1 : F₁ (vmapfst Rs) (F₁ (vmap-incl Rs) F-SetRs)
                    ≡ x 
          have1 = ,-injectiveˡ h∘Fincl-Rs≡x,y  

          have2 : F₁ (vmapsnd Rs) (F₁ (vmap-incl Rs) F-SetRs)
                  ≡ y 
          have2 = ,-injectiveʳ h∘Fincl-Rs≡x,y   

          com1 : (Sets^ k) [ vmapfst Ss ∘SetVec vmapRelUProd ms
                           ≈ vecmfst ms ∘SetVec vmapfst Rs ]
          com1 = vmap-foreach-commute RelUProdF π₁ RelUProd⇒π₁ ms

          com2 : (Sets^ k) [ vmap-incl Ss ∘SetVec vmapRelSet ms
                           ≈ vmapRelUProd ms ∘SetVec vmap-incl Rs ]
          com2 = vmap-foreach-commute RelSetF RelUProdF inclNat ms

          -- naturality proofs 
          comp1 : (Sets^ k) [ vmapfst Ss ∘SetVec (vmap-incl Ss ∘SetVec vmapRelSet ms)
                             ≈ vecmfst ms ∘SetVec (vmapfst Rs ∘SetVec vmap-incl Rs) ]
          comp1 =  begin≈ vmapfst Ss ∘SetVec (vmap-incl Ss ∘SetVec vmapRelSet ms)
                        ≈⟨ ( refl⟩∘⟨ com2) ⟩
                        vmapfst Ss ∘SetVec (vmapRelUProd ms ∘SetVec vmap-incl Rs)
                        ≈⟨ Sk.sym-assoc ⟩
                        (vmapfst Ss ∘SetVec vmapRelUProd ms) ∘SetVec vmap-incl Rs
                        ≈⟨ com1 ⟩∘⟨refl ⟩ 
                        (vecmfst ms ∘SetVec vmapfst Rs)  ∘SetVec vmap-incl Rs
                        ≈⟨ Sk.assoc ⟩
                        vecmfst ms ∘SetVec (vmapfst Rs ∘SetVec vmap-incl Rs)
                        ≈∎ 
    
          h1 : F₁ (vmapfst Ss) (F₁ (vmap-incl Ss) (F₁ (vmapRelSet ms) F-SetRs))
               ≡ F₁ (vecmfst ms) x 
          h1 =  begin F₁ (vmapfst Ss) (F₁ (vmap-incl Ss) (F₁ (vmapRelSet ms) F-SetRs)) 
                     ≡˘⟨ ≡.cong (F₁ (vmapfst Ss)) F.homomorphism ⟩
                     F₁ (vmapfst Ss) (F₁ ((vmap-incl Ss) ∘SetVec  (vmapRelSet ms)) F-SetRs)
                     ≡˘⟨ F.homomorphism ⟩
                     F₁ ((vmapfst Ss) ∘SetVec ((vmap-incl Ss) ∘SetVec (vmapRelSet ms))) F-SetRs
                     ≡⟨ F.F-resp-≈ comp1 ⟩ 
                     F₁ (vecmfst ms ∘SetVec (vmapfst Rs ∘SetVec vmap-incl Rs)) F-SetRs
                     ≡⟨  F.homomorphism ⟩ 
                     F₁ (vecmfst ms) (F₁ (vmapfst Rs ∘SetVec vmap-incl Rs) F-SetRs)
                     ≡⟨  ≡.cong (F₁ (vecmfst ms)) F.homomorphism ⟩ 
                     F₁ (vecmfst ms) (F₁ (vmapfst Rs) (F₁ (vmap-incl Rs) F-SetRs))
                     ≡⟨ ≡.cong (F₁ (vecmfst ms)) have1  ⟩ 
                     F₁ (vecmfst ms) x 
                     ∎ 

          comp2 : (Sets^ k) [ vmapsnd Ss ∘SetVec (vmap-incl Ss ∘SetVec vmapRelSet ms)
                             ≈ vecmsnd ms ∘SetVec (vmapsnd Rs ∘SetVec vmap-incl Rs) ]
          comp2 =  begin≈ vmapsnd Ss ∘SetVec (vmap-incl Ss ∘SetVec vmapRelSet ms)
                        ≈⟨ ( refl⟩∘⟨ com2) ⟩
                        vmapsnd Ss ∘SetVec (vmapRelUProd ms ∘SetVec vmap-incl Rs)
                        ≈⟨ Sk.sym-assoc ⟩
                        (vmapsnd Ss ∘SetVec vmapRelUProd ms) ∘SetVec vmap-incl Rs
                        ≈⟨  vmap-foreach-commute RelUProdF π₂ RelUProd⇒π₂ ms ⟩∘⟨refl ⟩ 
                        (vecmsnd ms ∘SetVec vmapsnd Rs)  ∘SetVec vmap-incl Rs
                        ≈⟨ Sk.assoc ⟩
                        vecmsnd ms ∘SetVec (vmapsnd Rs ∘SetVec vmap-incl Rs)
                        ≈∎ 
    
          h2 : F₁ (vmapsnd Ss) (F₁ (vmap-incl Ss) (F₁ (vmapRelSet ms) F-SetRs))
               ≡ F₁ (vecmsnd ms) y
          h2 =  begin F₁ (vmapsnd Ss) (F₁ (vmap-incl Ss) (F₁ (vmapRelSet ms) F-SetRs)) 
                     ≡˘⟨ ≡.cong (F₁ (vmapsnd Ss)) F.homomorphism ⟩
                     F₁ (vmapsnd Ss) (F₁ ((vmap-incl Ss) ∘SetVec  (vmapRelSet ms)) F-SetRs)
                     ≡˘⟨ F.homomorphism ⟩
                     F₁ ((vmapsnd Ss) ∘SetVec ((vmap-incl Ss) ∘SetVec (vmapRelSet ms))) F-SetRs
                     ≡⟨ F.F-resp-≈ comp2 ⟩ 
                     F₁ (vecmsnd ms ∘SetVec (vmapsnd Rs ∘SetVec vmap-incl Rs)) F-SetRs
                     ≡⟨  F.homomorphism ⟩ 
                     F₁ (vecmsnd ms) (F₁ (vmapsnd Rs ∘SetVec vmap-incl Rs) F-SetRs)
                     ≡⟨  ≡.cong (F₁ (vecmsnd ms)) F.homomorphism ⟩ 
                     F₁ (vecmsnd ms) (F₁ (vmapsnd Rs) (F₁ (vmap-incl Rs) F-SetRs))
                     ≡⟨ ≡.cong (F₁ (vecmsnd ms)) have2  ⟩ 
                     F₁ (vecmsnd ms) y
                     ∎ 

          h : h-A×B-R Ss (Fincl Ss (map-ms F-SetRs))
              ≡ (Functor.₁ F (vecmfst ms) x , Functor.₁ F (vecmsnd ms) y)
          h =  ≡.cong₂ _,_ h1 h2 

       in map-ms F-SetRs ,  h
        where open ≡.≡-Reasoning
              module Sk = Category (Sets^ k)
              open Sk.HomReasoning hiding (step-≡ ; step-≡˘) renaming (begin_ to begin≈_ ; _∎ to _≈∎) 

    idRT*Components : RTObj*Components F F 
    idRT*Components = record { F*Rel = idRT** ; F*Rel-preserves = idRT**-preserves } 

    idRT : RTObj k
    idRT = RT[ F , F , idRT*Components  ]

open Identities 


idRTFunctor-resp : ∀ {k} {F G : Category.Obj [Sets^ k ,Sets]}
                   → (η : [Sets^ k ,Sets] [ F , G ])
                   → {Rs : Vec RelObj k}
                   → RTMorph-resp (idRT F) (idRT G) η η Rs
idRTFunctor-resp {k} {F} {G} η {Rs} {x} {y} (F*Rs , hF*Rs≡x,y) =
  let π₁Rs = VecFuncH.HFunc^-map-comp Rels Sets (RelUProd⇒π₁) Rs
      π₂Rs = VecFuncH.HFunc^-map-comp Rels Sets (RelUProd⇒π₂) Rs
      inclRs = VecFuncH.HFunc^-map-comp Rels Sets (inclNat) Rs
      vmapRelSet = NaturalTransformation.η η (vmap (RelSet) Rs) 

      have1 : Functor.F₁ F π₁Rs (Functor.F₁ F inclRs F*Rs) ≡ x
      have1 = ,-injectiveˡ hF*Rs≡x,y 

      have1' : Functor.F₁ F (π₁Rs ∘SetVec inclRs) F*Rs ≡ x
      have1' = ≡.trans (Functor.homomorphism F) have1

      have2 : Functor.F₁ F π₂Rs (Functor.F₁ F inclRs F*Rs) ≡ y
      have2 = ,-injectiveʳ hF*Rs≡x,y 

      have2' : Functor.F₁ F (π₂Rs ∘SetVec inclRs) F*Rs ≡ y
      have2' = ≡.trans (Functor.homomorphism F) have2

      h1 : Functor.F₁ G π₁Rs (Functor.F₁ G inclRs (vmapRelSet F*Rs))
           ≡ NaturalTransformation.η η (vecfst Rs) x
      h1 = begin Functor.F₁ G π₁Rs (Functor.F₁ G inclRs (vmapRelSet F*Rs))
                ≡˘⟨ Functor.homomorphism G ⟩
                 Functor.F₁ G (π₁Rs ∘SetVec inclRs) (vmapRelSet F*Rs)
                ≡⟨ NaturalTransformation.sym-commute η (π₁Rs ∘SetVec inclRs)  ⟩
                 NaturalTransformation.η η (vecfst Rs) (Functor.F₁ F (π₁Rs ∘SetVec inclRs) F*Rs)
                ≡⟨ ≡.cong (NaturalTransformation.η η (vecfst Rs)) have1' ⟩ 
                NaturalTransformation.η η (vecfst Rs) x
                ∎   

      h2 : Functor.F₁ G π₂Rs (Functor.F₁ G inclRs (vmapRelSet F*Rs))
           ≡ NaturalTransformation.η η (vecsnd Rs) y
      h2 = begin Functor.F₁ G π₂Rs (Functor.F₁ G inclRs (vmapRelSet F*Rs))
                ≡˘⟨ Functor.homomorphism G ⟩
                 Functor.F₁ G (π₂Rs ∘SetVec inclRs) (vmapRelSet F*Rs)
                ≡⟨ NaturalTransformation.sym-commute η (π₂Rs ∘SetVec inclRs)  ⟩
                 NaturalTransformation.η η (vecsnd Rs) (Functor.F₁ F (π₂Rs ∘SetVec inclRs) F*Rs)
                ≡⟨ ≡.cong (NaturalTransformation.η η (vecsnd Rs)) have2' ⟩ 
                NaturalTransformation.η η (vecsnd Rs) y
                ∎   
      
   in (NaturalTransformation.η η (vmap (RelSet) Rs) F*Rs ) , ≡.cong₂ _,_ h1 h2 
     where open ≡.≡-Reasoning


idRTFunctor : ∀ {k} → Functor [Sets^ k ,Sets] (RTCat k)
idRTFunctor = record
                { F₀ = λ F → idRT F
                ; F₁ = λ η → RTM[ η , η , idRTFunctor-resp η ] 
                ; identity = ≡.refl , ≡.refl
                ; homomorphism = ≡.refl , ≡.refl
                ; F-resp-≈ = λ f≈g → f≈g , f≈g
                } 


module PolynomialRels where 

    open import Categories.Object.Terminal 
    open import Categories.Object.Initial

    -- first we have the actual relations (subsets) for initial and terminal relation 
    Rel0⊤ : REL0 ⊤ ⊤
    Rel0⊤ _ _ = ⊤

    Rel⊤ : RelObj
    Rel⊤ = R[ ⊤ , ⊤ , Rel0⊤ ]

    Rel⊤! : ∀ {R : RelObj} → RelMorph R Rel⊤ 
    Rel⊤! = RM[ const tt , const tt , const tt ]

    Rel⊤-IsTerminal : IsTerminal Rels Rel⊤
    Rel⊤-IsTerminal = record { ! = Rel⊤! ; !-unique = λ _ → ≡.refl , ≡.refl } 

    RelTerminal : Terminal Rels
    RelTerminal = record { ⊤ = Rel⊤ ; ⊤-is-terminal = Rel⊤-IsTerminal } 

    -- there are two possible choices to define initial relation 
    -- either the constantly false relation 
    Rel⊥0 : REL0 ⊥ ⊥ 
    Rel⊥0 _ _ = ⊥

    -- or we can use bottom-elimination (absurd pattern) 
    Rel⊥0-elim : REL0 ⊥ ⊥ 
    Rel⊥0-elim () 


    Rel⊥ : RelObj 
    Rel⊥ = R[ ⊥ , ⊥ , Rel⊥0 ] 

    Rel⊥! : ∀ {R : RelObj} → RelMorph Rel⊥ R
    Rel⊥! = RM[ exFalso , exFalso , (λ()) ] 
    
    Rel⊥-IsInitial : IsInitial Rels Rel⊥
    Rel⊥-IsInitial = record { ! = Rel⊥! ; !-unique = λ _ → (λ { {()} }) , (λ { {()} })  }

    RelInitial : Initial Rels
    RelInitial = record { ⊥ = Rel⊥ ; ⊥-is-initial = Rel⊥-IsInitial } 

    -- product of REL0 objects
    _×Rel0_ : ∀ {A B A' B' : Set} → REL0 A B → REL0 A' B' → REL0 (A ×' A') (B ×' B')
    (R0 ×Rel0 S0) (x , x') (y , y') = R0 x y ×'  S0 x' y'  

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
    (R0 +Rel0 S0) _ _ = ⊥

    -- sum of RelObj objects 
    _+Rel_ : RelObj → RelObj → RelObj
    R +Rel S = R[ (fst R ⊎ fst S) , (snd R ⊎ snd S) , (rel R +Rel0 rel S) ] 

    -- action of product functor on morphisms 
    _×RelM_ : ∀ {R S R' S' : RelObj} → RelMorph R S → RelMorph R' S' → RelMorph (R ×Rel R') (S ×Rel S')
    _×RelM_ {R} {S} {R'} {S'} RM[ f , g , fg-preserves ] RM[ f' , g' , f'g'-preserves ]  =
        RM[ funcprod (f , f')  , funcprod (g , g') , prod-preserves ] 
            where prod-preserves : preservesRelObj (R ×Rel R') (S ×Rel S') (funcprod (f , f')) (funcprod (g , g'))
                  prod-preserves {x , x'} {y , y'} p  = Sfxgy , S'f'x'g'y' -- ∧--, ( Sfxgy , S'f'x'g'y' ) 
                        where fgp :  (rel R x y) →  (rel S (f x) (g y))
                              fgp = fg-preserves {x} {y} 

                              f'g'p :  (rel R' x' y') →  (rel S' (f' x') (g' y'))
                              f'g'p = f'g'-preserves {x'} {y'} 

                              Sfxgy :  (rel S (f x) (g y))
                              Sfxgy = fgp (proj₁ p)
                              S'f'x'g'y' :  (rel S' (f' x') (g' y'))
                              S'f'x'g'y' = f'g'p (proj₂ p)

    -- action of sum functor on morphisms 
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

  [inj₁,inj₂]-id : ∀ {x : A ⊎ B} → Data.Sum.[ inj₁ , inj₂ ] x ≡ x 
  [inj₁,inj₂]-id {x = inj₁ x} = ≡.refl
  [inj₁,inj₂]-id {x = inj₂ y} = ≡.refl
  {-# REWRITE [inj₁,inj₂]-id #-}

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









record HRTObj* {k : ℕ} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) : Set₁ where
  module H1 = Functor H1 
  module H2 = Functor H2 
  open RelObj
  field

    H*RTRel : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
              → REL0 (Functor.F₀ (Functor.F₀ H1 (RTObj.F1 Rt)) (vecfst Rs))
                     (Functor.F₀ (Functor.F₀ H2 (RTObj.F2 Rt)) (vecsnd Rs))

    -- second 'implicit' bullet point after definition 3.6 
    H*RTRel-preserves : ∀ (Rt : RTObj k) → {Rs Ss : Vec RelObj k}
                        → (ms : Rels^ k [ Rs , Ss ])
                        → preservesRel (H*RTRel Rt Rs) (H*RTRel Rt Ss)
                            (Functor.F₁ (Functor.₀ H1 (RTObj.F1 Rt)) (vecmfst ms))
                            (Functor.F₁ (Functor.₀ H2 (RTObj.F2 Rt)) (vecmsnd ms))

    -- third 'implicit' bullet point after definition 3.6 
    H*RT-preserves : ∀ {Rt St : RTObj k} (m : RTMorph Rt St) → {Rs : Vec RelObj k}
                        → preservesRel (H*RTRel Rt Rs) (H*RTRel St Rs)
                            (NaturalTransformation.η (H1.F₁ (RTMorph.d1 m)) (vecfst Rs))
                            (NaturalTransformation.η (H2.F₁ (RTMorph.d2 m)) (vecsnd Rs))
                            
  -- end fields -- 

  -- action of HRT on objects (relation transformers) 
  H*Obj : ∀ (Rt : RTObj k) → Functor (Rels^ k) Rels
  H*Obj Rt@(RT[ F1 , F2 , F* ]) = RTObj.F* RT[ H1.₀ F1  , H2.₀ F2 , record { F*Rel = H*RTRel Rt ; F*Rel-preserves = H*RTRel-preserves Rt } ] 


  H*-map-component : ∀ {Rt St : Category.Obj (RTCat k)} → (d : RTMorph Rt St)
                      → (Rs : Vec RelObj k)
                      → RelMorph (Functor.F₀ (H*Obj Rt) Rs) (Functor.F₀ (H*Obj St) Rs)
  H*-map-component m@(RTM[ d1 , d2 , d-resp ]) Rs =  RM[ (NaturalTransformation.η (Functor.F₁ H1 d1) (vecfst Rs)) , (NaturalTransformation.η (Functor.F₁ H2 d2) (vecsnd Rs)) , H*RT-preserves m ] 
  
  -- action of HRT on morphisms of relation transformers 
  H*-map : ∀ {Rt St : Category.Obj (RTCat k)}
           → (d : RTMorph Rt St)
           → [Rels^ k ,Rels] [ H*Obj Rt , H*Obj St ] 
  H*-map {Rt} m@(RTM[ d1 , d2 , d-resp ]) =
         ntHelper (record { η = H*-map-component m
                          ; commute = λ fs → NaturalTransformation.commute (Functor.F₁ H1 d1) (vecmfst fs)
                                          , NaturalTransformation.commute (Functor.F₁ H2 d2) (vecmsnd fs)})

  -- these data comprise a functor from RT to [Rels^ k ,Rels]
  H* : Functor (RTCat k) [Rels^ k ,Rels]
  H* = record
         { F₀ = λ Rt → H*Obj Rt 
         ; F₁ = λ {Rt} {St} d → H*-map d
         ; identity = (Functor.identity H1) , (Functor.identity H2)
         ; homomorphism = (Functor.homomorphism H1) , (Functor.homomorphism H2)
         ; F-resp-≈ = λ f≈g → (Functor.F-resp-≈ H1 (proj₁ f≈g)) , (Functor.F-resp-≈ H2 (proj₂ f≈g))
         } 


record HRTObj (k : ℕ) : Set₁ where 
  field
    H1 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
    H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]

    H*Obj : HRTObj* H1 H2 
  -- end fields 

  H* : Functor (RTCat k) [Rels^ k ,Rels]
  H* = HRTObj*.H* H*Obj

  HEndo-rel* : ∀ (Rt : RTObj k) → RTObj*Components (Functor.F₀ H1 (RTObj.F1 Rt)) (Functor.F₀ H2 (RTObj.F2 Rt))
  HEndo-rel* Rt = (record { F*Rel = HRTObj*.H*RTRel H*Obj Rt ; F*Rel-preserves = HRTObj*.H*RTRel-preserves H*Obj Rt }) 

  HEndo-obj : ∀ (Rt : RTObj k) → RTObj k
  HEndo-obj Rt@(RT[ F1 , F2 , F* ]) = RT[ (Functor.F₀ H1 F1) , (Functor.F₀ H2 F2) , HEndo-rel* Rt ] 
  -- HEndo-rel* Rt ] 

  HEndo-map : ∀ {Rt St : RTObj k} (d : RTMorph Rt St) → RTMorph (HEndo-obj Rt) (HEndo-obj St)
  HEndo-map d@(RTM[ d1 , d2 , d-resp ]) = RTM[ (Functor.F₁ H1 d1) , (Functor.F₁ H2 d2) , HRTObj*.H*RT-preserves H*Obj d ] 
  

  HEndo : Functor (RTCat k) (RTCat k) 
  HEndo = record
            { F₀ = λ Rt → HEndo-obj Rt 
            ; F₁ = HEndo-map 
            ; identity = (Functor.identity H1) , (Functor.identity H2)
            ; homomorphism = (Functor.homomorphism H1) , (Functor.homomorphism H2)
            ; F-resp-≈ = λ { (f1≈g1 , f2≈g2) → Functor.F-resp-≈ H1 f1≈g1 , Functor.F-resp-≈ H2 f2≈g2 } 
            } 

record HRTMorph {k : ℕ} (H K : HRTObj k) : Set₁ where
  constructor HRTM[_,_,_]
  module H = HRTObj H
  module K = HRTObj K

  open H using (H* ; H1 ; H2)
  open K renaming (H* to K* ; H1 to K1 ; H2 to K2)

  field 
    σ1 : NaturalTransformation H.H1 K.H1 
    σ2 : NaturalTransformation H.H2 K.H2 

    -- need this extra condition (implicit requirement given after dfn 3.7) 
    σ-preserves : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
                  → preservesRelObj (Functor.F₀ (Functor.F₀ H* Rt) Rs)
                                    (Functor.F₀ (Functor.F₀ K* Rt) Rs)
                    (NaturalTransformation.η (NaturalTransformation.η σ1 (RTObj.F1 Rt)) (vecfst Rs))
                    (NaturalTransformation.η (NaturalTransformation.η σ2 (RTObj.F2 Rt)) (vecsnd Rs))

  -- end fields 

  σRT-component : ∀ (Rt : RTObj k)
                  → [Rels^ k ,Rels] [ Functor.F₀ H* Rt , Functor.F₀ K* Rt ]

  σRT-component Rt@(RT[ F1 , F2 , F* ]) =
    let σ1F1 : NaturalTransformation (Functor.F₀ H1 F1) (Functor.F₀ K1 F1)
        σ1F1 = NaturalTransformation.η σ1 F1 
        σ1F1-η : ∀ (Xs : Vec Set k) → Functor.F₀ (Functor.F₀ H1 F1) Xs → Functor.F₀ (Functor.F₀ K1 F1) Xs
        σ1F1-η Xs = NaturalTransformation.η σ1F1 Xs
        -- 
        σ2F2 : NaturalTransformation (Functor.F₀ H2 F2) (Functor.F₀ K2 F2)
        σ2F2 = NaturalTransformation.η σ2 F2 
        σ2F2-η : ∀ (Xs : Vec Set k) → Functor.F₀ (Functor.F₀ H2 F2) Xs → Functor.F₀ (Functor.F₀ K2 F2) Xs
        σ2F2-η Xs = NaturalTransformation.η σ2F2 Xs
        
     in ntHelper
       (record { η = λ Rs → RM[ σ1F1-η (vecfst Rs)  , σ2F2-η (vecsnd Rs) , σ-preserves Rt Rs ] 
               ; commute = λ fs → (NaturalTransformation.commute σ1F1 (vecmfst fs)) , ( (NaturalTransformation.commute σ2F2 (vecmsnd fs)))
               })

  σRT-commute : ∀ {Rt St : Category.Obj (RTCat k)} (d : RTMorph Rt St )
                → [Rels^ k ,Rels] [ 
                    [Rels^ k ,Rels] [ σRT-component St ∘ Functor.F₁ H* d ] 
                    ≈ [Rels^ k ,Rels] [ Functor.F₁ K* d ∘ σRT-component Rt ] 
                ]
  σRT-commute {Rt} {St} d@(RTM[ d1 , d2 , d-resp ]) =
              NaturalTransformation.commute σ1 d1 , NaturalTransformation.commute σ2 d2 

  σRT : NaturalTransformation H.H* K.H*
  σRT = ntHelper (record { η = σRT-component  ; commute = σRT-commute })
  


idHRTMorph : ∀ {k : ℕ} {H : HRTObj k} → HRTMorph H H
idHRTMorph {H} = record { σ1 = idnat ; σ2 = idnat ; σ-preserves = λ Rt Rs xy∈H*Rt-Rs → xy∈H*Rt-Rs } 

composeHRTMorph : ∀ {k} {H K L : HRTObj k} →
                  HRTMorph K L → HRTMorph H K → HRTMorph H L
composeHRTMorph m@(HRTM[ σ1 , σ2 , σ-preserves ]) m'@(HRTM[ σ1' , σ2' , σ'-preserves ])
                = HRTM[ (σ1 ∘v σ1') , (σ2 ∘v σ2') , (λ Rt Rs xy∈HRtRs → σ-preserves Rt Rs (σ'-preserves Rt Rs xy∈HRtRs)) ] 


HRTCat : ℕ → Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
HRTCat k = record
             { Obj = HRTObj k
             ; _⇒_ = HRTMorph
             ; _≈_ = λ {H} {K} m m' → (HRTMorph.σ1 m ≈ HRTMorph.σ1 m') ×' ( (HRTMorph.σ2 m ≈ HRTMorph.σ2 m') )  
             ; id = idHRTMorph
             ; _∘_ = composeHRTMorph
             ; assoc = ≡.refl , ≡.refl
             ; sym-assoc = ≡.refl , ≡.refl
             ; identityˡ = ≡.refl , ≡.refl
             ; identityʳ = ≡.refl , ≡.refl
             ; identity² = ≡.refl , ≡.refl
             ; equiv = record { refl = ≡.refl , ≡.refl
                              ; sym = λ { (e1 , e2) → (≡.sym e1) , (≡.sym e2) } 
                              ; trans = λ { (f1≈g1 , f2≈g2) (g1≈h1 , g2≈h2) → ≡.trans  f1≈g1 g1≈h1 , ≡.trans f2≈g2 g2≈h2  } } 
             ; ∘-resp-≈ =
               λ { {f = f} {h} {g} {i} (f1≈h1 , f2≈h2) (g1≈i1 , g2≈i2)
                   → (∘-resp-≈ {f = σ1 f} {σ1 h} {σ1 g} {σ1 i} f1≈h1 g1≈i1)
                   , (∘-resp-≈ {f = σ2 f} {σ2 h} {σ2 g} {σ2 i} f2≈h2 g2≈i2) } 
             } 
             where open Category ([[ [Sets^ k ,Sets] ,  [Sets^ k ,Sets] ]])
                   open HRTMorph using (σ1 ; σ2)


HRTEndo-map-component : ∀ {k} {H K : HRTObj k} → HRTMorph H K
                        → (Rt : RTObj k)
                        → RTMorph (Functor.F₀ (HRTObj.HEndo H) Rt) (Functor.F₀ (HRTObj.HEndo K) Rt)
HRTEndo-map-component m@(HRTM[ σ1 , σ2 , σ-preserves ]) Rt@(RT[ F1 , F2 , F* ]) =
  RTM[ (NaturalTransformation.η σ1 F1) , NaturalTransformation.η σ2 F2 , (λ {Rs} → σ-preserves Rt Rs ) ] 


HRTEndo-map : ∀ {k} {H K : HRTObj k} → HRTMorph H K
              → [[ RTCat k , RTCat k ]]
                   [ HRTObj.HEndo H , HRTObj.HEndo K ]
HRTEndo-map m@(HRTM[ σ1 , σ2 , σ-preserves ]) =
  ntHelper (record { η = HRTEndo-map-component m
                   ; commute =
                        λ { RTM[ d1 , d2 , _ ] → (NaturalTransformation.commute σ1 d1) ,
                                                NaturalTransformation.commute σ2 d2 } })
         

-- embed HRT into category of endofunctors on RT k 
embedHRT : ∀ {k} → Functor (HRTCat k) ([[ RTCat k , RTCat k ]])
embedHRT = record
             { F₀ = HRTObj.HEndo
             ; F₁ = HRTEndo-map
             ; identity = ≡.refl , ≡.refl
             ; homomorphism = ≡.refl , ≡.refl
             ; F-resp-≈ = λ { (f1≈g1 , f2≈g2) → f1≈g1 , f2≈g2 } 
             } 



-- can we also go in the other direction? 
-- i.e., get HRTObj from endofunctor on RT? 
{-


-- Goal: REL0 (Functor.F₀ (Functor.₀ π₁RT (Functor.₀ (H ∘F idRTFunctor) (RTObj.F1 Rt))) (vecfst Rs))
--            (Functor.F₀ (Functor.₀ π₂RT (Functor.₀ (H ∘F idRTFunctor) (RTObj.F2 Rt))) (vecsnd Rs))

    -- F*Rel : ∀ (Rs : Vec RelObj k) → REL0 (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))


-- normalized Goal: REL0
--   (Functor.F₀ (RTObj.F1 (Functor.F₀ H (idRT F1))) (vmap fst Rs))
--   (Functor.F₀ (RTObj.F2 (Functor.F₀ H (idRT F2))) (vmap snd Rs))


-- H1As : Functor.F₀ (RTObj.F1 (Functor.F₀ H RT[ RTObj.F1 Rt , RTObj.F1 Rt , idRT*Components (RTObj.F1 Rt) ])) (vmap fst Rs)
-- H2Bs : Functor.F₀ (RTObj.F2 (Functor.F₀ H RT[ RTObj.F2 Rt , RTObj.F2 Rt , idRT*Components (RTObj.F2 Rt) ])) (vmap snd Rs)


    -- H*RTRel : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
    --           → REL0 (Functor.F₀ (Functor.F₀ H1 (RTObj.F1 Rt)) (vecfst Rs))
    --                  (Functor.F₀ (Functor.F₀ H2 (RTObj.F2 Rt)) (vecsnd Rs))
    -- F*Rel-preserves : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ])
    --                   → preservesRel (F*Rel Rs) (F*Rel Ss) (F1.₁ (vecmfst ms)) (F2.₁ (vecmsnd ms))





toHRT-obj*Rel : ∀ {k} (H : Category.Obj [[ RTCat k , RTCat k ]])
                  (Rt : RTObj k) (Rs : Vec RelObj k)
                  → REL0 (Functor.F₀ (Functor.F₀ (π₁RT ∘F H ∘F idRTFunctor) (RTObj.F1 Rt)) (vecfst Rs))
                         (Functor.F₀ (Functor.F₀ (π₂RT ∘F H ∘F idRTFunctor) (RTObj.F2 Rt)) (vecsnd Rs)) 
toHRT-obj*Rel H Rt Rs x y = {!!} ×' {!!} 


toHRT-obj* : ∀ {k} (H : Category.Obj [[ RTCat k , RTCat k ]])
            → HRTObj* (π₁RT ∘F H ∘F idRTFunctor) (π₂RT ∘F H ∘F idRTFunctor)
toHRT-obj* {k} H = record { H*RTRel = λ Rt Rs → {!toHRT-obj*Rel H Rt Rs!} 
-- RTObj*Components.F*Rel (RTObj.F*Components {!Functor.F₀ H Rt!}) Rs

-- HRTObj*.H*RTRel (HRTObj.H*Obj {!H!}) Rt Rs 
-- RTObj*Components.F*Rel-preserves (record { F*Rel = {!!} ; F*Rel-preserves = {!!} }) {!!} {!!} {!!} 
                        ; H*RTRel-preserves = {!!}
                        ; H*RT-preserves = {!!} } 


toHRT-obj : ∀ {k} → Category.Obj [[ RTCat k , RTCat k ]] → HRTObj k
toHRT-obj {k} H = record { H1 = π₁RT ∘F H ∘F idRTFunctor  
                         ; H2 =  π₂RT ∘F H ∘F idRTFunctor
                         ; H*Obj = {!!} } 
                         -- toHRT-obj* H } 


-- can we get back an HRT obj from an endofunctor on RT k ? 
toHRT : ∀ {k} → Functor ([[ RTCat k , RTCat k ]]) (HRTCat k) 
toHRT {k} = record
              { F₀ = toHRT-obj
              ; F₁ = {!!}
              ; identity = {!!}
              ; homomorphism = {!!}
              ; F-resp-≈ = {!!}
              } 


-}


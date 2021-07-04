{-# OPTIONS --allow-unsolved-metas --rewriting --confluence-check --irrelevant-projections #-}
open import Agda.Builtin.Equality.Rewrite


open import Categories.Category
open import Categories.Functor using (Functor ; Endofunctor ; _∘F_ ) renaming (id to idF)
open import Categories.Category.Construction.Functors using (eval)
open import Categories.Category.Product using (Product ; _⁂_)
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

module RelSem.RelCats where


{-
-- proof irrelevant relation
record IRREL (A B : Set) : Set₁ where
  field
    R : A → B → Set
    irrelevant : ∀ {x : A} {y : B} → (p p' : R x y) → p ≡ p'

-- proof relevant relation
-- REL : Set → Set → Set₁
-- REL = IRREL0

-- _,_∈_ : ∀ {A B : Set} → A → B → REL A B → Set
-- x , y ∈ R = IRREL0.R R x y

-- irrel : ∀ {A B : Set} → (R : IRREL A B) → ∀ {x : A} {y : B} → (p p' : x , y ∈ R ) → p ≡ p'
-- irrel R = IRREL0.irrelevant R
-}


REL : Set → Set → Set₁
REL A B = A → B → Set

_,_∈_ : ∀ {A B : Set} → A → B → REL A B → Set
x , y ∈ R = R x y


private
    variable
      a b : Level
      A : Set a
      B : Set b




record RelObj : Set₁ where
  constructor R[_,_,_]
  field
    fst : Set
    snd : Set
    rel : REL fst snd

    -- irrelevant : ∀ {x y} → (p p' : rel x y) → p ≡ p'


open RelObj



preservesRel : ∀ {A B A' B' : Set} → (R : REL A B) → (R' : REL A' B')
               → (f : A → A') → (g : B → B') → Set
preservesRel R R' f g = ∀ {x y} → x , y ∈ R → (f x) , (g y) ∈ R'

-- relation preserving morphisms
-- whose types might not be definitionally equal to the domains/codomains of the relations
-- i.e. (f, g) : R → S where f : A → B and (A/fst R) and (B/snd R)
-- are not definitionally equal
preservesRel-prop-eq : ∀ {A B A' B' C D C' D' : Set} → (R : REL A B) → (R' : REL A' B')
               → (f : C → C') → (g : D → D')
               → A  ≡ C  → D  ≡ B
               → A' ≡ C' → D' ≡ B'
               → Set
preservesRel-prop-eq {A} {B} R R' f g ≡.refl ≡.refl ≡.refl ≡.refl = ∀ {x : A} {y : B} → x , y ∈ R → (f x) , (g y) ∈ R'



preservesRel-comp : ∀ {A B A' B' A'' B'' : Set} → (R : REL A B) → (R' : REL A' B') → (R'' : REL A'' B'')
               → (f : A → A') → (g : B → B') → (f' : A' → A'') → (g' : B' → B'')
               → preservesRel R R' f g
               → preservesRel R' R'' f' g'
               → preservesRel R R'' (f' ∘' f) (g' ∘' g)
preservesRel-comp R R' R'' f g f' g' pfg pf'g' = pf'g' ∘' pfg



preservesRelObj : ∀ (R R' : RelObj)
                  → (f : fst R → fst R') → (g : snd R → snd R') → Set
preservesRelObj R R' f g = ∀ {x : fst R} {y : snd R} → (x , y ∈ rel R) → (f x , g y ∈ rel R')
-- preservesRel (rel R) (rel R') f g


preservesRelObj-prop-eq : ∀ {A B A' B'} (R R' : RelObj)
               → A ≡ RelObj.fst R
               → B ≡ RelObj.snd R
               → A' ≡ RelObj.fst R'
               → B' ≡ RelObj.snd R'
               → (f : A → A') (g : B → B')
               → Set
preservesRelObj-prop-eq R R' ≡.refl ≡.refl ≡.refl ≡.refl f g = preservesRelObj R R' f g


preservesRelObj-comp : ∀ (R R' R'' : RelObj)
               → (f : fst R → fst R') → (g : snd R → snd R') → (f' : fst R' → fst R'') → (g' : snd R' → snd R'')
               → preservesRelObj R R' f g
               → preservesRelObj R' R'' f' g'
               → preservesRelObj R R'' (f' ∘' f) (g' ∘' g)
preservesRelObj-comp R R' R'' f g f' g' pfg pf'g' = pf'g' ∘' pfg


record RelMorph (R S : RelObj) : Set₁ where
  constructor RM[_,_,_]
  open RelObj
  field
    mfst : fst R → fst S
    msnd : snd R → snd S
    preserves : preservesRelObj R S mfst msnd

open RelMorph

idRelMorph : ∀ {R} → RelMorph R R
idRelMorph = RM[ idf , idf , idf ]


_∘RelM_ : ∀ {R S T : RelObj} → RelMorph S T → RelMorph R S → RelMorph R T
(RM[ g1 , g2 , pg ]) ∘RelM (RM[ f1 , f2 , pf ]) = RM[ (g1 ∘' f1) , (g2 ∘' f2) , (pg ∘' pf) ]


Rels : Category (lsuc lzero) (lsuc lzero) lzero
Rels = record
  { Obj = RelObj
  ; _⇒_ = RelMorph
  ; _≈_ = λ f g → (mfst f Sets.≈ mfst g) ×' (msnd f Sets.≈ msnd g)
  ; id = idRelMorph
  ; _∘_ = _∘RelM_

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



-- if two morphisms of relations are equivalent, then we can use the preservation properties interchangeably
--
-- f : R ⇒ S
-- g : R ⇒ S
RelMorph-preserves-from : ∀ {R1 R2 S1 S2 : Set} (R : REL R1 R2) (S : REL S1 S2) {f1 g1 : R1 → S1} {f2 g2 : R2 → S2}
                       → Sets [ f1 ≈ g1 ]
                       → Sets [ f2 ≈ g2 ]
                       → preservesRel R S f1 f2
                       → preservesRel R S g1 g2
RelMorph-preserves-from R S e1 e2 pf {x} {y} xy∈R =  ≡.subst₂ S (e1 {x}) (e2 {y}) (pf xy∈R)

RelMorph-preserves-to : ∀ {R1 R2 S1 S2 : Set} (R : REL R1 R2) (S : REL S1 S2) {f1 g1 : R1 → S1} {f2 g2 : R2 → S2}
                       → Sets [ f1 ≈ g1 ]
                       → Sets [ f2 ≈ g2 ]
                       → preservesRel R S g1 g2
                       → preservesRel R S f1 f2
RelMorph-preserves-to R S e1 e2 pf {x} {y} xy∈R = ≡.subst₂ S (≡.sym (e1 {x})) (≡.sym (e2 {y})) (pf xy∈R)

open import Categories.Category.Construction.Functors

Rels^ : ℕ → Category (lsuc lzero) (lsuc lzero) lzero
Rels^ k = Cat^ Rels k

[Rels^_,Rels] : ℕ → Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
[Rels^ k ,Rels] = Functors (Rels^ k) Rels





vecfst : ∀ {k} → Vec RelObj k → Vec Set k
vecfst = vmap RelObj.fst

vecsnd : ∀ {k} → Vec RelObj k → Vec Set k
vecsnd = vmap RelObj.snd

π₁Rels : Functor Rels Sets
π₁Rels = record
       { F₀ = fst
       ; F₁ = mfst
       ; identity = ≡.refl
       ; homomorphism = ≡.refl
       ; F-resp-≈ = λ { (f1≈g1 , _)  → f1≈g1 }
       }

π₂Rels : Functor Rels Sets
π₂Rels = record
       { F₀ = snd
       ; F₁ = msnd
       ; identity = ≡.refl
       ; homomorphism = ≡.refl
       ; F-resp-≈ = λ { (_ , f2≈g2) → f2≈g2 }
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
π₁Vec = Func^ Rels Sets π₁Rels

π₂Vec : ∀ (k : ℕ) → Functor (Rels^ k) (Sets^ k)
π₂Vec = Func^ Rels Sets π₂Rels

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



{-
module original-RT where

    record RTObj' (k : ℕ) : Set₁  where
    open Category Sets using (_≈_)
    field
        F1 : Functor (Sets^ k) Sets
        F2 : Functor (Sets^ k) Sets
        F* : Functor (Rels^ k) Rels

        over-rels1 : ∀ (Rs : Vec RelObj k) → fst (Functor.F₀ F* Rs) ≡ Functor.F₀ F1 (vecfst Rs)
        over-rels2 : ∀ (Rs : Vec RelObj k) → snd (Functor.F₀ F* Rs) ≡ Functor.F₀ F2 (vecsnd Rs)

        over-morphs1 : ∀ {Rs Ss : Vec RelObj k} (ms : (Rels^ k) [ Rs , Ss ])
                    → mfst (Functor.F₁ F* ms)
                        ≈ {!!} -- Goal: fst (Functor.F₀ F* Rs) → fst (Functor.F₀ F* Ss)

        over-morphs2 : ∀ {Rs Ss : Vec RelObj k} (ms : (Rels^ k) [ Rs , Ss ])
                    → msnd (Functor.F₁ F* ms)
                        ≈ {!!} -- Goal: snd (Functor.F₀ F* Rs) → snd (Functor.F₀ F* Ss)

    -- Functor.F₁ F1 (vecmfst ms) : Functor.F₀ F1 (vecfst Rs) → Functor.F₀ F1 (vecfst Ss)
    -- Functor.F₁ F2 (vecmsnd ms) : Functor.F₀ F2 (vecsnd Rs) → Functor.F₀ F2 (vecsnd Ss)
    -- msnd (Functor.F₁ F* ms) : snd (Functor.F₀ F* Rs) → snd (Functor.F₀ F* Ss)
    -- mfst (Functor.F₁ F* ms) : fst (Functor.F₀ F* Rs) → fst (Functor.F₀ F* Ss)
-}



-- instead of asking for a functor of type [Rels^ k ,Rels] and then asserting
-- a bunch of (non-definitional) equalities, we can just ask for the minimal
-- pieces needed to define such a functor, and then define the functor
-- so that these equalities hold definitionally
record RTObj* {k : ℕ} (F1 F2 : Functor (Sets^ k) Sets) : Set₁ where
  open RelObj
  private module F1 = Functor F1
  private module F2 = Functor F2
  field
    -- all we need is the action on objects (relations)
    F*Rel : ∀ (Rs : Vec RelObj k) → REL (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))
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
        F1∘π₁ = (F1 ∘F Func^ Rels Sets π₁Rels k)
        F2∘π₂ : Functor (Rels^ k) Sets
        F2∘π₂ = (F2 ∘F Func^ Rels Sets π₂Rels k)
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
    F*Data : RTObj* F1 F2

  -- aliases for RTObj*Components
  F* : Functor (Rels^ k) Rels
  F* = RTObj*.F* F*Data

  F*Rel : ∀ (Rs : Vec RelObj k) → REL (Functor.₀ F1 (vecfst Rs)) (Functor.₀ F2 (vecsnd Rs))
  F*Rel = RTObj*.F*Rel F*Data



RTMorph-preserves : ∀ {k : ℕ} (H K : RTObj k)
               → (d1 : NaturalTransformation (RTObj.F1 H) (RTObj.F1 K))
               → (d2 : NaturalTransformation (RTObj.F2 H) (RTObj.F2 K))
               → (Rs : Vec RelObj k) → Set
RTMorph-preserves H K d1 d2 Rs =
          preservesRelObj (Functor.F₀ (RTObj.F* H) Rs)
                          (Functor.F₀ (RTObj.F* K) Rs)
                          (NaturalTransformation.η d1 (vecfst Rs))
                          (NaturalTransformation.η d2 (vecsnd Rs))

record RTMorph {k : ℕ} (H K : RTObj k) : Set₁ where
  constructor RTM[_,_,_]
  private module H = RTObj H
  private module K = RTObj K

  field
    d1 : NaturalTransformation H.F1 K.F1
    d2 : NaturalTransformation H.F2 K.F2

    -- d-preserves : ∀ {Rs : Vec RelObj k} → RTMorph-preserves H K d1 d2 Rs

    d-preserves : ∀ {Rs : Vec RelObj k} → preservesRelObj (Functor.F₀ H.F* Rs) (Functor.F₀ K.F* Rs)
                                     (NaturalTransformation.η d1 (vecfst Rs))
                                     (NaturalTransformation.η d2 (vecsnd Rs))




  -- we can define a natural transformation
  -- from H.F* to K.F* in terms of d1 and d2.
  -- Naturality follows componentwise from naturality of d1 and d2,
  -- and the fact that each component of d* preserves relations follows
  -- directly from d-preserves
  d* : NaturalTransformation (RTObj.F* H) (RTObj.F* K)
  d* = record { η = λ Rs → RM[ (NaturalTransformation.η d1 (vecfst Rs)) , (NaturalTransformation.η d2 (vecsnd Rs)) , d-preserves ]
              ; commute = λ fs → (NaturalTransformation.commute d1 (vecmfst fs)) , NaturalTransformation.commute d2 (vecmsnd fs)
              ; sym-commute = λ fs → ( (NaturalTransformation.sym-commute d1 (vecmfst fs))) , (NaturalTransformation.sym-commute d2 (vecmsnd fs))  }


idRTMorph : ∀ {k : ℕ} → (H : RTObj k) → RTMorph H H
-- idRTMorph {k} H = RTM[ idnat , idnat , (λ xy∈H*R → xy∈H*R) ]
idRTMorph {k} H = RTM[ idnat , idnat , idf ]

compose-RTMorph : ∀ {k} {J K L : RTObj k} → RTMorph K L → RTMorph J K → RTMorph J L
compose-RTMorph RTM[ f1 , f2 , f-resp ] RTM[ g1 , g2 , g-resp ] = RTM[ f1 ∘v g1 , f2 ∘v g2 , f-resp ∘' g-resp ]


RTMorph-≈ : ∀ {k} {H K : RTObj k} → (m m' : RTMorph H K) → Set₁
RTMorph-≈ {k} m m' = [Sets^ k ,Sets] [ RTMorph.d1 m ≈ RTMorph.d1 m' ]
                  ×' [Sets^ k ,Sets] [ RTMorph.d2 m ≈ RTMorph.d2 m' ]

RTMorph-≈-Equiv : ∀ {k} {A B : RTObj k} → IsEquivalence (RTMorph-≈ {k} {A} {B})
RTMorph-≈-Equiv = record { refl = ≡.refl , ≡.refl ; sym = λ { (p1 , p2)  → ≡.sym p1 , ≡.sym p2  } ; trans = λ { (p1 , p2) (r1 , r2) → (≡.trans p1 r1) , (≡.trans p2 r2) }  }


RTCat : ℕ → Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
RTCat k =  record
  { Obj = RTObj k
  ; _⇒_ = RTMorph
  ; _≈_ = λ m m' → [Sets^ k ,Sets] [ RTMorph.d1 m ≈ RTMorph.d1 m' ]
                ×' [Sets^ k ,Sets] [ RTMorph.d2 m ≈ RTMorph.d2 m' ]
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




open import Categories.Object.Terminal
RT-Terminal : ∀ (k : ℕ) → Terminal (RTCat k)
RT-Terminal k = record { ⊤ = RT[ (ConstF ⊤) , (ConstF ⊤) , (record { F*Rel = λ Rs x y → ⊤ ; F*Rel-preserves = λ ms _ → tt }) ]
                ; ⊤-is-terminal = record { ! = RTM[ !⇒K⊤ , !⇒K⊤ , (λ _ → tt) ]
                                         ; !-unique = λ f → ≡.refl , ≡.refl } }


π₁RT : ∀ {k} → Functor (RTCat k) [Sets^ k ,Sets]
π₁RT {k} = record
             { F₀ = RTObj.F1
             ; F₁ = RTMorph.d1
             ; identity = ≡.refl
             ; homomorphism = ≡.refl
             ; F-resp-≈ = λ { (f1≈g1 , _) → f1≈g1 }
             }

π₂RT : ∀ {k} → Functor (RTCat k) [Sets^ k ,Sets]
π₂RT {k} = record
             { F₀ = RTObj.F2
             ; F₁ = RTMorph.d2
             ; identity = ≡.refl
             ; homomorphism = ≡.refl
             ; F-resp-≈ = λ { (_ , f2≈g2) → f2≈g2 }
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

evalRT : ∀ {k} → Functor (Product (RTCat k) (Rels^ k)) Rels
evalRT {k} = eval ∘F (embedRT ⁂ idF)

open 0Functors Rels
embedRT0 : Functor (RTCat 0) Rels
embedRT0 = 0Functors⇒C ∘F embedRT


-- ConstRT : RelObj → RTObj 0
-- previously called RelObjtoRT0
ConstRT : RelObj → RTObj 0
ConstRT R[ A , B , R ] = RT[ ConstF A , ConstF B , record { F*Rel = λ _ → R ; F*Rel-preserves = λ ms xy∈R → xy∈R } ]

RelMorphtoRTM0 : ∀ {R S : RelObj} → RelMorph R S → RTMorph (ConstRT R)  (ConstRT S)
RelMorphtoRTM0 RM[ f1 , f2 , fp ] = RTM[ (ConstNat f1) , (ConstNat f2) , fp ]

Rels⇒RT0 : Functor Rels (RTCat 0)
Rels⇒RT0 = record
             { F₀ = ConstRT
             ; F₁ = RelMorphtoRTM0
             ; identity = ≡.refl , ≡.refl
             ; homomorphism = ≡.refl , ≡.refl
             ; F-resp-≈ = λ { (f1≈g1 , f2≈g2) → f1≈g1 , f2≈g2  }
             }

RelMorph-preserves-nat : ∀ {k} (F1 F2 : Functor (Sets^ k) Sets) (F* : Functor (Rels^ k) Rels)
                       → (η1 : NaturalTransformation (F1 ∘F π₁Vec k) (π₁Rels ∘F F*))
                       → (η2 : NaturalTransformation (F2 ∘F π₂Vec k) (π₂Rels ∘F F*))
                       → ∀ (Rs Ss : Vec RelObj k) (ms : (Rels^ k) [ Rs , Ss ])
                       → preservesRel (λ x y → rel (Functor.F₀ F* Rs) (NaturalTransformation.η η1 Rs x) (NaturalTransformation.η η2 Rs y))
                                      (λ x y → rel (Functor.F₀ F* Ss) (NaturalTransformation.η η1 Ss x) (NaturalTransformation.η η2 Ss y))
                                      (Functor.F₁ F1 (vecmfst ms))
                                      (Functor.F₁ F2 (vecmsnd ms))
RelMorph-preserves-nat F1 F2 F* η1 η2 Rs Ss ms {x} {y} xy∈F*Rs =
  let
      F*ms = Functor.F₁ F* ms
      F*ms-p : preservesRelObj (Functor.F₀ F* Rs) (Functor.F₀ F* Ss)
                               (mfst (Functor.F₁ F* ms))
                               (msnd (Functor.F₁ F* ms))
      F*ms-p = RelMorph.preserves F*ms

      F*ms-x,y : rel (Functor.F₀ F* Ss) (mfst (Functor.F₁ F* ms) (NaturalTransformation.η η1 Rs x))
                                        (msnd (Functor.F₁ F* ms) (NaturalTransformation.η η2 Rs y))
      F*ms-x,y = F*ms-p {NaturalTransformation.η η1 Rs x} {NaturalTransformation.η η2 Rs y} xy∈F*Rs

      F*Rs = Functor.F₀ F* Rs
      F*Ss = Functor.F₀ F* Ss

      com1 : Sets [ mfst F*ms ∘' NaturalTransformation.η η1 Rs
                  ≈ NaturalTransformation.η η1 Ss ∘' Functor.F₁ F1 (vecmfst ms) ]
      com1 = NaturalTransformation.sym-commute η1 ms

      com2 : Sets [ msnd F*ms ∘' NaturalTransformation.η η2 Rs
                  ≈ NaturalTransformation.η η2 Ss ∘' Functor.F₁ F2 (vecmsnd ms) ]
      com2 = NaturalTransformation.sym-commute η2 ms

      -- Goal: rel (Functor.F₀ F* Rs)
      --       (NaturalTransformation.η η1 Rs x)
      --       (NaturalTransformation.η η2 Rs y) →
      --       rel (Functor.F₀ F* Ss)
      --       (NaturalTransformation.η η1 Ss (Functor.F₁ F1 (vecmfst ms) x))
      --       (NaturalTransformation.η η2 Ss (Functor.F₁ F2 (vecmsnd ms) y))
  in  ≡.subst₂ (rel (Functor.F₀ F* Ss)) com1 com2 F*ms-x,y





-- To express the higher-order natural transformation we need here,
-- we need precomposition and postcomposition functors that go between functor categories...

open import CatUtils
-- precomp-F  : (F : Functor D E) → Functor (Functors C D) (Functors C E)
-- postcomp-F :  (F : Functor C D) → Functor (Functors D E) (Functors C E)
--
-- H1 ∘F π₁RT : RTCat k → [Sets^ k ,Sets]
--
-- π₁Vec k : Rels^k → Sets^k
-- postcomp-F (π₁Vec k) : [Sets^ k ,Sets] → [Rels^ k ,Sets]
-- postcomp-F (π₁Vec k) ∘F H1 ∘F π₁RT  : RTCat k → [Rels^ k ,Set]
--
-- precomp-F π₁Rels : [Rels^ k ,Rels] → [Sets^ k ,Sets]
--
RelMorph-preserves-hnat : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (H* : Functor (RTCat k) [Rels^ k ,Rels])
                          → (hη1 : NaturalTransformation (postcomp-F (π₁Vec k) ∘F H1 ∘F π₁RT) (precomp-F π₁Rels ∘F H*))
                          → (hη2 : NaturalTransformation (postcomp-F (π₂Vec k) ∘F H2 ∘F π₂RT) (precomp-F π₂Rels ∘F H*))
                          → ∀ (Rt St : RTObj k) (m : RTMorph Rt St) (Rs : Vec RelObj k)
                          → preservesRel (λ x y → rel (Functor.F₀ (Functor.F₀ H* Rt) Rs)
                                                (NaturalTransformation.η (NaturalTransformation.η hη1 Rt) Rs x) (NaturalTransformation.η (NaturalTransformation.η hη2 Rt) Rs y))
                                         (λ x y → rel (Functor.F₀ (Functor.F₀ H* St) Rs)
                                                (NaturalTransformation.η (NaturalTransformation.η hη1 St) Rs x) (NaturalTransformation.η (NaturalTransformation.η hη2 St) Rs y))
                                            (NaturalTransformation.η (Functor.F₁ H1 (RTMorph.d1 m)) (vecfst Rs))
                                            (NaturalTransformation.η (Functor.F₁ H2 (RTMorph.d2 m)) (vecsnd Rs))
RelMorph-preserves-hnat {k} H1 H2 H* hη1 hη2 Rt St m Rs {x} {y} η1RtRsx,η2RtRsy∈H*RtRs =
  let H*m : NaturalTransformation (Functor.F₀ H* Rt) (Functor.F₀ H* St)
      H*m = Functor.F₁ H* m

      η1 : (Rt : RTObj k) → NaturalTransformation ((Functor.F₀ H1 (RTObj.F1 Rt)) ∘F π₁Vec k) (π₁Rels ∘F (Functor.F₀ H* Rt))
      η1 = NaturalTransformation.η hη1

      η2 : (Rt : RTObj k) → NaturalTransformation ((Functor.F₀ H2 (RTObj.F2 Rt)) ∘F π₂Vec k) (π₂Rels ∘F (Functor.F₀ H* Rt))
      η2 = NaturalTransformation.η hη2

      H*m-Rs : RelMorph (Functor.F₀ (Functor.F₀ H* Rt) Rs) (Functor.F₀ (Functor.F₀ H* St) Rs)
      H*m-Rs = NaturalTransformation.η H*m Rs

      H*St-Rs : RelObj
      H*St-Rs = Functor.F₀ (Functor.F₀ H* St) Rs

      H*m-Rs-pr : preservesRelObj (Functor.F₀ (Functor.F₀ H* Rt) Rs) (Functor.F₀ (Functor.F₀ H* St) Rs)
                                  (mfst H*m-Rs) (msnd H*m-Rs)
      H*m-Rs-pr = RelMorph.preserves H*m-Rs

      η1RtRs = NaturalTransformation.η (η1 Rt) Rs
      η1StRs = NaturalTransformation.η (η1 St) Rs

      η2RtRs = NaturalTransformation.η (η2 Rt) Rs
      η2StRs = NaturalTransformation.η (η2 St) Rs

      p : rel (Functor.F₀ (Functor.F₀ H* St) Rs)
            (mfst (NaturalTransformation.η (Functor.F₁ H* m) Rs) (NaturalTransformation.η (η1 Rt) Rs x))
            (msnd (NaturalTransformation.η (Functor.F₁ H* m) Rs) (NaturalTransformation.η (η2 Rt) Rs y))
      p = H*m-Rs-pr {η1RtRs x} {η2RtRs y} η1RtRsx,η2RtRsy∈H*RtRs

      com1 : Sets [
             mfst (NaturalTransformation.η (Functor.F₁ H* m) Rs) ∘' NaturalTransformation.η (η1 Rt) Rs
           ≈ NaturalTransformation.η (η1 St) Rs ∘' NaturalTransformation.η (Functor.F₁ H1 (RTMorph.d1 m)) (vecfst Rs)
             ]
      com1 = NaturalTransformation.sym-commute hη1 m

      com2 : Sets [
             msnd (NaturalTransformation.η (Functor.F₁ H* m) Rs) ∘' NaturalTransformation.η (η2 Rt) Rs
           ≈ NaturalTransformation.η (η2 St) Rs ∘' NaturalTransformation.η (Functor.F₁ H2 (RTMorph.d2 m)) (vecsnd Rs)
             ]
      com2 = NaturalTransformation.sym-commute hη2 m

   in ≡.subst₂ (rel H*St-Rs) com1 com2 p




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
    -- an element of RelSet but we don't care about p when comparing two elements of RelSet for equality
    .p : x , y ∈ rel R


module TestRelSet where
    -- example relation and its RelSet
    data lesseq : ℕ →  ℕ → Set where
        lz : ∀ n   → lesseq 0 n
        ls : ∀ n m → lesseq n m → lesseq n (suc m)

    lesseqRel : RelObj
    lesseqRel = R[ ℕ , ℕ , lesseq ]

    lesseqSet : Set
    lesseqSet = RelSet lesseqRel

    lesseqS : lesseqSet
    lesseqS = RI[ 0 , 1 , (lz 1) ]

    -- we can put an underscore for third component
    -- (which might suggest the irrelevant p field is breaking something)
    lesseqS' : lesseqSet
    lesseqS' = RI[ 1 , 0 , _ ]

    -- but we can do that anyways for regular relations (with no irrelevance)
    lesseqS'' : 1 , 0 ∈ lesseq
    lesseqS'' = _


-- note dot (.) preceding p and p' for irrelevance.
-- Since these arguments are irrelevant, and the p field of RelSet is irrelevant,
-- the values of p and p' are never checked (just their types) and we can say RI[x , y , p ] ≡ RI[ x' , y' , p' ]
-- as long as x ≡ x and y ≡ y'
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

RelUProd⇒π₁ : NaturalTransformation RelUProdF π₁Rels
RelUProd⇒π₁ = ntHelper (record { η = λ R → proj₁ ;  commute = λ f → ≡.refl })

RelUProd⇒π₂ : NaturalTransformation RelUProdF π₂Rels
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


    factor-subset : ∀ {A B C : Set} → (f : A → B ×' C) → REL B C
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
    h-A×B-R Rs = < F₁ (vmap-foreach RelUProdF π₁Rels RelUProd⇒π₁ Rs) , F₁ ( (vmap-foreach RelUProdF π₂Rels  RelUProd⇒π₂ Rs)) >

    vmap-incl : ∀ (Rs : Vec RelObj k) → Sets^ k [ vmap RelSet Rs , vmap RelUProd Rs ]
    vmap-incl = vmap-foreach RelSetF RelUProdF inclNat

    -- Goal: Sets^ k [ vmap RelSet Rs , vmap (λ R → fst R × snd R) Rs ]
    Fincl :  ∀ (Rs : Vec RelObj k)
            → F₀ (vmap RelSet Rs) → F₀ (vmap RelUProd Rs)
    Fincl Rs FRs = F₁ ( vmap-incl Rs ) FRs

    idRT** : ∀ (Rs : Category.Obj (Rels^ k)) → REL (F₀ (vecfst Rs)) (F₀ (vecsnd Rs))
    idRT** Rs = factor-subset {A = F₀ (vmap RelSet Rs)} (h-A×B-R Rs ∘' Fincl Rs)

    idRT**-preserves : ∀ {Rs Ss : Vec RelObj k} (ms : Rels^ k [ Rs , Ss ])
                       → preservesRel (idRT** Rs) (idRT** Ss) (Functor.₁ F (vecmfst ms))
                                                              (Functor.₁ F (vecmsnd ms))
    idRT**-preserves {Rs} {Ss} ms {x} {y} (F-SetRs , h∘Fincl-Rs≡x,y ) =
      let map-ms : F₀ (vmap RelSet Rs) → F₀ (vmap RelSet Ss)
          map-ms = F₁ (Functor.F₁ (Func^ Rels Sets RelSetF k) ms)

          vmapfst = vmap-foreach RelUProdF π₁Rels RelUProd⇒π₁
          vmapsnd  = vmap-foreach RelUProdF π₂Rels RelUProd⇒π₂

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
          com1 = vmap-foreach-commute RelUProdF π₁Rels RelUProd⇒π₁ ms

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
                        ≈⟨  vmap-foreach-commute RelUProdF π₂Rels RelUProd⇒π₂ ms ⟩∘⟨refl ⟩
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

    idRT*Components : RTObj* F F
    idRT*Components = record { F*Rel = idRT** ; F*Rel-preserves = idRT**-preserves }

    idRT : RTObj k
    idRT = RT[ F , F , idRT*Components  ]

open Identities


EqRT-resp : ∀ {k} {F G : Category.Obj [Sets^ k ,Sets]}
                   → (η : [Sets^ k ,Sets] [ F , G ])
                   → {Rs : Vec RelObj k}
                   → RTMorph-preserves (idRT F) (idRT G) η η Rs
EqRT-resp {k} {F} {G} η {Rs} {x} {y} (F*Rs , hF*Rs≡x,y) =
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


EqRT : ∀ {k} → Functor [Sets^ k ,Sets] (RTCat k)
EqRT = record
                { F₀ = λ F → idRT F
                ; F₁ = λ η → RTM[ η , η , EqRT-resp η ]
                ; identity = ≡.refl , ≡.refl
                ; homomorphism = ≡.refl , ≡.refl
                ; F-resp-≈ = λ f≈g → f≈g , f≈g
                }


-- proof that equality relation transformer for a set (0-ary functor)
-- gives equality relation on the set
EqRT0 : ∀ (X : Set) (x x' : X) → RTObj*.F*Rel (idRT*Components (ConstF X)) [] x x' → x ≡ x'
EqRT0 X x .x (.x , ≡.refl) = ≡.refl

EqRT0' : ∀ (X : Set) (x x' : X) → x ≡ x' → RTObj*.F*Rel (idRT*Components (ConstF X)) [] x x'
EqRT0' X x .x ≡.refl = x , ≡.refl


{-
open ≡.≡-Reasoning
EqRTEq : ∀ {A : Set}
         → (F : Functor (Sets^ 1) Sets)
         → (x x' : Functor.F₀ F (A ∷ []))
         → RTObj*.F*Rel (idRT*Components F) (EqRelObj A ∷ []) x  x'
         → x ≡ x'
-- EqRTEq F x x' (fst₁ , ≡.refl) = {!!}
EqRTEq {A} F .(Functor.F₁ F (proj₁ , bigtt) (Functor.F₁ F (incl R[ A , A , _ ] , bigtt) fst₁)) .(Functor.F₁ F (proj₂ , bigtt) (Functor.F₁ F (incl R[ A , A , _ ] , bigtt) fst₁)) (fst₁ , ≡.refl) =

  begin Functor.F₁ F (proj₁ , bigtt) (Functor.F₁ F (incl _ , bigtt) fst₁)
        ≡⟨ ≡.sym (Functor.homomorphism F)  ⟩
        Functor.F₁ F ((proj₁ ∘' incl _ , bigtt)) fst₁
        ≡⟨ Functor.F-resp-≈  F ((λ { {RI[ x , y , p ]} → {!!} } ) , bigtt)  ⟩
        Functor.F₁ F ((proj₂ ∘' incl _ , bigtt)) fst₁
        ≡⟨ Functor.homomorphism F ⟩
        Functor.F₁ F (proj₂ , bigtt) (Functor.F₁ F (incl _ , bigtt) fst₁) ∎
-- Goal: Functor.F₁ F (proj₁ , bigtt) (Functor.F₁ F (incl _ , bigtt) fst₁)
--       ≡ Functor.F₁ F (proj₂ , bigtt) (Functor.F₁ F (incl _ , bigtt) fst₁)

-}
-- EqRTEq F .(Functor.F₁ F (proj₁ , bigtt) (Functor.F₁ F (incl _ , bigtt) fst₁)) .(Functor.F₁ F (proj₂ , bigtt) (Functor.F₁ F (incl _ , bigtt) fst₁)) (fst₁ , ≡.refl) = {!!}

module PolynomialRels where

    open import Categories.Object.Terminal
    open import Categories.Object.Initial

    -- first we have the actual relations (subsets) for initial and terminal relation
    REL⊤ : REL ⊤ ⊤
    REL⊤ _ _ = ⊤

    Rel⊤ : RelObj
    Rel⊤ = R[ ⊤ , ⊤ , REL⊤ ]

    Rel⊤! : ∀ {R : RelObj} → RelMorph R Rel⊤
    Rel⊤! = RM[ const tt , const tt , const tt ]

    Rel⊤-IsTerminal : IsTerminal Rels Rel⊤
    Rel⊤-IsTerminal = record { ! = Rel⊤! ; !-unique = λ _ → ≡.refl , ≡.refl }

    RelTerminal : Terminal Rels
    RelTerminal = record { ⊤ = Rel⊤ ; ⊤-is-terminal = Rel⊤-IsTerminal }

    -- there are two possible choices to define initial relation
    -- either the constantly false relation
    Rel⊥0 : REL ⊥ ⊥
    Rel⊥0 _ _ = ⊥

    -- or we can use bottom-elimination (absurd pattern)
    Rel⊥0-elim : REL ⊥ ⊥
    Rel⊥0-elim ()

    Rel⊥ : RelObj
    Rel⊥ = R[ ⊥ , ⊥ , Rel⊥0 ]

    Rel⊥! : ∀ {R : RelObj} → RelMorph Rel⊥ R
    Rel⊥! = RM[ exFalso , exFalso , (λ()) ]

    Rel⊥-IsInitial : IsInitial Rels Rel⊥
    Rel⊥-IsInitial = record { ! = Rel⊥! ; !-unique = λ _ → (λ { {()} }) , (λ { {()} })  }

    RelInitial : Initial Rels
    RelInitial = record { ⊥ = Rel⊥ ; ⊥-is-initial = Rel⊥-IsInitial }

    _×REL_ : ∀ {A B A' B' : Set} → REL A B → REL A' B' → REL (A ×' A') (B ×' B')
    (R0 ×REL S0) (x , x') (y , y') = R0 x y ×'  S0 x' y'

    _×Rel_ : RelObj → RelObj → RelObj
    R ×Rel S = R[ (fst R ×' fst S) , (snd R ×' snd S) , (rel R ×REL rel S) ]

    -- sum of REL objects
    _+REL_ : ∀ {A B A' B' : Set} → REL A B → REL A' B' → REL (A ⊎ A') (B ⊎ B')
    (R0 +REL S0) (inj₁ x) (inj₁ y) = R0 x y
    -- (R0 +REL S0) (inj₁ x) (inj₂ y) = {!!}
    -- (R0 +REL S0) (inj₂ y) (inj₁ x) = {!!}
    (R0 +REL S0) (inj₂ x') (inj₂ y') = S0 x' y'
    {-# CATCHALL #-}
    (R0 +REL S0) _ _ = ⊥

    -- sum of RelObj objects
    _+Rel_ : RelObj → RelObj → RelObj
    R +Rel S = R[ (fst R ⊎ fst S) , (snd R ⊎ snd S) , (rel R +REL rel S) ]

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
  private module H1 = Functor H1
  private module H2 = Functor H2
  open RelObj
  field

    -- compared to lmcs paper, this is action on objects of action on objects of H*
    -- given in first implicit bullet point
    H*RTRel : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
              → REL (Functor.F₀ (H1.₀ (RTObj.F1 Rt)) (vecfst Rs))
                    (Functor.F₀ (H2.₀ (RTObj.F2 Rt)) (vecsnd Rs))

    -- second 'implicit' bullet point after definition 3.6
    H*RTRel-preserves : ∀ (Rt : RTObj k) → {Rs Ss : Vec RelObj k}
                        → (ms : Rels^ k [ Rs , Ss ])
                        → preservesRel (H*RTRel Rt Rs) (H*RTRel Rt Ss)
                            (Functor.F₁ (H1.₀ (RTObj.F1 Rt)) (vecmfst ms))
                            (Functor.F₁ (H2.₀ (RTObj.F2 Rt)) (vecmsnd ms))

    -- third 'implicit' bullet point after definition 3.6
    H*RT-preserves : ∀ {Rt St : RTObj k} (m : RTMorph Rt St) → {Rs : Vec RelObj k}
                        → preservesRel (H*RTRel Rt Rs) (H*RTRel St Rs)
                            (NaturalTransformation.η (H1.₁ (RTMorph.d1 m)) (vecfst Rs))
                            (NaturalTransformation.η (H2.₁ (RTMorph.d2 m)) (vecsnd Rs))



  -- end fields --

  -- action of HRT on objects (relation transformers)

  H*Obj : ∀ (Rt : RTObj k) → Functor (Rels^ k) Rels
  H*Obj Rt@(RT[ F1 , F2 , _ ]) =
        RTObj.F* (RT[ H1.₀ F1
                   , H2.₀ F2
                   , record { F*Rel = H*RTRel Rt ; F*Rel-preserves = H*RTRel-preserves Rt } ])


  H*-map-component : ∀ {Rt St : RTObj k} → (d : RTMorph Rt St)
                     → (Rs : Vec RelObj k)
                     → RelMorph (Functor.F₀ (H*Obj Rt) Rs) (Functor.F₀ (H*Obj St) Rs)
  H*-map-component d@(RTM[ d1 , d2 , d-preserves ]) Rs =
    RM[ (NaturalTransformation.η (H1.₁ d1) (vecfst Rs))
      , (NaturalTransformation.η (H2.₁ d2) (vecsnd Rs))
      , H*RT-preserves d ]

  H*-map-commutes : ∀ {Rt St : RTObj k} → (d : RTMorph Rt St)
                    → {Rs Ss : Vec RelObj k}
                    → (fs : (Rels^ k) [ Rs , Ss ])
                    → Rels [ H*-map-component d Ss ∘RelM (Functor.F₁ (H*Obj Rt) fs)
                           ≈ Functor.F₁ (H*Obj St) fs ∘RelM H*-map-component d Rs ]
  H*-map-commutes RTM[ d1 , d2 , _ ] fs =
                  NaturalTransformation.commute (H1.₁ d1) (vecmfst fs)
                , NaturalTransformation.commute (H2.₁ d2) (vecmsnd fs)

  -- action of HRT on morphisms of relation transformers
  H*-map : ∀ {Rt St : RTObj k}
           → (d : RTMorph Rt St)
           → [Rels^ k ,Rels] [ H*Obj Rt , H*Obj St ]
  H*-map {Rt} d =
    record { η           = λ Rs → H*-map-component d Rs
           ; commute     = λ fs → H*-map-commutes d fs
           ; sym-commute = λ fs → Category.Equiv.sym Rels (H*-map-commutes d fs) }

  -- -- third bullet in Definition 3.6 of lmcs
  -- these data yield a functor from RT to [Rels^ k ,Rels]
  H* : Functor (RTCat k) [Rels^ k ,Rels]
  H* = record
         { F₀ = λ Rt → H*Obj Rt
         ; F₁ = λ {Rt} {St} d → H*-map d
         ; identity = (Functor.identity H1) , (Functor.identity H2)
         ; homomorphism = (Functor.homomorphism H1) , (Functor.homomorphism H2)
         ; F-resp-≈ = λ (f1≈g1 , f2≈g2) → (Functor.F-resp-≈ H1 f1≈g1) , (Functor.F-resp-≈ H2 f2≈g2)
         }





record HRTObj (k : ℕ) : Set₁ where
  constructor HRT[_,_,_]
  field
    H1 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
    H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]

    H*Data : HRTObj* H1 H2
  -- end fields

  private module H1 = Functor H1
  private module H2 = Functor H2

  open HRTObj* H*Data
  open HRTObj* H*Data using (H*) public -- export H* field

  HEndo-rel* : ∀ (Rt : RTObj k) → RTObj* (H1.₀ (RTObj.F1 Rt)) (H2.₀ (RTObj.F2 Rt))
  HEndo-rel* Rt = record { F*Rel = H*RTRel Rt
                         ; F*Rel-preserves = H*RTRel-preserves Rt }

  -- fourth bullet of HRT def
  HEndo-obj : ∀ (Rt : RTObj k) → RTObj k
  HEndo-obj Rt@(RT[ F1 , F2 , _ ]) = RT[ (H1.₀ F1) , (H2.₀ F2) , HEndo-rel* Rt ]

  -- fifth bullet of HRT def
  HEndo-map : ∀ {Rt St : RTObj k} (d : RTMorph Rt St) → RTMorph (HEndo-obj Rt) (HEndo-obj St)
  HEndo-map d@(RTM[ d1 , d2 , _ ]) = RTM[ (H1.₁ d1) , (H2.₁ d2) , H*RT-preserves d ]

  HEndo : Functor (RTCat k) (RTCat k)
  HEndo = record
            { F₀ = λ Rt → HEndo-obj Rt
            ; F₁ = HEndo-map
            ; identity = (Functor.identity H1) , (Functor.identity H2)
            ; homomorphism = (Functor.homomorphism H1) , (Functor.homomorphism H2)
            ; F-resp-≈ = λ { (f1≈g1 , f2≈g2) → Functor.F-resp-≈ H1 f1≈g1 , Functor.F-resp-≈ H2 f2≈g2 }
            }


{- this uses subst and equalities.. maybe we just need a natural transformation or morphisms ...
-- what do we need to know about H* to make HRTObj* ?
make-HRTObj* : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
               → (H* : Functor (RTCat k) [Rels^ k ,Rels])
               → HRTObj* H1 H2
make-HRTObj* {k} H1 H2 H* =
  let H*Rel : RTObj k → Vec RelObj k → RelObj
      H*Rel Rt Rs = Functor.F₀ (Functor.F₀ H* Rt) Rs

      rm : ∀ (Rt : RTObj k) {Rs Ss : Vec RelObj k} (ms : (Rels^ k) [ Rs , Ss ])
           → RelMorph (H*Rel Rt Rs) (H*Rel Rt Ss)
      rm Rt ms = Functor.F₁ (Functor.F₀ H* Rt) ms

      p1' : ∀ (Rt : RTObj k) {Rs Ss : Vec RelObj k} (ms : (Rels^ k) [ Rs , Ss ])
            → ∀ {x} {y}
            → x Het.≅ y
            → (Functor.F₁ (Functor.₀ H1 (RTObj.F1 Rt)) (vecmfst ms) x)
            Het.≅ (mfst (Functor.F₁ (Functor.F₀ H* Rt) ms) y)
      p1' = {!!}

--       (Functor.F₁ (Functor.₀ H2 (RTObj.F2 Rt)) (vecmsnd ms) y)
-- Have: preservesRelObj (Functor.F₀ (Functor.F₀ H* Rt) Rs)
--       (Functor.F₀ (Functor.F₀ H* Rt) Ss)
--       (mfst (Functor.F₁ (Functor.F₀ H* Rt) ms))
--       (msnd (Functor.F₁ (Functor.F₀ H* Rt) ms))

      p1 : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
           → (fst (Functor.F₀ (Functor.F₀ H* Rt) Rs))
           ≡ (Functor.F₀ (Functor.F₀ H1 (RTObj.F1 Rt)) (vecfst Rs))
      p1 = {!!}


      p2 : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
           → (snd (Functor.F₀ (Functor.F₀ H* Rt) Rs))
           ≡ (Functor.F₀ (Functor.F₀ H2 (RTObj.F2 Rt)) (vecsnd Rs))
      p2 = {!!}

  in
  record { H*RTRel = λ Rt Rs → ≡.subst₂ REL (p1 Rt Rs) (p2 Rt Rs) (rel (H*Rel Rt Rs))
        -- Goal: REL (Functor.F₀ (Functor.F₀ H1 (RTObj.F1 Rt)) (vecfst Rs))
        --            (Functor.F₀ (Functor.F₀ H2 (RTObj.F2 Rt)) (vecsnd Rs))
        -- Have: REL (fst (Functor.F₀ (Functor.F₀ H* Rt) Rs))
        --            (snd (Functor.F₀ (Functor.F₀ H* Rt) Rs))
         ; H*RTRel-preserves = λ Rt {Rs} {Ss} ms {x} {y} p → {! RelMorph.preserves (rm Rt ms)   !}
         ; H*RT-preserves = {!!} }
-}


-- construct HRT from H1, H2, H* and some natural transformations
module make-HRT {k : ℕ}
    (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
    (H* : Functor (RTCat k) [Rels^ k ,Rels])
    (hη1 : NaturalTransformation (postcomp-F (π₁Vec k) ∘F H1 ∘F π₁RT) (precomp-F π₁Rels ∘F H*))
    (hη2 : NaturalTransformation (postcomp-F (π₂Vec k) ∘F H2 ∘F π₂RT) (precomp-F π₂Rels ∘F H*))
    where

    private module H* = Functor H*
    private module H1 = Functor H1
    private module H2 = Functor H2


    η1 : (Rt : RTObj k) → NaturalTransformation ((Functor.F₀ H1 (RTObj.F1 Rt)) ∘F π₁Vec k) (π₁Rels ∘F (Functor.F₀ H* Rt))
    η1 = NaturalTransformation.η hη1

    η2 : (Rt : RTObj k) → NaturalTransformation ((Functor.F₀ H2 (RTObj.F2 Rt)) ∘F π₂Vec k) (π₂Rels ∘F (Functor.F₀ H* Rt))
    η2 = NaturalTransformation.η hη2


    H*Rel : RTObj k → Vec RelObj k → RelObj
    H*Rel Rt Rs = Functor.F₀ (Functor.F₀ H* Rt) Rs

    rm : ∀ (Rt : RTObj k) {Rs Ss : Vec RelObj k} (ms : (Rels^ k) [ Rs , Ss ])
            → RelMorph (H*Rel Rt Rs) (H*Rel Rt Ss)
    rm Rt ms = Functor.F₁ (Functor.F₀ H* Rt) ms

    f1 : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
         → (Functor.F₀ (H1.₀ (RTObj.F1 Rt)) (vecfst Rs))
         → (fst (Functor.F₀ (H*.₀ Rt) Rs))
    f1 Rt Rs = NaturalTransformation.η (η1 Rt) Rs


    f2 : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
         → (Functor.F₀ (H2.₀ (RTObj.F2 Rt)) (vecsnd Rs))
         → (snd (Functor.F₀ (H*.₀ Rt) Rs))
    f2 Rt Rs = NaturalTransformation.η (η2 Rt) Rs

    H1F1 : ∀ (Rt : RTObj k) → Functor (Sets^ k) Sets
    H1F1 Rt = H1.₀ (RTObj.F1 Rt)
    H2F2 : ∀ (Rt : RTObj k) → Functor (Sets^ k) Sets
    H2F2 Rt = H2.₀ (RTObj.F2 Rt)

    make-HRTObj* : HRTObj* H1 H2
    make-HRTObj* =
      record { H*RTRel = λ Rt Rs x y → rel (H*Rel Rt Rs) (f1 Rt Rs x) (f2 Rt Rs y)
             ; H*RTRel-preserves = λ Rt {Rs} {Ss} ms → RelMorph-preserves-nat (H1F1 Rt) (H2F2 Rt) (H*.₀ Rt) (η1 Rt) (η2 Rt) Rs Ss ms
             ; H*RT-preserves = λ {Rt} {St} RTm {Rs} → RelMorph-preserves-hnat H1 H2 H* hη1 hη2 Rt St RTm Rs   }

    make-HRTObj : HRTObj k
    make-HRTObj = HRT[ H1 , H2 , make-HRTObj* ]



open make-HRT



record HRTMorph {k : ℕ} (H K : HRTObj k) : Set₁ where
  constructor HRTM[_,_,_]
  module H = HRTObj H
  module K = HRTObj K

  open H using (H* ; H1 ; H2)
  open K renaming (H* to K* ; H1 to K1 ; H2 to K2)

  field
    σ1 : NaturalTransformation H1 K1
    σ2 : NaturalTransformation H2 K2

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
  σRT-commute {Rt} {St} d@(RTM[ d1 , d2 , d-preserves ]) =
              NaturalTransformation.commute σ1 d1 , NaturalTransformation.commute σ2 d2

  σRT : NaturalTransformation H.H* K.H*
  σRT = ntHelper (record { η = σRT-component  ; commute = σRT-commute })



idHRTMorph : ∀ {k : ℕ} {H : HRTObj k} → HRTMorph H H
idHRTMorph {H} = HRTM[ idnat , idnat , (λ Rt Rs → idf) ]

-- record { σ1 = idnat ; σ2 = idnat ; σ-preserves = λ Rt Rs xy∈H*Rt-Rs → xy∈H*Rt-Rs }


composeHRTMorph : ∀ {k} {H K L : HRTObj k} →
                  HRTMorph K L → HRTMorph H K → HRTMorph H L
composeHRTMorph HRTM[ σ1 , σ2 , σ-preserves ] HRTM[ σ1' , σ2' , σ'-preserves ]
                = HRTM[ (σ1 ∘v σ1') , (σ2 ∘v σ2') , (λ Rt Rs xy∈HRtRs → σ-preserves Rt Rs (σ'-preserves Rt Rs xy∈HRtRs)) ]



HRTCat : ℕ → Category (lsuc lzero) (lsuc lzero) (lsuc lzero)
HRTCat k = record
             { Obj = HRTObj k
             ; _⇒_ = HRTMorph
             ; _≈_ = λ {H} {K} m m' → (HRTMorph.σ1 m ≈ HRTMorph.σ1 m') ×'(HRTMorph.σ2 m ≈ HRTMorph.σ2 m')
             ; id = idHRTMorph
             ; _∘_ = composeHRTMorph
             -- HERE
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
             -- HERE
             }
             where open Category ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
                   open HRTMorph using (σ1 ; σ2)



HRTEndo-map-component : ∀ {k} {H K : HRTObj k} → HRTMorph H K
                        → (Rt : RTObj k)
                        → RTMorph (Functor.F₀ (HRTObj.HEndo H) Rt) (Functor.F₀ (HRTObj.HEndo K) Rt)
HRTEndo-map-component HRTM[ σ1 , σ2 , σ-preserves ] Rt@(RT[ F1 , F2 , F* ]) =
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

-- Goal: REL (Functor.F₀ (Functor.₀ π₁RT (Functor.₀ (H ∘F EqRT) (RTObj.F1 Rt))) (vecfst Rs))
--            (Functor.F₀ (Functor.₀ π₂RT (Functor.₀ (H ∘F EqRT) (RTObj.F2 Rt))) (vecsnd Rs))

    -- F*Rel : ∀ (Rs : Vec RelObj k) → REL (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))


-- normalized Goal: REL0
--   (Functor.F₀ (RTObj.F1 (Functor.F₀ H (idRT F1))) (vmap fst Rs))
--   (Functor.F₀ (RTObj.F2 (Functor.F₀ H (idRT F2))) (vmap snd Rs))


-- H1As : Functor.F₀ (RTObj.F1 (Functor.F₀ H RT[ RTObj.F1 Rt , RTObj.F1 Rt , idRT*Components (RTObj.F1 Rt) ])) (vmap fst Rs)
-- H2Bs : Functor.F₀ (RTObj.F2 (Functor.F₀ H RT[ RTObj.F2 Rt , RTObj.F2 Rt , idRT*Components (RTObj.F2 Rt) ])) (vmap snd Rs)


    -- H*RTRel : ∀ (Rt : RTObj k) (Rs : Vec RelObj k)
    --           → REL (Functor.F₀ (Functor.F₀ H1 (RTObj.F1 Rt)) (vecfst Rs))
    --                  (Functor.F₀ (Functor.F₀ H2 (RTObj.F2 Rt)) (vecsnd Rs))
    -- F*Rel-preserves : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ])
    --                   → preservesRel (F*Rel Rs) (F*Rel Ss) (F1.₁ (vecmfst ms)) (F2.₁ (vecmsnd ms))





toHRT-obj*Rel : ∀ {k} (H : Category.Obj [[ RTCat k , RTCat k ]])
                  (Rt : RTObj k) (Rs : Vec RelObj k)
                  → REL (Functor.F₀ (Functor.F₀ (π₁RT ∘F H ∘F EqRT) (RTObj.F1 Rt)) (vecfst Rs))
                         (Functor.F₀ (Functor.F₀ (π₂RT ∘F H ∘F EqRT) (RTObj.F2 Rt)) (vecsnd Rs))
toHRT-obj*Rel H Rt Rs x y =
  let
      HR1 : REL0
            (Functor.₀ (RTObj.F1 (Functor.₀ H (Functor.₀ EqRT (RTObj.F1 Rt)))) (vecfst Rs))
            (Functor.₀ (RTObj.F2 (Functor.₀ H (Functor.₀ EqRT (RTObj.F1 Rt)))) (vecsnd Rs))
      HR1 = RTObj.F*Rel (Functor.F₀ (H ∘F EqRT) (RTObj.F1 Rt)) Rs

      HR2 : REL0
            (Functor.₀ (RTObj.F1 (Functor.₀ H (Functor.₀ EqRT (RTObj.F2 Rt)))) (vecfst Rs))
            (Functor.₀ (RTObj.F2 (Functor.₀ H (Functor.₀ EqRT (RTObj.F2 Rt)))) (vecsnd Rs))
      HR2 = RTObj.F*Rel (Functor.F₀ (H ∘F EqRT) (RTObj.F2 Rt)) Rs
   in HR1 x {!!} ×' HR2 {!x!} y


toHRT-obj* : ∀ {k} (H : Category.Obj [[ RTCat k , RTCat k ]])
            → HRTObj* (π₁RT ∘F H ∘F EqRT) (π₂RT ∘F H ∘F EqRT)
toHRT-obj* {k} H = record { H*RTRel = λ Rt Rs → {!toHRT-obj*Rel H Rt Rs!}
-- RTObj*.F*Rel (RTObj.F*Data {!Functor.F₀ H Rt!}) Rs

-- HRTObj*.H*RTRel (HRTObj.H*Obj {!H!}) Rt Rs
-- RTObj*.F*Rel-preserves (record { F*Rel = {!!} ; F*Rel-preserves = {!!} }) {!!} {!!} {!!}
                        ; H*RTRel-preserves = {!!}
                        ; H*RT-preserves = {!!} }


toHRT-obj : ∀ {k} → Category.Obj [[ RTCat k , RTCat k ]] → HRTObj k
toHRT-obj {k} H = record { H1 = π₁RT ∘F H ∘F EqRT
                         ; H2 =  π₂RT ∘F H ∘F EqRT
                         ; H*Obj = {!!} }
                         -- toHRT-obj* H }


-- can we get back an HRT obj from an endofunctor on RT k ? not sure
toHRT : ∀ {k} → Functor ([[ RTCat k , RTCat k ]]) (HRTCat k)
toHRT {k} = record
              { F₀ = toHRT-obj
              ; F₁ = {!!}
              ; identity = {!!}
              ; homomorphism = {!!}
              ; F-resp-≈ = {!!}
              }



-}



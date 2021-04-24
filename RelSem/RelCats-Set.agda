{-# OPTIONS --allow-unsolved-metas --rewriting --confluence-check #-}
open import Agda.Builtin.Equality.Rewrite


open import Categories.Category 
open import Categories.Functor using (Functor ; Endofunctor ; _∘F_ )
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
open import Data.Vec using (Vec ; [] ; _∷_; replicate ; zipWith) renaming (map to vmap)
open import Data.Product renaming (_×_ to _×'_ ; map to ×'-map)
open import Data.Bool
open import SetCats 
open VecCat 


open import Utils

module RelSem.RelCats-Set where 


-- proof irrelevant relation
record IRREL0 (A B : Set) : Set₁ where 
  field 
    R : A → B → Set
    irrel : ∀ {x : A} {y : B} → (p p' : R x y) → p ≡ p'


-- want to be able to do
-- R : IRREL0 A B
--
-- R x y : Set 

-- proof relevant relation 
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
preservesRel R R' f g = ∀ {x y} → R x y → R' (f x) (g y)


preservesRel-comp : ∀ {A B A' B' A'' B'' : Set} → (R : REL0 A B) → (R' : REL0 A' B') → (R'' : REL0 A'' B'')
               → (f : A → A') → (g : B → B') → (f' : A' → A'') → (g' : B' → B'') 
               → preservesRel R R' f g
               → preservesRel R' R'' f' g'
               → preservesRel R R'' (f' ∘' f) (g' ∘' g)
preservesRel-comp R R' R'' f g f' g' pfg pf'g' = pf'g' ∘' pfg  


preservesRelObj : ∀ (R R' : RelObj)
               → (f : RelObj.fst R → RelObj.fst R') → (g : RelObj.snd R → RelObj.snd R') → Set 
preservesRelObj R R' f g = preservesRel (RelObj.rel R) (RelObj.rel R') f g 
-- ∀ {x y} →  (RelObj.rel R x y) →  (RelObj.rel R' (f x) (g y))

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



relPreservesEq : ∀ {A B A' B' : Set} → (R : REL0 A B) → (S : REL0 A' B')
                 → A ≡ A' → B ≡ B' → R Het.≅ S
                 → (f : A → A') → (g : B → B')
                 → preservesRel R S f g
                 → ∀ {x y} → R x y → S (f x) (g y)
relPreservesEq R .R ≡.refl ≡.refl Het.refl f g x,y∈R = x,y∈R

relObjPreservesEq : ∀ (R S R' S' : RelObj) → (m : RelMorph R S)
                    → (f1 : fst R' → fst S') → (f2 : snd R' → snd S')
                    → fst R ≡ fst R' → fst S ≡ fst S'
                    → snd R ≡ snd R' → snd S ≡ snd S'
                    → rel R Het.≅ rel R'
                    → rel S Het.≅ rel S' 
                    → mfst m Het.≅ f1 → msnd m Het.≅ f2
                    → RelMorph R' S' 
relObjPreservesEq R S R' S' m f1 f2 ≡.refl ≡.refl ≡.refl ≡.refl Het.refl Het.refl Het.refl Het.refl = m


relObjPreservesEq-ext : ∀ (R S R' S' : RelObj) → (m : RelMorph R S)
                    → (f1 : fst R' → fst S') → (f2 : snd R' → snd S')
                    → fst R ≡ fst R' → fst S ≡ fst S'
                    → snd R ≡ snd R' → snd S ≡ snd S'
                    → rel R Het.≅ rel R'
                    → rel S Het.≅ rel S' 
                    → (∀ {x y} → x Het.≅ y → mfst m x Het.≅ f1 y)
                    → (∀ {x y} → x Het.≅ y → msnd m x Het.≅ f2 y)
                    → RelMorph R' S' 
relObjPreservesEq-ext R S R' S' m f1 f2 ≡.refl ≡.refl ≡.refl ≡.refl Het.refl Het.refl e1 e2 =
  let
      h : ∀ {x : fst R} {y : snd R} → x , y ∈ rel R → (mfst m x , msnd m y ∈ rel S)
      h = RelMorph.preserves m 
    
      -- preservesRS : preservesRelObj R S f1 f2
      preservesRS : ∀ {x : fst R} {y : snd R} → x , y ∈ rel R → (f1 x , f2 y ∈ rel S) 
      preservesRS {x} {y} xy∈R = ≡.subst₂ (λ z w → z , w ∈ rel S) (Het.≅-to-≡ (e1 {x} {x} Het.refl)) (Het.≅-to-≡ (e2 {y} {y} Het.refl)) (h xy∈R) 
    in RM[ f1 , f2 , preservesRS ] 

relObjPreservesEq-ext-p : ∀ (R S R' S' : RelObj) → (m : RelMorph R S)
                    → (f1 : fst R' → fst S') → (f2 : snd R' → snd S')
                    → fst R ≡ fst R' → fst S ≡ fst S'
                    → snd R ≡ snd R' → snd S ≡ snd S'
                    → rel R Het.≅ rel R'
                    → rel S Het.≅ rel S' 
                    → (∀ {x y} → x Het.≅ y → mfst m x Het.≅ f1 y)
                    → (∀ {x y} → x Het.≅ y → msnd m x Het.≅ f2 y)
                    → preservesRelObj R' S' f1 f2
relObjPreservesEq-ext-p R S R' S' m f1 f2 ≡.refl ≡.refl ≡.refl ≡.refl Het.refl Het.refl e1 e2 = 
  let
      h : ∀ {x : fst R} {y : snd R} → x , y ∈ rel R → (mfst m x , msnd m y ∈ rel S)
      h = RelMorph.preserves m 
    
      -- preservesRS : preservesRelObj R S f1 f2
      preservesRS : ∀ {x : fst R} {y : snd R} → x , y ∈ rel R → (f1 x , f2 y ∈ rel S) 
      preservesRS {x} {y} xy∈R = ≡.subst₂ (λ z w → z , w ∈ rel S) (Het.≅-to-≡ (e1 {x} {x} Het.refl)) (Het.≅-to-≡ (e2 {y} {y} Het.refl)) (h xy∈R) 
    in preservesRS 


-- third component of RTObj -- functor of relations + properties 
record RTObj* {k : ℕ} (F1 F2 : Functor (Sets^ k) Sets) : Set₁ where 
  open RelObj
  module F1 = Functor F1
  module F2 = Functor F2
  field 
    F* : Functor (Rels^ k) Rels 

    F*-preserves-1 : ∀ (Rs : Vec RelObj k) → fst (Functor.F₀ F* Rs) ≡ F1.₀ (vecfst Rs)
    F*-preserves-2 : ∀ (Rs : Vec RelObj k) → snd (Functor.F₀ F* Rs) ≡ F2.₀ (vecsnd Rs)

    F*-preserves-m1 : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ])
                      -- have to use x y , x ≅ y because LHS and RHS don't have definitionally equal types 
                      →  ∀ {x y} → x Het.≅ y → mfst (Functor.F₁ F* ms) x Het.≅ Functor.F₁ F1 (vecmfst ms) y

    F*-preserves-m2 : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ])
                      -- have to use x y , x ≅ y because LHS and RHS don't have definitionally equal types 
                      →  ∀ {x y} → x Het.≅ y → msnd (Functor.F₁ F* ms) x Het.≅ Functor.F₁ F2 (vecmsnd ms) y

  -- abstract 

-- Goal: RTObj*.F*Rel (RTObj.F* Rt) Ss
--       (Functor.F₁ Rt.F1 (vecmfst fs) x)
--       (Functor.F₁ Rt.F1 (vecmsnd fs) y)
-- Have: RTObj*.F*Rel (RTObj.F* Rt) Rs x y



  F*Rel : ∀ (Rs : Vec RelObj k) → REL0 (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))
  F*Rel Rs = ≡.subst₂ REL0 (F*-preserves-1 Rs) ( (F*-preserves-2 Rs) ) (rel (Functor.F₀ F* Rs)) 

  F*RelObj : ∀ (Rs : Vec RelObj k) → RelObj 
  F*RelObj Rs = R[ F1.₀ (vecfst Rs) , F2.₀ (vecsnd Rs) , F*Rel Rs ]

  F*Rel-eq : ∀ (Rs : Vec RelObj k) → F*Rel Rs Het.≅ rel (Functor.F₀ F* Rs) 
  F*Rel-eq Rs = subst₂-reduce REL0 (F*-preserves-1 Rs) (F*-preserves-2 Rs) (rel (Functor.F₀ F* Rs)) 

  -- TODO combine this with F*Rel-map 
  F*RelObj-preserves : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ]) → preservesRelObj (F*RelObj Rs) (F*RelObj Ss) ( (F1.₁ (vecmfst ms))) ( (F2.₁ (vecmsnd ms))) 
  F*RelObj-preserves {Rs} {Ss} ms = relObjPreservesEq-ext-p F*Rs F*Ss (F*RelObj Rs) (F*RelObj Ss) F*ms F1ms F2ms p1Rs p1Ss p2Rs p2Ss p*Rs p*Ss pm1 pm2 
    where
          F*ms = Functor.F₁ F* ms ; F1ms = F1.₁ (vecmfst ms) ; F2ms = F2.₁ (vecmsnd ms)
          F*Rs = Functor.F₀ F* Rs ; F*Ss = Functor.F₀ F* Ss
          F1Rs = F1.₀ (vecfst Rs) ; F2Rs = F2.₀ (vecsnd Rs)
          F1Ss = F1.₀ (vecfst Ss) ; F2Ss = F2.₀ (vecsnd Ss)

          p1Rs : fst F*Rs ≡ F1Rs ; p1Rs = F*-preserves-1 Rs
          p2Rs : snd F*Rs ≡ F2Rs ; p2Rs = F*-preserves-2 Rs 
          --
          p1Ss : fst F*Ss ≡ F1Ss ; p1Ss = F*-preserves-1 Ss 
          p2Ss : snd F*Ss ≡ F2Ss ; p2Ss = F*-preserves-2 Ss 
          --
          p*Rs : rel F*Rs Het.≅ rel (F*RelObj Rs) ; p*Rs = Het.sym (F*Rel-eq Rs)
          p*Ss : rel F*Ss Het.≅ rel (F*RelObj Ss) ; p*Ss = Het.sym (F*Rel-eq Ss)
          --
          pm1 : ∀ {x y} → x Het.≅ y → mfst F*ms x Het.≅ F1ms y 
          pm1 = F*-preserves-m1 ms
          pm2 : ∀ {x y} → x Het.≅ y → msnd F*ms x Het.≅ F2ms y
          pm2 = F*-preserves-m2 ms


  F*Rel-map : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ]) → Rels [ F*RelObj Rs , F*RelObj Ss ]
  F*Rel-map {Rs} {Ss} ms = relObjPreservesEq-ext F*Rs F*Ss (F*RelObj Rs) (F*RelObj Ss) F*ms F1ms F2ms p1Rs p1Ss p2Rs p2Ss p*Rs p*Ss pm1 pm2 
    where
          F*ms = Functor.F₁ F* ms ; F1ms = F1.₁ (vecmfst ms) ; F2ms = F2.₁ (vecmsnd ms)
          F*Rs = Functor.F₀ F* Rs ; F*Ss = Functor.F₀ F* Ss
          F1Rs = F1.₀ (vecfst Rs) ; F2Rs = F2.₀ (vecsnd Rs)
          F1Ss = F1.₀ (vecfst Ss) ; F2Ss = F2.₀ (vecsnd Ss)

          p1Rs : fst F*Rs ≡ F1Rs ; p1Rs = F*-preserves-1 Rs
          p2Rs : snd F*Rs ≡ F2Rs ; p2Rs = F*-preserves-2 Rs 
          --
          p1Ss : fst F*Ss ≡ F1Ss ; p1Ss = F*-preserves-1 Ss 
          p2Ss : snd F*Ss ≡ F2Ss ; p2Ss = F*-preserves-2 Ss 
          --
          p*Rs : rel F*Rs Het.≅ rel (F*RelObj Rs) ; p*Rs = Het.sym (F*Rel-eq Rs)
          p*Ss : rel F*Ss Het.≅ rel (F*RelObj Ss) ; p*Ss = Het.sym (F*Rel-eq Ss)
          --
          pm1 : ∀ {x y} → x Het.≅ y → mfst F*ms x Het.≅ F1ms y 
          pm1 = F*-preserves-m1 ms
          pm2 : ∀ {x y} → x Het.≅ y → msnd F*ms x Het.≅ F2ms y
          pm2 = F*-preserves-m2 ms

  -- try to construct a functor from F*RelObj and F*Rel-map 
  F*Functor : Functor (Rels^ k) Rels 
  F*Functor = record
                { F₀ = F*RelObj
                ; F₁ = F*Rel-map
                ; identity = {!!} , {!!}
                ; homomorphism = {!!}
                ; F-resp-≈ = {!!}
                } 

  -- instead of taking F* as a field of RTObj*,
  -- and having a bunch of properties (that are tedious to prove)
  --
  -- what if we take components of F* (F₀, F₁ , etc.)
  -- that are maybe easier to reason about
  -- and then
  -- construct a functor from these pieces ?? 

  -- like rather than taking some arbitrary functor from [Rels^ k ,Rels]
  -- and asserting its components must satisfy XYZ,
  -- just ask directly for components satisfying XYZ...
  -- and then construct a functor! 



-- vecmfst {k} {Rs = Rs} {S } ms = Functor.F₁ (π₁Vec k) ms 
-- π₁Vec = Func^ Rels Sets π₁ 
-- p1 : Sets [ Functor.F₁ F (Functor.F₁ (Func^ C D g) ((C^ k) [ gs ∘ fs ] ))
--             ≈ μH1-map (vecmfst gs) ∘' (μH1-map (vecmfst fs)) ]





 



record RTObj (k : ℕ) : Set (lsuc lzero) where 
  constructor RT[_,_,_]
  open RelObj
  field 
    F1 : Functor (Sets^ k) Sets
    F2 : Functor (Sets^ k) Sets
    F* : RTObj* F1 F2 
    -- Functor (Rels^ k) Rels 

  -- aliases for fields of RTObj* 
  F*₀ : Vec RelObj k → RelObj 
  F*₀ = Functor.F₀ (RTObj*.F* F*)

  F*-preserves-1 : ∀ (Rs : Vec RelObj k) → fst (F*₀ Rs) ≡ Functor.F₀ F1 (vecfst Rs)
  F*-preserves-1 = RTObj*.F*-preserves-1 F*

  F*-preserves-2 : ∀ (Rs : Vec RelObj k) → snd (F*₀ Rs) ≡ Functor.F₀ F2 (vecsnd Rs)
  F*-preserves-2 = RTObj*.F*-preserves-2 F*




record RTObj*Components {k : ℕ} (F1 F2 : Functor (Sets^ k) Sets) : Set₁ where 
  open RelObj
  module F1 = Functor F1
  module F2 = Functor F2
  field 
    F*Rel : ∀ (Rs : Vec RelObj k) → REL0 (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))
    F*Rel-preserves : ∀ {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ])
                      → preservesRel (F*Rel Rs) (F*Rel Ss) (F1.₁ (vecmfst ms)) (F2.₁ (vecmsnd ms))


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

record RTObj2 (k : ℕ) : Set (lsuc lzero) where 
  constructor RT2[_,_,_]
  open RelObj
  field 
    F1 : Functor (Sets^ k) Sets
    F2 : Functor (Sets^ k) Sets
    F*Components : RTObj*Components F1 F2 

  F* : Functor (Rels^ k) Rels 
  F* = RTObj*Components.F* F*Components 

RTMorph-resp : ∀ {k : ℕ} → (H K : RTObj2 k) → (d1 : NaturalTransformation (RTObj2.F1 H) (RTObj2.F1 K)) 
         → (d2 : NaturalTransformation (RTObj2.F2 H) (RTObj2.F2 K)) 
         → (Rs : Vec RelObj k) → Set 
RTMorph-resp H K d1 d2 Rs = preservesRelObj (Functor.F₀ (RTObj2.F* H) Rs)
                                            (Functor.F₀ (RTObj2.F* K) Rs)
                                            (NaturalTransformation.η d1 (vecfst Rs))
                                            (NaturalTransformation.η d2 (vecsnd Rs)) 

record RTMorph2 {k : ℕ} (H K : RTObj2 k) : Set (lsuc lzero) where 
  constructor RTM[_,_,_] 
  private module H = RTObj2 H
  private module K = RTObj2 K 

  field 
    d1 : NaturalTransformation H.F1 K.F1
    d2 : NaturalTransformation H.F2 K.F2


    d-resp : ∀ {Rs : Vec RelObj k} → RTMorph-resp H K d1 d2 Rs 

  -- we can define a natural transformation
  -- from H.F* to K.F* in terms of d1 and d2 
  d* : NaturalTransformation (RTObj2.F* H) (RTObj2.F* K)
  d* = record { η = λ Rs → RM[ (NaturalTransformation.η d1 (vecfst Rs)) , (NaturalTransformation.η d2 (vecsnd Rs)) , d-resp ]
              ; commute = λ fs → (NaturalTransformation.commute d1 (vecmfst fs)) , NaturalTransformation.commute d2 (vecmsnd fs)
              ; sym-commute = λ fs → ( (NaturalTransformation.sym-commute d1 (vecmfst fs))) , (NaturalTransformation.sym-commute d2 (vecmsnd fs))  }



idRTMorph : ∀ {k : ℕ} → (H : RTObj2 k) → RTMorph2 H H
idRTMorph {k} H = record { d1 = idnat ; d2 = idnat ; d-resp = λ xy∈H*R → xy∈H*R } 

compose-RTMorph2 : ∀ {k} {J K L : RTObj2 k} → RTMorph2 K L → RTMorph2 J K → RTMorph2 J L
compose-RTMorph2 RTM[ f1 , f2 , f-resp ] RTM[ g1 , g2 , g-resp ] = RTM[ f1 ∘v g1 , f2 ∘v g2 , f-resp ∘' g-resp ] 


RTMorph2-≈ : ∀ {k} {H K : RTObj2 k} → (m1 m2 : RTMorph2 H K) → Set₁ 
RTMorph2-≈ {k} m m' = [Sets^ k ,Sets] [ RTMorph2.d1 m ≈ RTMorph2.d1 m' ]
                     ×' [Sets^ k ,Sets] [ RTMorph2.d2 m ≈ RTMorph2.d2 m' ]  

RTMorph2-≈-Equiv : ∀ {k} {A B : RTObj2 k} → IsEquivalence (RTMorph2-≈ {k} {A} {B})
RTMorph2-≈-Equiv = record { refl = ≡.refl , ≡.refl ; sym = λ { (p1 , p2)  → ≡.sym p1 , ≡.sym p2  } ; trans = λ { (p1 , p2) (r1 , r2) → (≡.trans p1 r1) , (≡.trans p2 r2) }  } 


RTCat : ℕ → Category (lsuc lzero) (lsuc lzero) (lsuc lzero) 
RTCat k =  record
  { Obj = RTObj2 k
  ; _⇒_ = RTMorph2 
  ; _≈_ = RTMorph2-≈  
  ; id = λ {H} → idRTMorph H   
  ; _∘_ =   compose-RTMorph2 
  ; assoc =  ≡.refl , ≡.refl 
  ; sym-assoc =  ≡.refl , ≡.refl
  ; identityˡ = ≡.refl , ≡.refl
  ; identityʳ = ≡.refl , ≡.refl
  ; identity² = ≡.refl , ≡.refl
  ; equiv = RTMorph2-≈-Equiv  
  ; ∘-resp-≈ = λ { {f = f} {g} {h} {i} (f1≈h1 , f2≈h2) (g1≈i1 , g2≈i2) → SetFuncs.∘-resp-≈ {f = RTMorph2.d1 f} {RTMorph2.d1 g} {RTMorph2.d1 h} {RTMorph2.d1 i} f1≈h1 g1≈i1
                                                                       , SetFuncs.∘-resp-≈ {f = RTMorph2.d2 f} {RTMorph2.d2 g} {RTMorph2.d2 h} {RTMorph2.d2 i} f2≈h2 g2≈i2 } 
  }
  where module SetFuncs = Category [Sets^ k ,Sets]
        



-- should be able to embed RT k into Rels functor category
embedRT : ∀ {k} → Functor (RTCat k) [Rels^ k ,Rels] 
embedRT = record
            { F₀ = λ Rt → {!!} 
            -- need to define natural transformation in [Rels^ k ,Rels] in terms
            -- of RTMorph.
            ; F₁ = λ f → {!!} 
            ; identity = {!!}
            ; homomorphism = {!!}
            ; F-resp-≈ = {!!}
            } 


{-




vecproj₁ : ∀ {k} {As Bs : Vec Set k} → (Sets^ k) [ zipWith _×'_ As Bs  , As ]
vecproj₁ {zero} {[]} {[]} = bigtt
vecproj₁ {suc k} {A ∷ As} {B ∷ Bs} = proj₁ , vecproj₁ 

vecproj₂ : ∀ {k} {As Bs : Vec Set k} → (Sets^ k) [ zipWith _×'_ As Bs  , Bs ]
vecproj₂ {zero} {[]} {[]} = bigtt
vecproj₂ {suc k} {A ∷ As} {B ∷ Bs} = proj₂ , vecproj₂ 



module Identities {k : ℕ} (F : Functor (Sets^ k) Sets) where 
{- this is more developed in RelCats-Set-irrel
  
    module F = Functor F 
    open F using (F₀ ; F₁) 

    -- need to see a relation as a set 
    -- to define graph relation transformers 
    RelSet : ∀ (R : RelObj) → Set
    RelSet R[ X , Y , R* ] = Σ[ x ∈ X ] (Σ[ y ∈ Y ] R* x y)

    RelSet-map : ∀ {R S : RelObj} → RelMorph R S → RelSet R → RelSet S
    RelSet-map RM[ ffst , fsnd , preserves ] (x , y , rxy) = ffst x , fsnd y , preserves rxy

    {- Maybe we can define this if RelMorph-≈ also includes proof about preserves f ≈ preserves g
    RelSetF : Functor Rels Sets
    RelSetF = record
                { F₀ = RelSet
                ; F₁ = RelSet-map
                ; identity = ≡.refl
                ; homomorphism = ≡.refl
                ; F-resp-≈ = λ { {f = f} {g = g} (f₁≈g₁ , f₂≈g₂) {x , y , rxy} → {! RelMorph.preserves g rxy!}  } 
                } 
    -}

    -- get the underlying product  of a relation 
    RelUProd : ∀ (R : RelObj) → Set
    RelUProd R[ X , Y , _ ] = X ×' Y

    -- function from the relation seen as an object to the underlying product 
    incl : ∀ (R : RelObj) → RelSet R → RelUProd R
    incl R (x , y , _) = x , y


    h-A×B : ∀ {As Bs : Vec Set k} 
            → F₀ (zipWith _×'_ As Bs) → F₀ As ×' F₀ Bs
    h-A×B {As} {Bs} FAs×Bs = < F₁ vecproj₁ , F₁ vecproj₂ > FAs×Bs 



    -- normalized Goal: foreach2 (λ A B → A → B) (vmap RelSet Rs)
                        --       (vmap (λ R → Σ (fst R) (λ x → snd R)) Rs)
    -- normalized Goal: foreach2 (λ R R' → RelSet R → fst R' ×' snd R' ) Rs Rs
    -- normalized Goal: foreach (λ R → RelSet R → fst R ×' snd R ) Rs
    -- normalized Goal: foreach incl Rs
    -- normalized Goal: Vec (Σ RelObj (incl R)) n

    vmap-foreach : ∀ {l} {k} {X : Set l} (f g : X → Set) → (nat : ∀ x → f x → g x) → (xs : Vec X k) → Sets^ k [ vmap f xs , vmap g xs ] 
    vmap-foreach f g nat [] = bigtt
    vmap-foreach f g nat (x ∷ xs) = nat x , vmap-foreach f g nat xs 


    h-A×B-R : ∀ (Rs : Vec RelObj k)
            → F₀ (vmap RelUProd Rs) → F₀ (vecfst Rs) ×' F₀ (vecsnd Rs)
    h-A×B-R Rs = < F₁ (vmap-foreach RelUProd fst (λ R → proj₁) Rs) , F₁ ( (vmap-foreach RelUProd snd (λ R → proj₂) Rs)) >  

    vmap-incl : ∀ {k} (Rs : Vec RelObj k) → Sets^ k [ vmap RelSet Rs , vmap RelUProd Rs ] 
    vmap-incl = vmap-foreach RelSet RelUProd incl 

    -- Goal: Sets^ k [ vmap RelSet Rs , vmap (λ R → fst R ×' snd R) Rs ]
    Fincl :  ∀ (Rs : Vec RelObj k)  
            → F₀ (vmap RelSet Rs) → F₀ (vmap RelUProd Rs)
    Fincl Rs FRs = F₁ ( vmap-incl Rs ) FRs

    Fincl' :  ∀ (Rs : Vec RelObj k)  
            → F₀ (vmap RelSet Rs) → F₀ (zipWith _×'_ (vecfst Rs) (vecsnd Rs))
    Fincl' Rs FRs = {!!} 
    
    Fincl-lem : ∀ {k} (Rs : Vec RelObj k)  
            → (vmap RelUProd Rs)
            ≡ zipWith _×'_ (vecfst Rs) (vecsnd Rs)
    Fincl-lem [] = ≡.refl
    Fincl-lem (R ∷ Rs) = ≡.cong (_∷_ (RelUProd R)) (Fincl-lem Rs)


    factor-subset : ∀ {A B C : Set} → (f : A → B ×' C) → REL0 B C 
    factor-subset {A = A} f b c = Σ[ x ∈ A ] f x ≡ (b , c)    

    idRT** : ∀ (Rs : Category.Obj (Rels^ k)) → REL0 (F₀ (vecfst Rs)) (F₀ (vecsnd Rs))
    idRT** Rs = factor-subset {A = F₀ (vmap RelSet Rs)} (h-A×B-R Rs ∘' Fincl Rs)

    -- this is like functorial action for 'vmap f' for functor f : Rels → Sets 
    map-fst' : ∀ {k} (Rs Ss : Vec RelObj k) (f : RelObj → Set) (fmap : ∀ {R S} → RelMorph R S → f R → f S)
               → (ms : Rels^ k [ Rs , Ss ]) → Sets^ k [ vmap f Rs , vmap f Ss ]
    map-fst' [] [] _ _ _ = bigtt
    map-fst' (R ∷ Rs) (S ∷ Ss) f fmap (m , ms) = fmap m , map-fst' Rs Ss f fmap ms 

    map-fst : ∀ {k} (Rs Ss : Vec RelObj k) (fs : Rels^ k [ Rs , Ss ]) → Sets^ k [ vecfst Rs , vecfst Ss ]
    map-fst [] [] _ = bigtt
    map-fst (R ∷ Rs) (S ∷ Ss) (f , fs) = mfst f , map-fst Rs Ss fs

    map-snd : ∀ {k} (Rs Ss : Vec RelObj k) (fs : Rels^ k [ Rs , Ss ]) → Sets^ k [ vecsnd Rs , vecsnd Ss ]
    map-snd Rs Ss fs = map-fst' Rs Ss snd msnd fs 




   --  Goal: (F₁ (vmap-foreach RelUProd fst (λ R → proj₁) Ss)
   --      (F₁ (vmap-foreach RelSet RelUProd incl Ss)
   --          (F₁ (map-fst' Rs Ss RelSet RelSet-map fs) FRs))
   --      ,
   --      F₁ (vmap-foreach RelUProd snd (λ R → proj₂) Ss)
   --      (F₁ (vmap-foreach RelSet RelUProd incl Ss)
   --          (F₁ (map-fst' Rs Ss RelSet RelSet-map fs) FRs)))
   --      ≡ (F₁ (map-fst Rs Ss fs) FAs , F₁ (map-fst' Rs Ss snd msnd fs) FBs)
   --  ————————————————————————————————————————————————————————————
   --  e   : (F₁ (vmap-foreach RelUProd fst (λ R → proj₁) Rs)
   --      (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs)
   --      ,
   --      F₁ (vmap-foreach RelUProd snd (λ R → proj₂) Rs)
   --      (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs))
   --      ≡ (FAs , FBs)

    idRT*-preserves : ∀ (Rs Ss : Vec RelObj k) (fs : Rels^ k [ Rs , Ss ])
                      → preservesRelObj
                            R[ F₀ (vecfst Rs) , F₀ (vecsnd Rs) , idRT** Rs ]
                            R[ F₀ (vecfst Ss) , F₀ (vecsnd Ss) , idRT** Ss ]
                            (F₁ (map-fst Rs Ss fs)) (F₁ (map-snd Rs Ss fs))
    idRT*-preserves Rs Ss fs {FAs} {FBs} (FRs , e) = (F₁  mapfs FRs) , {!!}
        where mapfs : Sets^ k [ vmap RelSet Rs , vmap RelSet Ss ] 
              mapfs = map-fst' Rs Ss RelSet RelSet-map fs 



    -- Goal: h-A×B-R Ss (Fincl Ss (F₁ mapfs FRs)) ≡
    --     (F₁ (map-fst Rs Ss fs) FAs , F₁ (map-snd Rs Ss fs) FBs)
    --    ≡ 
    --     (F₁ (map-fst Rs Ss fs) F₁ (vmap-foreach RelUProd fst (λ R → proj₁) Rs) (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs)
    --   ,  F₁ (map-snd Rs Ss fs) F₁ (vmap-foreach RelUProd snd (λ R → proj₂) Rs) (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs)

    -- Goal: idRT** Ss (F₁ (map-fst Rs Ss fs) FAs)
                    -- (F₁ (map-snd Rs Ss fs) FBs)
    -- ————————————————————————————————————————————————————————————
    -- e   : h-A×B-R Rs (Fincl Rs FRs) ≡ (FAs , FBs)
    -- FRs : F₀ (vmap RelSet Rs)
    -- FBs : F₀ (vecsnd Rs)
    -- FAs : F₀ (vecfst Rs)
    -- fs  : Rels^ k [ Rs , Ss ]

    -- e   : (F₁ (vmap-foreach RelUProd fst (λ R → proj₁) Rs)
       --     (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs)
    --     ,
    --     F₁ (vmap-foreach RelUProd snd (λ R → proj₂) Rs)
    --     (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs))
    --     ≡ (FAs , FBs)

    -- FAs = F₁ (vmap-foreach RelUProd fst (λ R → proj₁) Rs) (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs)
    -- FBs = F₁ (vmap-foreach RelUProd snd (λ R → proj₂) Rs) (F₁ (vmap-foreach RelSet RelUProd incl Rs) FRs)


    idRT* : Functor (Rels^ k) Rels 
    idRT* = record
                { F₀ = λ Rs → R[ (F₀ (vecfst Rs)) , (F₀ (vecsnd Rs)) , idRT** Rs ]
                ; F₁ = λ {Rs} {Ss} fs → RM[ F₁ ( map-fst Rs Ss fs) , F₁ (map-snd Rs Ss fs) , {! idRT*-preserves  !} ]
                ; identity = {!!}
                ; homomorphism = {!!}
                ; F-resp-≈ = {!!}
                } 


    idRT : RTObj k
    idRT = record
            { F1 = F
            ; F2 = F
            ; F* = idRT* 
            ; F*-preserves-1 = λ Rs → ≡.refl
            ; F*-preserves-2 = λ Rs → ≡.refl
            } 


-}
open Identities 

-- RTEndo : ∀ {k} → Endofunctor (RT k) → Functor (Sets^ k) Sets
-- RTEndo H = record
--              { F₀ = {!!}
--              ; F₁ = {!!}
--              ; identity = {!!}
--              ; homomorphism = {!!}
--              ; F-resp-≈ = {!!}
--              } 



module PolynomialRels where 

    open import Categories.Object.Terminal 

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

    -- there are two possible choices here 
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


    -- TODO need actions on morphisms as well 

    _×RelM_ : ∀ {R S R' S' : RelObj} → RelMorph R S → RelMorph R' S' → RelMorph (R ×Rel R') (S ×Rel S')
    _×RelM_ {R} {S} {R'} {S'} RM[ f , g , fg-preserves ] RM[ f' , g' , f'g'-preserves ]  =
        RM[ funcprod (f , f')  , funcprod (g , g') , prod-preserves ] 
            where prod-preserves : preservesRelObj (R ×Rel R') (S ×Rel S') (funcprod (f , f')) (funcprod (g , g'))
                  prod-preserves {x , x'} {y , y'} p  = Sfxgy , S'f'x'g'y' -- ∧--, ( Sfxgy , S'f'x'g'y' ) 
                        where fgp :  (rel R x y) →  (rel S (f x) (g y))
                              fgp = fg-preserves {x} {y} 

                              f'g'p :  (rel R' x' y') →  (rel S' (f' x') (g' y'))
                              f'g'p = f'g'-preserves {x'} {y'} 

                              -- -prod :  (rel R x y) ×'  (rel R' x' y') 
                              -- -prod = ∧- p

                              Sfxgy :  (rel S (f x) (g y))
                              Sfxgy = fgp (proj₁ p)
                              S'f'x'g'y' :  (rel S' (f' x') (g' y'))
                              S'f'x'g'y' = f'g'p (proj₂ p)

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






-- second order relation transformer over H1, H2 
-- -- TODO move this to RelCats-x 
-- -- this should give all the data needed to define an endofunctor on RT k 
--
-- TODO implement all of Definition 3.6 in mscs.pdf
{-

-- This is slightly off .. H* should be a functor from RT k to [Rels^k , Rels]
record HRTObj* {k : ℕ} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) : Set₁ where
  open RelObj
  field
    H* : Functor [Rels^ k ,Rels] [Rels^ k ,Rels]

    -- -- these use RTObj -- need to update to use RTObj* 
    -- H*-preserves-1 : ∀ (RT : RTObj k) → (F* : Functor (Sets^ k) Sets)  → (Rs : Vec RelObj k)
    --                  → fst (Functor.F₀ (Functor.F₀ H* (RTObj.F* RT)) Rs)
    --                  ≡ Functor.F₀ (Functor.F₀ H1 (RTObj.F1 RT)) (vecfst Rs)

    -- H*-preserves-2 : ∀ (RT : RTObj k) → (F* : Functor (Sets^ k) Sets)  → (Rs : Vec RelObj k)
    --                  → snd (Functor.F₀ (Functor.F₀ H* (RTObj.F* RT)) Rs)
    --                  ≡ Functor.F₀ (Functor.F₀ H2 (RTObj.F2 RT)) (vecsnd Rs)


    H*-preserves-1 : ∀ (F1 F2 : Functor (Sets^ k) Sets) (F* : RTObj* F1 F2) → (Rs : Vec RelObj k)
                     → fst (Functor.F₀ (Functor.F₀ H* (RTObj*.F* F*)) Rs)
                     ≡ Functor.F₀ (Functor.F₀ H1 F1) (vecfst Rs)

    H*-preserves-2 : ∀ (F1 F2 : Functor (Sets^ k) Sets) (F* : RTObj* F1 F2) → (Rs : Vec RelObj k)
                     → snd (Functor.F₀ (Functor.F₀ H* (RTObj*.F* F*)) Rs)
                     ≡ Functor.F₀ (Functor.F₀ H2 F2) (vecsnd Rs)



  endoRT₀ : RTObj k → RTObj k 
  endoRT₀ RT[ F1 , F2 , F* ] =
    let RT* : RTObj* (Functor.F₀ H1 F1) (Functor.F₀ H2 F2)
        RT* = record { F* = Functor.F₀ H* (RTObj*.F* F*) ; F*-preserves-1 = H*-preserves-1 F1 F2 F* ; F*-preserves-2 = H*-preserves-2 F1 F2 F* }

    in RT[ Functor.F₀ H1 F1 , Functor.F₀ H2 F2 , RT* ] 

    -- record { F1 = Functor.F₀ H1 F1
    --        ; F2 = Functor.F₀ H2 F2
    --        ; F* = {! RTObj.F* (endoRT₀ rt)!} } 
  -- RTObj.F* (endoRT₀ rt) } 

  -- this constitutes an endofunctor on RT k
  endo : Functor (RTCat k) (RTCat k)
  endo = record
           { F₀ = endoRT₀  
           ; F₁ = {!!}
           ; identity = {!!}
           ; homomorphism = {!!}
           ; F-resp-≈ = {!!}
           } 
-}



record HRTObj* {k : ℕ} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) : Set₁ where
  open RelObj
  field
    H* : Functor (RTCat k) [Rels^ k ,Rels]

    -- first 'implicit' bullet point 
    H*-preserves-1 : ∀ (F1 F2 : Functor (Sets^ k) Sets) (F* : RTObj* F1 F2) → (Rs : Vec RelObj k)
                     → fst (Functor.F₀ (Functor.F₀ H* RT[ F1 , F2 , F* ]) Rs)
                     ≡ Functor.F₀ (Functor.F₀ H1 F1) (vecfst Rs)
    -- first 'implicit' bullet point 
    H*-preserves-2 : ∀ (F1 F2 : Functor (Sets^ k) Sets) (F* : RTObj* F1 F2) → (Rs : Vec RelObj k)
                     → snd (Functor.F₀ (Functor.F₀ H* RT[ F1 , F2 , F* ]) Rs)
                     ≡ Functor.F₀ (Functor.F₀ H2 F2) (vecsnd Rs)


    -- second 'implicit' bullet point 
    H*-preserves-m1 : ∀ (F1 F2 : Functor (Sets^ k) Sets) (F* : RTObj* F1 F2)
                     → {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ] )
                     → ∀ {x y} → x Het.≅ y
                     → mfst (Functor.F₁ (Functor.F₀ H* RT[ F1 , F2 , F* ]) ms) x
                     Het.≅ Functor.F₁ (Functor.F₀ H1 F1) (vecmfst ms) y
    -- second 'implicit' bullet point
    H*-preserves-m2 : ∀ (F1 F2 : Functor (Sets^ k) Sets) (F* : RTObj* F1 F2) 
                     → {Rs Ss : Vec RelObj k} → (ms : (Rels^ k) [ Rs , Ss ] )
                     → ∀ {x y} → x Het.≅ y
                     → msnd (Functor.F₁ (Functor.F₀ H* RT[ F1 , F2 , F* ]) ms) x
                     Het.≅ Functor.F₁ (Functor.F₀ H2 F2) (vecmsnd ms) y


    -- third bullet point, part 1 
    H*-preserves-nat1 : ∀  (Rt St : RTObj k) → (rtm : RTMorph Rt St)
                      → ∀ {Rs : Vec RelObj k} {x y} → x Het.≅ y
                      → mfst (NaturalTransformation.η (Functor.F₁ H* rtm) Rs) x
                        Het.≅ NaturalTransformation.η (Functor.F₁ H1 (δ₁ rtm)) (vecfst Rs) y

    -- third bullet point, part 2
    H*-preserves-nat2 : ∀  (Rt St : RTObj k) → (m : RTMorph Rt St)
                      → ∀ {Rs : Vec RelObj k} {x y} → x Het.≅ y
                      → msnd (NaturalTransformation.η (Functor.F₁ H* m) Rs) x
                        Het.≅ NaturalTransformation.η (Functor.F₁ H2 (δ₂ m)) (vecsnd Rs) y


  endoRT₀ : RTObj k → RTObj k 
  endoRT₀ rt@(RT[ F1 , F2 , F* ]) =
    let RT* : RTObj* (Functor.F₀ H1 F1) (Functor.F₀ H2 F2)
        RT* = record { F* = Functor.F₀ H* rt
                     ; F*-preserves-1 = H*-preserves-1 F1 F2 F*
                     ; F*-preserves-2 = H*-preserves-2 F1 F2 F*
                     ; F*-preserves-m1 = H*-preserves-m1 F1 F2 F* 
                     ; F*-preserves-m2 = H*-preserves-m2 F1 F2 F* }

    in RT[ Functor.F₀ H1 F1 , Functor.F₀ H2 F2 , RT* ]

  {- [ ]TODO 
     - Need to figure out what other assumptions are needed to complete this proof of endoRT₁ 
   -}

  endoRT₁ : ∀ {Rt St : RTObj k} → RTCat k [ Rt , St ] → RTCat k [ endoRT₀ Rt , endoRT₀ St ]
  endoRT₁ {Rt} {St} RTM[ d1 , d2 , d-resp ] = RTM[ Functor.F₁ H1 d1 , Functor.F₁ H2 d2 , resp ]
    where
          -- this is implied by the third bullet point of Definition 3.6 
          -- i.e., H*-preserves-nat-
          resp : ∀ (Rs : Vec RelObj k) → RTMorph-resp (endoRT₀ Rt) (endoRT₀ St) (Functor.F₁ H1 d1) (Functor.F₁ H2 d2) Rs
          resp Rs {x} {y} x,y∈H*Rt*Rs = {!    !} 

          endoH-St* : Functor (Rels^ k) Rels
          endoH-St* = (RTObj*.F* (RTObj.F* (endoRT₀ St)))

          -- goal : : rel (Functor.F₀ H*St* Rs)
                    -- (get-comp-1 (endoRT₀ Rt) (endoRT₀ St) (Functor.F₁ H1 d1) Rs x)
                    -- (get-comp-2 (endoRT₀ Rt) (endoRT₀ St) (Functor.F₁ H2 d2) Rs y)


-- get-comp-1 turns a component of d1 into a function from fst (Rt* Rs) → fst (St* Rs)
-- get-comp-1 : ∀ {k : ℕ} → (H K : RTObj k) → (d1 : NaturalTransformation (RTObj.F1 H) (RTObj.F1 K)) 
--          → (Rs : Vec RelObj k)
--          → RelObj.fst (RTObj.F*₀ H Rs)
--          → RelObj.fst (RTObj.F*₀ K Rs)

    -- F*Rel : ∀ (Rs : Vec RelObj k) → REL0 (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))

    -- H*-preserves-nat1 : ∀  (Rt St : RTObj k) → (m : RTMorph Rt St)
    --                   → ∀ {Rs : Vec RelObj k} {x y} → x Het.≅ y
    --                   → mfst (NaturalTransformation.η (Functor.F₁ H* m) Rs) x
    --                     Het.≅ NaturalTransformation.η (Functor.F₁ H1 (δ₁ m)) (vecfst Rs) y

      -- need to use H*-preserves-nat1  where m = RTM[ d1 , d2 , d-resp ] and
      -- 


          rmorph : ∀ (Rs : Vec RelObj k) → Rels [ Functor.F₀ (Functor.F₀ H* Rt) Rs , Functor.F₀ (Functor.F₀ H* St) Rs ]
          rmorph = NaturalTransformation.η (Functor.F₁ H* RTM[ d1 , d2 , d-resp ]) 

          -- p : ∀ (Rs  : Vec RelObj k) → {!preservesRelObj (Functor.F₀ (Functor.F₀ H* Rt) Rs) (Functor.F₀ (Functor.F₀ H* St) Rs) (mfst (rmorph Rs)) (msnd (rmorph Rs))       !} 
          p : ∀ (Rs  : Vec RelObj k) → ∀ {x y} → rel ((Functor.F₀ (Functor.F₀ H* Rt) Rs)) x y
              → rel ( (Functor.F₀ (Functor.F₀ H* St) Rs)) (mfst (rmorph Rs) x) (msnd (rmorph Rs) y)
          p Rs = RelMorph.preserves (rmorph Rs)



-- preservesRelObj R R' f g = preservesRel (RelObj.rel R) (RelObj.rel R') f g 
-- preservesRel R R' f g = ∀ {x y} → R x y → R' (f x) (g y)
    -- preserves : preservesRelObj R S mfst msnd 
    

  -- this constitutes an endofunctor on RT k
  endo : Functor (RTCat k) (RTCat k)
  endo = record
           { F₀ = endoRT₀  
           ; F₁ = {!endoRT₁ !}
           ; identity = {!!}
           ; homomorphism = {!!}
           ; F-resp-≈ = {!!}
           } 



record HRTObj (k : ℕ) : Set₁ where
  field
    H1 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets] 
    H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets] 

    H* : HRTObj* H1 H2 


record HRTMorph {k : ℕ} (H K : HRTObj k) : Set₁ where
  constructor HRTM[_,_]
  private module H = HRTObj H
  private module K = HRTObj K 
  field
    σ1 : NaturalTransformation H.H1 K.H1
    σ2 : NaturalTransformation H.H2 K.H2

    -- do we need any other conditions ? 
    -- definition 3.7 says that σ_F = (σ1_F1 , σ2_F2) (where F : RT_k)
    -- should be a natural transformation from
    --
    -- H.H* F to K.H* F  in [Rel^k , Rel]
    -- so for every Rs : Vec RelObj k
    --
    -- we have (σ1_F1 As , σ2_F2 Bs) is a RelMorph 
    -- from H* F Rs
    -- to   K* F Rs
    -- 
    


-- category of ho relation transformers.
-- should be naturally isomorphic to
-- functor category [[ RT k , RT k ]] 
HRTCat : ℕ → Category _ _ _
HRTCat k = record
               { Obj = HRTObj k
               ; _⇒_ = HRTMorph
               ; _≈_ = λ m m' → (HRTMorph.σ1 m ≈ HRTMorph.σ1 m') ×' ( (HRTMorph.σ2 m ≈ HRTMorph.σ2 m')) 
               ; id = {!!}
               ; _∘_ = {!!}
               ; assoc = {!!}
               ; sym-assoc = {!!}
               ; identityˡ = {!!}
               ; identityʳ = {!!}
               ; identity² = {!!}
               ; equiv = {!!}
               ; ∘-resp-≈ = {!!}
               }
           where open Category ([[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]]) using (_≈_) 

-}

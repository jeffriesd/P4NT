{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting --confluence-check #-}
-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite


-- open import Data.Nat

open import Data.Product 
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Categories.Category 
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Morphism using (Iso)
open import Data.Vec using (Vec ; _∷_; replicate) renaming (map to vmap)
open import Level renaming (zero to  lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
-- open ≡.≡-Reasoning

open import SetCats
open import RelSem.RelCats-Set

open import Utils using (big⊤ ; bigtt)


module RelSem.HFixRel where 



RelFunc : ℕ → Set₁
RelFunc k = (Vec RelObj k → RelObj)

HFunc : ℕ → Set _
HFunc k = RelFunc k → RelFunc k

FMAP : ∀ {k} → RelFunc k → Set₁
FMAP {k} F = ∀ {As Bs : Vec RelObj k} → (Rels^ k) [ As ,  Bs ]  → Rels [ F As , F Bs ]

FID : ∀ {k} → (F : RelFunc k) → (Fmap : FMAP F) → Set₁
-- FID {k} F Fmap = ∀ {As} {xs} → Fmap {As} {As} (Category.id (Rels^ k )) xs ≡ xs
FID {k} F Fmap = ∀ {As} → Rels [ Fmap {As} {As} (Category.id (Rels^ k )) ≈ idRelMorph ] 

FHOMO : ∀ {k} → (F : RelFunc k) → FMAP F → Set₁ 
FHOMO {k} F Fmap = ∀ {As Bs Cs} 
      → {f : (Rels^ k) [ As ,  Bs ] } → {g : (Rels^ k) [ Bs ,  Cs ] }
      → Rels [ Fmap (Category._∘_ (Rels^ k )  g f) ≈ Rels [ Fmap g ∘ Fmap f ] ]

FRESP : ∀ {k} → (F : RelFunc k) → FMAP F → Set₁ 
FRESP {k} F Fmap = ∀ {As Bs} → {fs gs : (Rels^ k) [ As ,  Bs ] } → (Rels^ k) [ fs ≈ gs ] → Rels [ Fmap fs ≈ Fmap gs ]

-- combine components of a k-ary Rel functor 
mkFunc : ∀ {k} 
         → (F0 : RelFunc k) 
         → (F1 : FMAP F0)
         → (Fid : FID F0 F1)
         → (Fhomo : FHOMO F0 F1)
         → (Fresp : FRESP F0 F1)
         → Functor (Rels^ k) Rels
mkFunc {k} F0 F1 Fid Fhomo Fresp = record
  { F₀ = F0
  ; F₁ = F1
  ; identity = Fid
  ; homomorphism = Fhomo 
  ; F-resp-≈ = Fresp
  } 



-- HFOBJ, HFMAP, etc. just give the types for each component 
-- of a higher order functor 
HFOBJ : ℕ → Set₁
HFOBJ k = Functor (Rels^ k) Rels → Functor (Rels^ k) Rels 

HFMAP : ∀ {k} → (H : HFOBJ k) → Set₁
HFMAP {k} H = ∀ {F G : Functor (Rels^ k) Rels} → NaturalTransformation F G → NaturalTransformation (H F) (H G)

HFID : ∀ {k} → (H : HFOBJ k) → (HFMAP H) → Set₁
 -- ; _≈_ = λ eta1 eta2 → ∀ Xs → NaturalTransformation.η eta1 Xs ≈ NaturalTransformation.η eta2 Xs
HFID {k} H Hmap = ∀ {F : Functor (Rels^ k) Rels} {Xs} → Rels [ NaturalTransformation.η (Hmap {F} {F} (Category.id [Rels^ k ,Rels])) Xs
                                                                ≈ NaturalTransformation.η {F = H F} (Category.id [Rels^ k ,Rels]) Xs ]

HFHOMO : ∀ {k} → (H : HFOBJ k) → HFMAP H → Set₁
HFHOMO {k} H Hmap =  ∀ {F G K : Functor (Rels^ k) (Rels )} {f : NaturalTransformation F G} {g : NaturalTransformation G K}
          → {Xs : Vec RelObj k}  
          → Rels [ 
                NaturalTransformation.η (Hmap (g ∘v f)) Xs 
                ≈ Rels [ (NaturalTransformation.η (Hmap g) Xs) ∘ (NaturalTransformation.η (Hmap f) Xs) ] ]

HFRESP : ∀ {k} → (H : HFOBJ k) → HFMAP H → Set₁
HFRESP {k} H Hmap = ∀ {A B : Functor (Rels^ k) (Rels)} {f g : NaturalTransformation A B} 
          → (f≈g : {Xs : Vec RelObj k} → Rels [ NaturalTransformation.η f Xs ≈ NaturalTransformation.η g Xs ] )
          → {Xs : Vec RelObj k} 
          → Rels [ NaturalTransformation.η (Hmap f) Xs ≈ NaturalTransformation.η (Hmap g) Xs ]

mkHFunc : ∀ {k} 
         → (H0 : HFOBJ k)
         → (H1 : HFMAP H0)
         → (Hid : HFID H0 H1)
         → (Hhomo : HFHOMO H0 H1)
         → (Hresp : HFRESP H0 H1)
         → Functor ([Rels^ k ,Rels]) ([Rels^ k ,Rels])
mkHFunc {k} H0 H1 Hid Hhomo Hresp = record
  { F₀ = H0
  ; F₁ = H1
  ; identity = Hid
  ; homomorphism = Hhomo
  ; F-resp-≈ = Hresp
  } 


import HFixFunctorLib as SFix renaming (HFixFunctor to HFixObj) 


-- -- definition for sets
-- -- data HFixFunctor (H : Functor ([[ C , Sets ]]) [[ C , Sets ]] ) : C.Obj → Set  
-- data HFixFunctor H where
--   hffin : ∀ {As : C.Obj} → Functor.F₀ (Functor.F₀ H (fixHFunc H)) As → HFixFunctor H As

-- data HFixFunctor {k} (H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])) : (Rs : Vec RelObj k) → Set → Set → Set  where 

open RelObj
open RelMorph


open HRTObj*

import Relation.Binary.HeterogeneousEquality as Het

-- compute fixpoint of relation transformer RH
module FixRel where 


    {-# NO_POSITIVITY_CHECK #-}
    data RHFixRT {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
                     (RH  : HRTObj* H1 H2)
        : ∀ (Rs : Vec RelObj k) → REL0 (SFix.HFixObj H1 (vecfst Rs)) (SFix.HFixObj H2 (vecsnd Rs)) 


    -- -- need to encode the fact that RH is over H1, H2 using RTObj* 
    {-# TERMINATING #-}
    μRT* : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2)
                → RTObj* (SFix.fixHFunc H1) (SFix.fixHFunc H2)

    {-# TERMINATING #-}
    μRT : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2)
                → RTObj k

    -- the relation functor (third component of RT) part of fixpoint of RH 
    {-# TERMINATING #-}
    μRels : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH  : HRTObj* H1 H2)
                  → Functor (Rels^ k) Rels


    -- the object part of μ RH 
    HFixRelObj : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH  : HRTObj* H1 H2) → Vec RelObj k → RelObj 
    -- HFixRelObj2 : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH  : HRTObj* H1 H2) → Vec RelObj k → RelObj 

    -- functor map of μ RH 
    {-# TERMINATING #-}
    HFixRel-fmap : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2)
                → FMAP (HFixRelObj H1 H2 RH)


    {-# TERMINATING #-}
    HFixRel-fmap-preserves : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2) {Rs : Vec RelObj k} {Ss : Vec RelObj k}
                             → (fs : (Rels^ k) [ Rs , Ss ])
                             → ∀ {x : SFix.HFixObj H1 (vecfst Rs)} {y : SFix.HFixObj H2 (vecsnd Rs)}
                             → RHFixRT H1 H2 RH Rs x y
                             → RHFixRT H1 H2 RH Ss (SFix.HFix-fmap H1 (vecmfst fs) x) (SFix.HFix-fmap H2 (vecmsnd fs) y)

    -- functor identity 
    HFixRel-id : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2)
                 → FID (HFixRelObj H1 H2 RH) (HFixRel-fmap H1 H2 RH)

    HFixRel-homo : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2)
                   → FHOMO (HFixRelObj H1 H2 RH) (HFixRel-fmap H1 H2 RH)

    HFixRel-resp : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2)
                   → FRESP (HFixRelObj H1 H2 RH) (HFixRel-fmap H1 H2 RH)

    --------------------------------------------------------------------------- 
    -- end types 
    --------------------------------------------------------------------------- 

    -- relation part (third component) of fixpoint of higher order relation transformer 
    μRels H1 H2 RH = mkFunc (HFixRelObj H1 H2 RH) (HFixRel-fmap H1 H2 RH) (HFixRel-id H1 H2 RH) (HFixRel-homo H1 H2 RH) (HFixRel-resp H1 H2 RH)

    HFixRelObj H1 H2 RH Rs = R[ SFix.HFixObj H1 (vecfst Rs) , SFix.HFixObj H2 (vecsnd Rs) , RHFixRT H1 H2 RH Rs ] 

    -- HFixRelObj2 H1 H2 RH Rs = RTObj*.F*RelObj (RTObj.F* (endoRT₀ RH (μRT H1 H2 RH))) Rs
    -- HFixRel-fmap2 H1 H2 RH ms = RTObj*.F*Rel-map (RTObj.F* (endoRT₀ RH (μRT H1 H2 RH))) ms

    HFixRel-fmap H1 H2 RH ms = RM[ Functor.F₁ (SFix.fixHFunc H1) (vecmfst ms)
                                  , Functor.F₁ (SFix.fixHFunc H2) (vecmsnd ms)
                                  , HFixRel-fmap-preserves H1 H2 RH ms ]

    -- fixpoint of higher order relation transformer 
    -- -- F*-preserves-1,2 are immediate because
    -- -- fst (Functor.F₀ (μRels H1 H2 RH) Rs)
    -- -- = SFix.HFixObj H2 (vmap fst Rs)
    -- -- by definition 
    μRT* H1 H2 RH = record { F* = μRels H1 H2 RH
                           ; F*-preserves-1 = λ Rs → ≡.refl
                           ; F*-preserves-2 = λ Rs → ≡.refl
                           ; F*-preserves-m1 = λ { ms Het.refl → Het.refl } 
                           ; F*-preserves-m2 = λ { ms Het.refl → Het.refl } }

    μRT H1 H2 RH = RT[ (SFix.fixHFunc H1) , (SFix.fixHFunc H2) , (μRT* H1 H2 RH) ]


    -- F*Rel : ∀ (Rs : Vec RelObj k) → REL0 (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))
    data RHFixRT {k} H1 H2 RH where 
        rhfin : ∀ {Rs  : Vec RelObj k}
                → {x : Functor.F₀ (Functor.F₀ H1 (SFix.fixHFunc H1)) (vecfst Rs)}
                → {y : Functor.F₀ (Functor.F₀ H2 (SFix.fixHFunc H2)) (vecsnd Rs)}
                → RTObj*.F*Rel (RTObj.F* (endoRT₀ RH (μRT H1 H2 RH))) Rs x y
                → RHFixRT H1 H2 RH Rs (SFix.hffin x)
                                      (SFix.hffin y)


    HFixRel-fmap-preserves {k} H1 H2 RH {Rs} {Ss} fs {SFix.hffin x} {SFix.hffin y} (rhfin p) = 
      let -- subgoal : 
          H1μH1 = Functor.F₀ H1 (SFix.fixHFunc H1)
          H2μH2 = Functor.F₀ H2 (SFix.fixHFunc H2)
          RHμRH : RTObj* H1μH1 H2μH2
          RHμRH = RTObj.F* (endoRT₀ RH (μRT H1 H2 RH))
          --
          -- RHμRH* : Functor (Rels^ k) Rels
          -- RHμRH* = RTObj*.F* RHμRH
          -- 
          fx : Functor.F₀ H1μH1 (vecfst Ss)
          fx = Functor.F₁ H1μH1 (vecmfst fs) x
          -- 
          fy : Functor.F₀ H2μH2 (vecsnd Ss)
          fy = Functor.F₁ H2μH2 (vecmsnd fs) y

          pr : fx , fy ∈ RTObj*.F*Rel (RHμRH) Ss
          -- (RTObj*.F1.₁ RHμRH (vecmfst fs) x) (RTObj*.F2.₁ RHμRH (vecmsnd fs) y)
          pr = RTObj*.F*RelObj-preserves {F1 = H1μH1} {F2 = H2μH2} RHμRH fs p
   
          -- p : x , y ∈ RTObj.F*Rel RHμRH* Rs 
          -- subgoal : RTObj*.F*Rel RHμRH Ss fx fy
          subgoal : fx , fy ∈ RTObj*.F*Rel RHμRH Ss 
          subgoal = RTObj*.F*RelObj-preserves {F1 = H1μH1} {F2 = H2μH2} RHμRH fs p
          -- pr -- ≡.subst idf ≡.refl pr 

        -- -- not sure why I'm getting this error: (when trying to define subgoal = pr) 
        -- (Functor.F₀ (RTObj.F1 (μRT H1 H2 RH)) x₁) != (SFix.HFixObj H1 x₁)
        -- of type Set
        -- when checking that the expression RHμRH has type
        -- RTObj* (Functor.F₀ H1 (SFix.fixHFunc H1))
        -- (Functor.F₀ H2 (SFix.fixHFunc H2))
        --
        --
        -- because the LHS does in fact normalize to the RHS 
        --
        -- okay apparently using (≡.subst idf ≡.refl x) works. this doesn't change the type at all, so that's confusing 
        -- okay, not it works without the subst. The only thing I added was some TERMINATING pragmas. I guess that did the trick.

       in rhfin subgoal  


    HFixRel-id {k} H1 H2 RH {Rs} =
      let   p1 : Sets [ SFix.HFix-fmap H1 (Functor.F₁ (π₁Vec k) (Category.id (Rels^ k) {Rs})) ≈ idf ] 
            p1 =  begin (SFix.HFix-fmap H1 (Functor.F₁ (π₁Vec k) (Category.id (Rels^ k) {Rs})))
                        ≈⟨   (Functor.F-resp-≈ (SFix.fixHFunc H1) (Functor.identity (π₁Vec k))) ⟩ 
                         (SFix.HFix-fmap H1 (Category.id (Sets^ k)))
                        ≈⟨ Functor.identity (SFix.fixHFunc H1) ⟩ 
                         idf
                         ∎  

            p2 : Sets [ SFix.HFix-fmap H2 (Functor.F₁ (π₂Vec k) (Category.id (Rels^ k) {Rs})) ≈ idf ] 
            p2 =  begin (SFix.HFix-fmap H2 (Functor.F₁ (π₂Vec k) (Category.id (Rels^ k) {Rs})))
                        ≈⟨   (Functor.F-resp-≈ (SFix.fixHFunc H2) (Functor.identity (π₂Vec k))) ⟩ 
                         (SFix.HFix-fmap H2 (Category.id (Sets^ k)))
                        ≈⟨ Functor.identity (SFix.fixHFunc H2) ⟩ 
                         idf
                         ∎  
        in p1 , p2
           where open Category.HomReasoning (Sets)

    HFixRel-homo {k} H1 H2 RH {Rs} {Ss} {Ts} {fs} {gs} =
      let μH1 = SFix.fixHFunc H1
          μH2 = SFix.fixHFunc H2

          μH1-map = SFix.HFix-fmap H1
          μH2-map = SFix.HFix-fmap H2

          -- [ ] TODO - generalize this proof 
          -- should be able to define this as homomorphism for
          -- F1∘π₁ = (F1 ∘F Func^ Rels Sets π₁ k)
          p1 : Sets [ μH1-map (vecmfst ((Rels^ k) [ gs ∘ fs ] )) ≈ μH1-map (vecmfst gs) ∘' (μH1-map (vecmfst fs)) ]
          p1 = begin μH1-map (vecmfst ((Rels^ k) [ gs ∘ fs ] ))
                               ≈⟨ Functor.F-resp-≈ μH1 (Functor.homomorphism (π₁Vec k)) ⟩
                               μH1-map ((Sets^ k) [ vecmfst gs ∘ vecmfst fs ])
                               ≈⟨ Functor.homomorphism μH1 ⟩
                               μH1-map (vecmfst gs) ∘' μH1-map (vecmfst fs) ∎  
          p2 : Sets [ μH2-map (vecmsnd ((Rels^ k) [ gs ∘ fs ] )) ≈ μH2-map (vecmsnd gs) ∘' (μH2-map (vecmsnd fs)) ]
          p2 = begin μH2-map (vecmsnd ((Rels^ k) [ gs ∘ fs ] ))
                               ≈⟨ Functor.F-resp-≈ μH2 (Functor.homomorphism (π₂Vec k)) ⟩
                               μH2-map ((Sets^ k) [ vecmsnd gs ∘ vecmsnd fs ])
                               ≈⟨ Functor.homomorphism μH2 ⟩
                               μH2-map (vecmsnd gs) ∘' μH2-map (vecmsnd fs) ∎ 

       in p1 , p2 
           where open Category.HomReasoning (Sets)


    HFixRel-resp {k} H1 H2 RH {Rs} {Ss} {fs} {gs} fs≈gs =
      let μH1 = SFix.fixHFunc H1
          μH2 = SFix.fixHFunc H2

          μH1-map = SFix.HFix-fmap H1
          μH2-map = SFix.HFix-fmap H2

          p1 : Sets [ μH1-map (vecmfst fs) ≈ μH1-map (vecmfst gs) ]
          p1 = Functor.F-resp-≈ μH1 (Functor.F-resp-≈ (π₁Vec k) fs≈gs) 

          p2 : Sets [ μH2-map (vecmsnd fs) ≈ μH2-map (vecmsnd gs) ]
          p2 = Functor.F-resp-≈ μH2 (Functor.F-resp-≈ (π₂Vec k) fs≈gs) 

       in p1  , p2
           where open Category.HomReasoning (Sets)

open FixRel

-------------------------------------------------------  
-- definitions
-----------------------------------------------------  


    -- μRels : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH  : HRTObj* H1 H2)
    --               → Functor (Rels^ k) Rels

HFix-hmap : ∀ {k} (H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])) (RH : HRTObj* H1 H2)
          → (K1 K2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
          → (RK : HRTObj* K1 K2)
          -- → HRTMorph RH KH 
          → NaturalTransformation H1 K1
          → NaturalTransformation H2 K2
          → RTMorph (μRT H1 H2 RH) (μRT K1 K2 RK)
HFix-hmap {k} H1 H2 RH K1 K2 RK η1 η2 = RTM[ (SFix.HFix-hmap H1 K1 η1) , SFix.HFix-hmap H2 K2 η2 , {!hmap-resp!} ] 
            where hmap-resp : ∀ (Rs : Vec RelObj k) → RTMorph-resp (μRT H1 H2 RH) (μRT K1 K2 RK) (SFix.HFix-hmap H1 K1 η1) (SFix.HFix-hmap H2 K2 η2) Rs
                  hmap-resp Rs {x} {y} xy∈μRH-Rs = {!!}

--     HFixRel-fmap-preserves : ∀ {k} (H1 H2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) (RH : HRTObj* H1 H2) {Rs : Vec RelObj k} {Ss : Vec RelObj k}
--                              → (fs : (Rels^ k) [ Rs , Ss ])
--                              → ∀ {x : SFix.HFixObj H1 (vecfst Rs)} {y : SFix.HFixObj H2 (vecsnd Rs)}
--                              → RHFixRT H1 H2 RH Rs x y
--                              → RHFixRT H1 H2 RH Ss (SFix.HFix-fmap H1 (vecmfst fs) x) (SFix.HFix-fmap H2 (vecmsnd fs) y)



fixH : ∀ {k} → Functor [[ [Rels^ k ,Rels] , [Rels^ k ,Rels] ]] [Rels^ k ,Rels] 
fixH = record
         { F₀ = {!!}
         ; F₁ = {!!}
         ; identity = {!!}
         ; homomorphism = {!!}
         ; F-resp-≈ = {!!}
         } 


-- fixHRT : ∀ {k} → Functor (HRTCat k) (RTCat k)
-- fixHRT = ? 

-- fixRT : ∀ {k} → Functor [[ RTCat k , RTCat k ]] (RTCat k)
-- fixRT = ? 

{- WORKING COMMENT 

-- higher-order map for fixHFunc
{-# TERMINATING #-}
HFix-hmap : ∀ {k} (H1 H2 : Functor ([Rels^ k ,Rels]) ([Rels^ k ,Rels]))
          → NaturalTransformation H1 H2
          → NaturalTransformation (fixHFunc H1) (fixHFunc H2)
HFix-hmap {k} H1 H2 η = record { η = hη ; commute = commutes ; sym-commute = λ f → ≡.sym (commutes f)  } 
      where hη : (Xs : Vec RelObj k) → HFixFunctor H1 Xs → HFixFunctor H2 Xs
            -- need natural transformation from (Functor.F₀ H1 (fixHFunc H1)) to (Functor.F₀ H2 (fixHFunc H2))
            -- (H1 (fixHFunc H1)) Xs ------> (H1 (fixHFunc H2)) Xs
            --        |                               |
            --        v                               v
            -- (H2 (fixHFunc H1)) Xs ------> (H2 (fixHFunc H2)) Xs
            -- 
            -- -- alternative definition (by naturality)
            -- hη Xs (hffin x) = let r = HFix-hmap H1 H2 η -- n.t. from fixHFunc H1 to fixHFunc H2
            --                       -- n.t. from H1 (fixHFunc H1) to H2 (fixHFunc H1)
            --                       ηH1 = NaturalTransformation.η η (fixHFunc H1) 
            --                       -- function from H1 (fixHFunc H1) Xs to H2 (fixHFunc H1) Xs
            --                       ηH1x = NaturalTransformation.η ηH1 Xs x
            --                       -- n.t. from H2 (fixHFunc H1) to H2 (fixHFunc H2)
            --                       mapH2 = Functor.F₁ H2 r  
            --                   in hffin (NaturalTransformation.η mapH2 Xs ηH1x)
            hη Xs (hffin x) = let μη = HFix-hmap H1 H2 η -- n.t. from fixHFunc H1 to fixHFunc H2
                                  -- n.t. from H1 (fixHFunc H2) to H2 (fixHFunc H2)
                                  ηH2 = NaturalTransformation.η η (fixHFunc H2) 
                                  -- n.t. from H1 (fixHFunc H1) to H1 (fixHFunc H2)
                                  mapH1 = Functor.F₁ H1 μη
                                  mapH1-x = NaturalTransformation.η mapH1 Xs x
                              in hffin (NaturalTransformation.η ηH2 Xs mapH1-x)

            commutes : ∀ {Xs Ys : Vec RelObj k} → (f : VecFSpace Xs Ys)
                          → ∀ {xs : HFixFunctor H1 Xs}
                          → hη Ys (Functor.F₁ (fixHFunc H1) f xs) ≡ Functor.F₁ (fixHFunc H2) f (hη Xs xs)


    -- Commutativity proof given by naturality 'cube' 
    -- where each face is a naturality square for a different n.t. 
    -- The front and back faces are the naturality squares for hη Xs
    -- and hη Ys, respectively. 
    -- To prove commutativity we use naturality of the top and right faces, 
    -- called H1μη-commutes and ημH2-commutes, respectively. 
    -- 
    -- (H1 μH1) Xs ------> (H1 μH2) Xs
    --       |   \               |   \
    --       v    \              v    \
    -- (H2 μH1) Xs \-----> (H2 μH2) Xs \
    --        \     \             \     \
    --         \     \             \     \
    --          \  (H1 μH1) Ys ------> (H1 μH2) Ys
    --           \    |              \    | 
    --            \   v               \   v 
    --             (H2 μH1) Ys ------> (H2 μH2) Ys
    -- 
    -- 
    -- goal : hη Ys (Functor.F₁ (fixHFunc H1) f x) 
    --        ≡ Functor.F₁ (fixHFunc H2) f (hη Xs x)
    -- 
    -- i.e. hη Ys (HFix-fmap H1 f x)
    --      ≡ HFix-fmap H2 f (hη Xs x)
            commutes {Xs} {Ys} fs {hffin x} = 
                  let μη = HFix-hmap H1 H2 η
                      -- H1μη : H1 μH1 => H1 μH2  ()
                      H1μη = Functor.F₁ H1 μη
                      -- commutativity of top face on cube 
                      H1μη-commutes = NaturalTransformation.commute H1μη {Xs} {Ys} fs {x}
                      -- H1μη-x : (H1 μH2) Xs
                      H1μη-x = NaturalTransformation.η H1μη Xs x
                      -- ημH2 : H1 μH2 => H2 μH2  (top right and bottom right vertical arrows)
                      ημH2 = NaturalTransformation.η η (fixHFunc H2)
                      -- commutativity of right face on cube
                      ημH2-commutes = NaturalTransformation.commute ημH2 {Xs} {Ys} fs {H1μη-x}
                      H1μH1-fs = Functor.F₁ (Functor.F₀ H1 (fixHFunc H1)) fs
                      H1μH2-fs = Functor.F₁ (Functor.F₀ H1 (fixHFunc H2)) fs
                      H2μH2-fs = Functor.F₁ (Functor.F₀ H2 (fixHFunc H2)) fs
                    in ≡.cong hffin 
                    (begin 
                      NaturalTransformation.η ημH2 Ys (NaturalTransformation.η H1μη Ys (H1μH1-fs x))
                      ≡⟨ ≡.cong (NaturalTransformation.η ημH2 Ys) H1μη-commutes  ⟩ 
                      NaturalTransformation.η ημH2 Ys (H1μH2-fs (NaturalTransformation.η H1μη Xs x))
                      ≡⟨ ημH2-commutes ⟩ 
                      H2μH2-fs (NaturalTransformation.η ημH2 Xs (NaturalTransformation.η H1μη Xs x)) ∎)


-- TODO.. try showing HFixFullFunctor H is colimit of H 


-- END MUTUAL 


{-# TERMINATING #-}
HFix-hmap-identity : ∀ {k} (H : Functor ([Rels^ k ,Rels]) ([Rels^ k ,Rels]))
                    → [Rels^ k ,Rels]  Categories.Category.[ 
                      HFix-hmap H H (Category.id [[ [Rels^ k ,Rels] , [Rels^ k ,Rels] ]] {H}) 
                      ≈ Category.id [Rels^ k ,Rels] {fixHFunc H}
                    ]
HFix-hmap-identity {k} H {As} {hffin x} = 
  let idH = Category.id [[ [Rels^ k ,Rels] , [Rels^ k ,Rels] ]] {H}
      idH-μH = NaturalTransformation.η idH (fixHFunc H)
      Hid≈id = Functor.identity H {fixHFunc H}

      μidH≈id : [Rels^ k ,Rels] Categories.Category.[
                    HFix-hmap H H (Category.id [[ [Rels^ k ,Rels] , [Rels^ k ,Rels] ]])
                    ≈ Category.id [Rels^ k ,Rels] ] 
      μidH≈id = HFix-hmap-identity H 
      --
      μidH  = HFix-hmap H H idH
      Hid-resp = Functor.F-resp-≈ H {fixHFunc H} {fixHFunc H} {μidH} {Category.id [Rels^ k ,Rels]} μidH≈id
      -- HμidH = Functor.F₁ H μidH
      -- HμidH-As = NaturalTransformation.η HμidH As
    in ≡.cong hffin 
        (begin      
          NaturalTransformation.η (Functor.F₁ H μidH) As x
          ≡⟨ Hid-resp ⟩      
          NaturalTransformation.η (Functor.F₁ H (Category.id [Rels^ k ,Rels])) As x
          ≡⟨ Hid≈id {As} {x} ⟩      
          x    ∎) 



{-# TERMINATING #-}
HFix-hmap-homomorphism : ∀ {k} (H1 H2 H3 : Functor ([Rels^ k ,Rels]) ([Rels^ k ,Rels]))
                    → (f : NaturalTransformation H1 H2) → (g : NaturalTransformation H2 H3)
                    → [Rels^ k ,Rels]  Categories.Category.[ 
                      HFix-hmap H1 H3 (g ∘v f)  
                      ≈ HFix-hmap H2 H3 g ∘v HFix-hmap H1 H2 f
                    ]
HFix-hmap-homomorphism {k} H1 H2 H3 f g {Xs} {hffin x} = 
    let μg : NaturalTransformation (fixHFunc H2) (fixHFunc H3)
        μg       = HFix-hmap H2 H3 g
        -- 
        μf : NaturalTransformation (fixHFunc H1) (fixHFunc H2)
        μf       = HFix-hmap H1 H2 f
        -- 
        μg∘f : NaturalTransformation (fixHFunc H1) (fixHFunc H3)
        μg∘f     = HFix-hmap H1 H3 (g ∘v f)
        -- 
        g-μH3 : NaturalTransformation 
              (Functor.F₀ H2 (fixHFunc H3)) 
              (Functor.F₀ H3 (fixHFunc H3))
        g-μH3    = NaturalTransformation.η g (fixHFunc H3) 
        -- 
        g-μH3-Xs : Functor.F₀ (Functor.F₀ H2 (fixHFunc H3)) Xs 
                 → Functor.F₀ (Functor.F₀ H3 (fixHFunc H3)) Xs 
        g-μH3-Xs = NaturalTransformation.η g-μH3 Xs
        --        
        f-μH1 : NaturalTransformation 
              (Functor.F₀ H1 (fixHFunc H1))  
              (Functor.F₀ H2 (fixHFunc H1))
        f-μH1    = NaturalTransformation.η f (fixHFunc H1) 
        --
        f-μH1-Xs : Functor.F₀ (Functor.F₀ H1 (fixHFunc H1)) Xs 
                 → Functor.F₀ (Functor.F₀ H2 (fixHFunc H1)) Xs 
        f-μH1-Xs = NaturalTransformation.η f-μH1 Xs
        --
        f-μH2 : NaturalTransformation
              (Functor.F₀ H1 (fixHFunc H2)) 
              (Functor.F₀ H2 (fixHFunc H2))
        f-μH2    = NaturalTransformation.η f (fixHFunc H2) 
        -- 
        f-μH2-Xs : Functor.F₀ (Functor.F₀ H1 (fixHFunc H2)) Xs 
                 → Functor.F₀ (Functor.F₀ H2 (fixHFunc H2)) Xs 
        f-μH2-Xs = NaturalTransformation.η f-μH2 Xs
        --
        f-μH3 : NaturalTransformation
              (Functor.F₀ H1 (fixHFunc H3)) 
              (Functor.F₀ H2 (fixHFunc H3))
        f-μH3    = NaturalTransformation.η f (fixHFunc H3) 
        -- 
        f-μH3-Xs : Functor.F₀ (Functor.F₀ H1 (fixHFunc H3)) Xs 
                 → Functor.F₀ (Functor.F₀ H2 (fixHFunc H3)) Xs 
        f-μH3-Xs = NaturalTransformation.η f-μH3 Xs
        --
        H1-μg∘f : NaturalTransformation
           (Functor.F₀ H1 (fixHFunc H1)) 
           (Functor.F₀ H1 (fixHFunc H3))
        H1-μg∘f  = Functor.F₁ H1 μg∘f
        -- 
        H1-μg∘μf : NaturalTransformation
              (Functor.F₀ H1 (fixHFunc H1)) 
              (Functor.F₀ H1 (fixHFunc H3))
        H1-μg∘μf = Functor.F₁ H1 (μg ∘v μf)
        -- 
        μg∘f≈μg∘μf : [Rels^ k ,Rels] Categories.Category.[ 
          HFix-hmap H1 H3 (g ∘v f) ≈ HFix-hmap H2 H3 g ∘v HFix-hmap H1 H2 f ]
        μg∘f≈μg∘μf     = HFix-hmap-homomorphism H1 H2 H3 f g 
        -- 
        H1μg∘f≈H1μg∘μf : [Rels^ k ,Rels] Categories.Category.[
           Functor.F₁ H1 (HFix-hmap H1 H3 (g ∘v f)) 
           ≈ Functor.F₁ H1 (HFix-hmap H2 H3 g ∘v HFix-hmap H1 H2 f) ]
        H1μg∘f≈H1μg∘μf = Functor.F-resp-≈ H1 {f = μg∘f} {g = μg ∘v μf} μg∘f≈μg∘μf
        --
        H2-μg : NaturalTransformation
            (Functor.F₀ H2 (fixHFunc H2))  
            (Functor.F₀ H2 (fixHFunc H3))
        H2-μg = Functor.F₁ H2 μg
        -- 
        H1-μf : NaturalTransformation
            (Functor.F₀ H1 (fixHFunc H1))  
            (Functor.F₀ H1 (fixHFunc H2))
        H1-μf = Functor.F₁ H1 μf
        --
        H2-μg-Xs : Functor.F₀ (Functor.F₀ H2 (fixHFunc H2)) Xs 
                 → Functor.F₀ (Functor.F₀ H2 (fixHFunc H3)) Xs 
        H2-μg-Xs = NaturalTransformation.η H2-μg Xs

      in ≡.cong (hffin ∘' g-μH3-Xs) (begin 
            f-μH3-Xs (NaturalTransformation.η (H1-μg∘f) Xs x)
          ≡⟨ ≡.cong f-μH3-Xs H1μg∘f≈H1μg∘μf ⟩ 
            f-μH3-Xs (NaturalTransformation.η (Functor.F₁ H1 (μg ∘v μf)) Xs x)
          ≡⟨ NaturalTransformation.commute f (μg ∘v μf) ⟩ 
            NaturalTransformation.η (Functor.F₁ H2 (μg ∘v μf)) Xs (f-μH1-Xs x)
          ≡⟨ Functor.homomorphism H2 ⟩ 
            (NaturalTransformation.η (Functor.F₁ H2 μg ∘v Functor.F₁ H2 μf)) Xs (f-μH1-Xs x)
          ≡⟨ ≡.cong H2-μg-Xs (NaturalTransformation.sym-commute f μf) ⟩ 
            NaturalTransformation.η H2-μg Xs (f-μH2-Xs (NaturalTransformation.η H1-μf Xs x))
          ∎)

{-# TERMINATING #-}
HFix-hmap-F-resp : ∀ {k} (H1 H2 : Functor ([Rels^ k ,Rels]) ([Rels^ k ,Rels]))
                    → (f g : NaturalTransformation H1 H2) 
                    → [[ [Rels^ k ,Rels] , [Rels^ k ,Rels] ]] Categories.Category.[ f ≈ g ]
                    → [Rels^ k ,Rels]  Categories.Category.[ 
                      HFix-hmap H1 H2 f ≈ HFix-hmap H1 H2 g 
                    ]
HFix-hmap-F-resp H1 H2 f g f≈g {Xs} {hffin x} = 
  let f-μH2    = NaturalTransformation.η f (fixHFunc H2) 
      f-μH2-Xs = NaturalTransformation.η f-μH2 Xs
      g-μH2    = NaturalTransformation.η g (fixHFunc H2) 
      g-μH2-Xs = NaturalTransformation.η g-μH2 Xs
      μf       = HFix-hmap H1 H2 f
      H1-μf    = Functor.F₁ H1 μf
      H1-μf-Xs = NaturalTransformation.η H1-μf Xs
      μg       = HFix-hmap H1 H2 g
      H1-μg    = Functor.F₁ H1 μg
      H1-μg-Xs = NaturalTransformation.η H1-μg Xs

    in ≡.cong hffin (begin  
                    f-μH2-Xs (H1-μf-Xs x) 
                    ≡⟨ ≡.cong f-μH2-Xs (Functor.F-resp-≈ H1 (HFix-hmap-F-resp H1 H2 f g f≈g)) ⟩   
                    f-μH2-Xs (H1-μg-Xs x) 
                    ≡⟨ f≈g ⟩   
                    g-μH2-Xs (H1-μg-Xs x) ∎) 




-- fixpoint of a higher order functor H
fixH : ∀ {k} → Functor [[ [Rels^ k ,Rels] , [Rels^ k ,Rels] ]] [Rels^ k ,Rels] 
fixH = record
  { F₀ = λ H → fixHFunc H
  ; F₁ = λ {H1} {H2} η → HFix-hmap H1 H2 η
  ; identity = λ {H} → HFix-hmap-identity H
  ; homomorphism = λ {H1} {H2} {H3} {f} {g} → HFix-hmap-homomorphism H1 H2 H3 f g
  ; F-resp-≈ = λ {H1} {H2} {f} {g} f≈g → HFix-hmap-F-resp H1 H2 f g f≈g
  } 





hin : ∀ {k} → (H : Functor [Rels^ k ,Rels] [Rels^ k ,Rels]) → NaturalTransformation (Functor.F₀ H (fixHFunc H)) (fixHFunc H)
hin H = record { η = λ { Xs x → hffin x  }
                ; commute = λ f → ≡.refl
                ; sym-commute = λ f → ≡.refl } 

hinv : ∀ {k} → (H : Functor [Rels^ k ,Rels] [Rels^ k ,Rels]) → NaturalTransformation (fixHFunc H) (Functor.F₀ H (fixHFunc H)) 
hinv H = 
  record { η = λ { X (hffin x) → x } 
         ; commute = λ { {Xs} {Ys} fs {hffin x} → ≡.refl  }
         ; sym-commute = λ { {Xs} {Ys} fs {hffin x}  → ≡.refl }  }

fix-iso : ∀ {k} (H : Functor [Rels^ k ,Rels] [Rels^ k ,Rels])
            (Xs : Vec RelObj k) 
            → Categories.Morphism.Iso Rels (NaturalTransformation.η (hinv H) Xs) (NaturalTransformation.η (hin H) Xs)
fix-iso H Xs = record { isoˡ = λ { {hffin x} → ≡.refl } 
                      ; isoʳ = ≡.refl } 


-- hin, hinv form natural isomorphism 
hhin : ∀ {k} → (H : Functor [Rels^ k ,Rels] [Rels^ k ,Rels]) → NaturalIsomorphism (fixHFunc H) (Functor.F₀ H (fixHFunc H))
hhin H = record { F⇒G = hinv H ; F⇐G = hin H ; iso = fix-iso H }



mutual 
  {-# TERMINATING #-}
  foldH-η : ∀ {k} (H : Functor [Rels^ k ,Rels] [Rels^ k ,Rels])
              (F : Functor (Rels^ k) Rels)
              (η : NaturalTransformation (Functor.F₀ H F) F)
              (Xs : Vec RelObj k)
              → Functor.F₀ (fixHFunc H) Xs 
              → Functor.F₀ F Xs 
  foldH-η H F η Xs (hffin x) = 
    let Hη : NaturalTransformation (Functor.F₀ H (Functor.F₀ H F))
                                  (Functor.F₀ H F)
        Hη = Functor.F₁ H η 

        Hfold : NaturalTransformation (Functor.F₀ H (fixHFunc H))
                                      (Functor.F₀ H F)
        Hfold = Functor.F₁ H (foldH H F η)

      in NaturalTransformation.η (η ∘v Hfold) Xs x 

  -- -- commutativity of foldH is given by 
  -- 
  -- HμH Xs ------> HF Xs ------> F Xs 
  --   |              |            |
  --   |              |            |    
  --   v              v            v     
  -- HμH Ys ------> HF Ys ------> F Ys
  -- 
  -- where the right square commutes by naturality of η 
  -- and the left square commutes by naturality of H (foldH H F η)
  foldH-commute : ∀ {k} (H : Functor [Rels^ k ,Rels] [Rels^ k ,Rels])
                    → (F : Functor (Rels^ k) Rels)
                    → (η : NaturalTransformation (Functor.F₀ H F) F)
                    → {Xs Ys : Vec RelObj k}
                    → (f : VecFSpace Xs Ys)
                    → Rels Categories.Category.[
                        foldH-η H F η Ys ∘' (Functor.F₁ (fixHFunc H) f)
                        ≈ Functor.F₁ F f ∘' (foldH-η H F η Xs)
                    ]
  foldH-commute H F η {Xs} {Ys} f {hffin x} = 
    let η-Ys = NaturalTransformation.η η Ys
        η-Xs = NaturalTransformation.η η Xs
        H-foldη = Functor.F₁ H (foldH H F η)
        H-foldη-Xs = NaturalTransformation.η H-foldη Xs
        H-foldη-Ys = NaturalTransformation.η H-foldη Ys
        HμH = Functor.F₀ H (fixHFunc H)
        HμH-f = Functor.F₁ HμH f
        -- r = foldH-commute H F η f x
        
        HF-f = Functor.F₁ (Functor.F₀ H F) f
        
        η-com = NaturalTransformation.commute η

        -- H (foldH H F η) is a natural transformation 
        -- from HμH to HF. we use it's commutativity property 
        -- to prove that foldH is commutative 
        H-foldη-com : 
          NaturalTransformation.η H-foldη Ys (Functor.F₁ HμH f x)
          ≡ Functor.F₁ (Functor.F₀ H F) f (NaturalTransformation.η H-foldη Xs x)
        H-foldη-com = 
          NaturalTransformation.commute (Functor.F₁ H (foldH H F η)) f

     in begin
       η-Ys (H-foldη-Ys (HμH-f x))
   ≡⟨ ≡.cong η-Ys H-foldη-com ⟩
       η-Ys (HF-f (H-foldη-Xs x))
     ≡⟨ η-com f ⟩
       Functor.F₁ F f (η-Xs (H-foldη-Xs x))
     ∎   


  foldH : ∀ {k} → (H : Functor [Rels^ k ,Rels] [Rels^ k ,Rels]) 
          → (F : Functor (Rels^ k) Rels)
          → NaturalTransformation (Functor.F₀ H F) F
          → NaturalTransformation (fixHFunc H) F
  foldH H F η = 
    record { η = foldH-η H F η  
           ; commute = foldH-commute H F η
           ; sym-commute = λ {Xs} {Ys} f {x} → ≡.sym (foldH-commute H F η f {x}) } 







-}


-- {-# OPTIONS --allow-unsolved-metas #-}
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
open import RelSem.RelCats

open import Utils using (big⊤ ; bigtt)


module RelSem.HFixRel where

import HFixFunctorLib as SetFix


-- -- definition for sets
-- -- data HFixObj (H : Functor ([[ C , Sets ]]) [[ C , Sets ]] ) : C.Obj → Set
-- data HFixObj H where
--   hin : ∀ {As : C.Obj} → Functor.F₀ (Functor.F₀ H (fixH₀ H)) As → HFixObj H As

-- data HFixObj {k} (H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])) : (Rs : Vec RelObj k) → Set → Set → Set  where

open RelObj
open RelMorph


open HRTObj*
open HRTObj


-- compute fixpoint of relation transformer RH
module object-fixpoint-rel {k : ℕ} where

    HFunc = Functor [Sets^ k ,Sets] [Sets^ k ,Sets]

    {-# NO_POSITIVITY_CHECK #-}
    data HRTFixRel (H1 H2 : HFunc) (RH  : HRTObj* H1 H2)
        : ∀ (Rs : Vec RelObj k) → REL (SetFix.HFixObj H1 (vecfst Rs)) (SetFix.HFixObj H2 (vecsnd Rs))

    -- -- need to encode the fact that RH is over H1, H2 using RTObj*
    {-# TERMINATING #-}
    fixHRT₀* : ∀ (H1 H2 : HFunc) (RH : HRTObj* H1 H2) → RTObj* (SetFix.fixH₀ H1) (SetFix.fixH₀ H2)

    {-# TERMINATING #-}
    fixHRT₀ : ∀ (H1 H2 : HFunc) (RH : HRTObj* H1 H2) → RTObj k

    ---------------------------------------------------------------------------
    -- end types
    ---------------------------------------------------------------------------

    fixHRT₀ H1 H2 RH = RT[ (SetFix.fixH₀ H1) , (SetFix.fixH₀ H2) , (fixHRT₀* H1 H2 RH) ]


    -- HRTFixRelObj H1 H2 RH Rs = R[ SetFix.HFixObj H1 (vecfst Rs) , SetFix.HFixObj H2 (vecsnd Rs) , HRTFixRel H1 H2 RH Rs ]

    -- HRTFixRelObj2 H1 H2 RH Rs = RTObj*.F*RelObj (RTObj.F* (endoRT₀ RH (fixHRT₀ H1 H2 RH))) Rs
    -- HFixRel-fmap2 H1 H2 RH ms = RTObj*.F*Rel-map (RTObj.F* (endoRT₀ RH (fixHRT₀ H1 H2 RH))) ms

    -- F*Rel : ∀ (Rs : Vec RelObj k) → REL (F1.₀ (vecfst Rs)) (F2.₀ (vecsnd Rs))
    data HRTFixRel H1 H2 RH where
        rhin : ∀ {Rs  : Vec RelObj k}
                → {x : Functor.F₀ (Functor.F₀ H1 (SetFix.fixH₀ H1)) (vecfst Rs)}
                → {y : Functor.F₀ (Functor.F₀ H2 (SetFix.fixH₀ H2)) (vecsnd Rs)}
                -- → RTObj*.F*Rel (RTObj.F*Data (H*Obj RH (fixHRT₀ H1 H2 RH))) Rs x y
                → RTObj.F*Rel ((HEndo-obj HRT[ H1 , H2 , RH ]) (fixHRT₀ H1 H2 RH)) Rs x y
                → HRTFixRel H1 H2 RH Rs (SetFix.hin {k} {H1} {vecfst Rs} x)
                                      (SetFix.hin {k} {H2} {vecsnd Rs} y)

    fixHRT₀* H1 H2 RH =
      record { F*Rel = λ Rs x y → HRTFixRel H1 H2 RH Rs x y
             ; F*Rel-preserves = fix-preserves }
         where fix-preserves : ∀ {Rs Ss : Vec RelObj k} (ms : Rels^ k [ Rs , Ss ])
                               → preservesRel (HRTFixRel H1 H2 RH Rs) (HRTFixRel H1 H2 RH Ss)
                                               (Functor.₁ (SetFix.fixH₀ H1) (vecmfst ms))
                                               (Functor.₁ (SetFix.fixH₀ H2) (vecmsnd ms))
               fix-preserves ms (rhin p) = rhin (H*RTRel-preserves RH (fixHRT₀ H1 H2 RH) ms p)
               -- Goal: H*RTRel RH (fixHRT₀ H1 H2 RH) Ss
               --       (Functor.F₁ (Functor.F₀ H1 (SetFix.fixH₀ H1)) (vecmfst ms) x)
               --       (Functor.F₁ (Functor.F₀ H2 (SetFix.fixH₀ H2)) (vecmsnd ms) y)
               --
               -- Have - p : H*RTRel RH (fixHRT₀ H1 H2 RH) Rs x y



-- λ { ms {.(SetFix.hin _)} {.(SetFix.hin _)} (rhin p) →
-- rhin (H*RTRel-preserves RH (fixHRT₀ H1 H2 RH) ms p) }  }

    -- Goal: RTObj*.F*Rel
    --       (RTObj.F*Data (HEndo-obj HRT[ H1 , H2 , RH ] (fixHRT₀ H1 H2 RH))) Ss
    --       (Functor.F₁ (Functor.F₀ H1 (SetFix.fixH₀ H1)) (vecmfst ms) x)
    --       (Functor.F₁ (Functor.F₀ H2 (SetFix.fixH₀ H2)) (vecmsnd ms) y)
    -- ————————————————————————————————————————————————————————————
    -- p  : RTObj*.F*Rel
    --      (RTObj.F*Data (HEndo-obj HRT[ H1 , H2 , RH ] (fixHRT₀ H1 H2 RH)))
    --      Rs x y

open object-fixpoint-rel public 



-------------------------------------------------------
-- definitions
-----------------------------------------------------
module morph-fixpoint-rel {k : ℕ} where

  mutual

    {-# TERMINATING #-}
    fixHRT₁ : ∀ (H1 H2 : HFunc) (RH : HRTObj* H1 H2)
              → (K1 K2 : HFunc) (RK : HRTObj* K1 K2)
              → HRTMorph HRT[ H1 , H2 , RH ] HRT[ K1 , K2 , RK ]
              → RTMorph (fixHRT₀ H1 H2 RH) (fixHRT₀ K1 K2 RK)

    fixHRT₁ H1 H2 RH K1 K2 RK σ@(HRTM[ σ1 ,  σ2 , σ-preserves ]) =
      RTM[ (SetFix.fixH₁ H1 K1 σ1)
         , SetFix.fixH₁ H2 K2 σ2
         , (λ {Rs} → fixHRT₁-preserves H1 H2 RH K1 K2 RK σ Rs ) ]

                    -- we have a naturality square in [Rels^k ,Rels]
                    --
                    --   (RH* Rt)   ==>  (RH* St)
                    --     ||             ||
                    --     vv             vv
                    --   (RK* Rt)   ==>  (RK* St)
                    --
                    -- with Rt = fixHRT₀ (H1 H2 RH)
                    --      St = fixHRT₀ (K1 K2 KH)

    -- note we aren't actually using σ-preserves....
    fixHRT₁-preserves : ∀ (H1 H2 : HFunc) (RH : HRTObj* H1 H2)
                → (K1 K2 : HFunc) (RK : HRTObj* K1 K2)
                → (σ : HRTMorph HRT[ H1 , H2 , RH ] HRT[ K1 , K2 , RK ])
                → (Rs : Vec RelObj k)
                → RTMorph-preserves (fixHRT₀ H1 H2 RH) (fixHRT₀ K1 K2 RK)
                               (SetFix.fixH₁ H1 K1 (HRTMorph.σ1 σ))
                               (SetFix.fixH₁ H2 K2 (HRTMorph.σ2 σ)) Rs
    fixHRT₁-preserves H1 H2 RH K1 K2 RK σ@(HRTM[ σ1 , σ2 , σ-preserves ]) Rs
              {(SetFix.hin x)} {(SetFix.hin y)} (rhin p) = rhin (preserves (f1-comp Rs) p) 
-- p : H*RTRel RH (fixHRT₀ H1 H2 RH) Rs x y
-- 
-- Goal: H*RTRel RK (fixHRT₀ H1 H2 RH) Rs
--       (NaturalTransformation.η
--        (NaturalTransformation.η σ1 (SetFix.fixH₀ K1)) (vecfst Rs)
--        (NaturalTransformation.η (Functor.F₁ H1 (SetFix.fixH₁ H1 K1 σ1)) (vecfst Rs) x))
--       (NaturalTransformation.η
--        (NaturalTransformation.η σ2 (SetFix.fixH₀ K2)) (vecsnd Rs)
--        (NaturalTransformation.η (Functor.F₁ H2 (SetFix.fixH₁ H2 K2 σ2)) (vecsnd Rs) y))
                where
                    RH* : Functor (RTCat k) [Rels^ k ,Rels]
                    RH* = HRTObj*.H* RH
                    --
                    RK* : Functor (RTCat k) [Rels^ k ,Rels]
                    RK* = HRTObj*.H* RK

                    RH*μH : Functor (Rels^ k) Rels
                    RH*μH = Functor.F₀ RH* (fixHRT₀ H1 H2 RH)

                    RH*μK : Functor (Rels^ k) Rels
                    RH*μK = Functor.F₀ RH* (fixHRT₀ K1 K2 RK)

                    μσ : RTMorph (fixHRT₀ H1 H2 RH) (fixHRT₀ K1 K2 RK)
                    μσ = fixHRT₁ H1 H2 RH K1 K2 RK σ

                    RH*μσ : [Rels^ k ,Rels] [ RH*μH , RH*μK ]
                    RH*μσ = Functor.F₁ RH* μσ

                    RK*μH : Functor (Rels^ k) Rels
                    RK*μH = Functor.F₀ RK* (fixHRT₀ H1 H2 RH)

                    RK*μK : Functor (Rels^ k) Rels
                    RK*μK = Functor.F₀ RK* (fixHRT₀ K1 K2 RK)

                    RK*μσ : [Rels^ k ,Rels] [ RK*μH , RK*μK ]
                    RK*μσ = Functor.F₁ RK* μσ

                    σ-μH : [Rels^ k ,Rels] [ RH*μH , RK*μH ]
                    σ-μH = NaturalTransformation.η (HRTMorph.σRT σ) (fixHRT₀ H1 H2 RH)

                    σ-μK : [Rels^ k ,Rels] [ RH*μK , RK*μK ]
                    σ-μK = NaturalTransformation.η (HRTMorph.σRT σ) (fixHRT₀ K1 K2 RK)

                    -- top, right sides of square
                    f1 : [Rels^ k ,Rels] [ RH*μH , RK*μK ]
                    f1 = σ-μK ∘v RH*μσ
                    {- not needed for the definition, but here is the naturality square/proof
                    f2 : [Rels^ k ,Rels] [ RH*μH , RK*μK ]
                    f2 = RK*μσ ∘v σ-μH

                    commutes : [Rels^ k ,Rels] [ f1 ≈ f2 ]
                    commutes = NaturalTransformation.commute (HRTMorph.σRT σ) μσ
                    -}

                    f1-comp : ∀ Rs → RelMorph (Functor.F₀ RH*μH Rs) (Functor.F₀ RK*μK Rs)
                    f1-comp Rs = NaturalTransformation.η f1 Rs


open morph-fixpoint-rel public

fixHRT : ∀ {k} → Functor (HRTCat k) (RTCat k)
fixHRT = record
           { F₀ = λ { HRT[ H1 , H2 , RH ] → fixHRT₀ H1 H2 RH }
           ; F₁ = λ { {HRT[ H1 , H2 , RH ]} {HRT[ K1 , K2 , RK ]} σ → fixHRT₁ H1 H2 RH K1 K2 RK σ }
           ; identity = λ { {HRT[ H1 , H2 , _ ]} → SetFix.fixH₁-identity H1  , SetFix.fixH₁-identity H2  }
           ; homomorphism = λ { {HRT[ H1 , H2 , _ ]} {HRT[ K1 , K2 , _ ]} {HRT[ J1 , J2 , _ ]} {f} {g}
                            → SetFix.fixH₁-homomorphism H1 K1 J1 (HRTMorph.σ1 f) (HRTMorph.σ1 g)
                            , SetFix.fixH₁-homomorphism H2 K2 J2 (HRTMorph.σ2 f) (HRTMorph.σ2 g) }
           ; F-resp-≈ = λ { {HRT[ H1 , H2 , _ ]} {HRT[ K1 , K2 , _ ]} {f} {g} (f1≈g1 , f2≈g2)
                      → (SetFix.fixH₁-F-resp H1 K1 (HRTMorph.σ1 f) (HRTMorph.σ1 g) f1≈g1)
                      , (SetFix.fixH₁-F-resp H2 K2 (HRTMorph.σ2 f) (HRTMorph.σ2 g) f2≈g2) }
           }

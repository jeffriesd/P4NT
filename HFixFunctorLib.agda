
-- {-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting --confluence-check #-}
-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite


-- open import Data.Nat

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; id to idnat)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Morphism using (Iso)
open import Data.Vec using (Vec ; _∷_; replicate) renaming (map to vmap)
open import Level renaming (zero to  lzero ; suc to lsuc)
open import Function using (flip) renaming (id to idf; _∘_ to _∘'_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open ≡.≡-Reasoning

open import SetCats

open import Utils


module HFixFunctorLib where

Set^ : ℕ → Set₁
Set^ k = Vec Set k

SetFunc : ℕ → Set₁
SetFunc k = (Set^ k → Set) 

HFunc : ℕ → Set₁
HFunc k = SetFunc k → SetFunc k

FMAP : ∀ {k} → SetFunc k → Set₁
FMAP {k} F = ∀ {As Bs : Set^ k} → VecFSpace As Bs → F As → F Bs

SetNat : ∀ {k} → (F G : SetFunc k) → Set₁
SetNat {k} F G = ∀ As → F As → G As

FID : ∀ {k} → (F : SetFunc k) → (Fmap : FMAP F) → Set₁
FID {k} F Fmap = ∀ {As} {xs} → Fmap {As} {As} (Category.id (Sets^ k )) xs ≡ xs

FHOMO : ∀ {k} → (F : SetFunc k) → FMAP F → Set₁ 
FHOMO {k} F Fmap = ∀ {As Bs Cs} 
      → {f : VecFSpace As Bs} → {g : VecFSpace Bs Cs}
      → ∀ {x} → Fmap (Category._∘_ (Sets^ k )  g f) x ≡ Fmap g (Fmap f x)

FRESP : ∀ {k} → (F : SetFunc k) → FMAP F → Set₁ 
FRESP F Fmap =  ∀ {As Bs} → {fs gs : VecFSpace As Bs} → pointwise-≈ fs gs → ∀ {x : F As} →  Fmap fs x ≡ Fmap gs x

-- combine components of a k-ary Set functor 
mkFunc : ∀ {k} 
         → (F0 : SetFunc k) 
         → (F1 : FMAP F0)
         → (Fid : FID F0 F1)
         → (Fhomo : FHOMO F0 F1)
         → (Fresp : FRESP F0 F1)
         → Functor (Sets^ k) Sets
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
HFOBJ k = Functor (Sets^ k) Sets → Functor (Sets^ k) Sets 

HFMAP : ∀ {k} → (H : HFOBJ k) → Set₁
HFMAP {k} H = ∀ {F G : Functor (Sets^ k) Sets} → NaturalTransformation F G → NaturalTransformation (H F) (H G)

HFID : ∀ {k} → (H : HFOBJ k) → (HFMAP H) → Set₁
 -- ; _≈_ = λ eta1 eta2 → ∀ Xs → NaturalTransformation.η eta1 Xs ≈ NaturalTransformation.η eta2 Xs
HFID {k} H Hmap = ∀ {F : Functor (Sets^ k) Sets} {Xs} {xs} → NaturalTransformation.η (Hmap {F} {F} (Category.id [Sets^ k ,Sets])) Xs xs ≡ NaturalTransformation.η {F = H F} (Category.id [Sets^ k ,Sets]) Xs xs

-- HFID2 : ∀ {k} (H0 : HFOBJ k) (H1 : HFMAP H0)
--           {A : Category.Obj [Sets^ k ,Sets]} 
--           → [Sets^ k ,Sets] Categories.Category.[
--                 H1 (Category.id [Sets^ k ,Sets]) 
--                 ≈ Category.id [Sets^ k ,Sets]   ]
-- HFID2 {k} H Hmap = {!   !} 


HFHOMO : ∀ {k} → (H : HFOBJ k) → HFMAP H → Set₁
HFHOMO {k} H Hmap =  ∀ {F G K : Functor (Sets^l k lzero) (Setsl lzero)} {f : NaturalTransformation F G} {g : NaturalTransformation G K}
          → {Xs : Vec Set k} {x : Functor.F₀ (H F) Xs} 
          → NaturalTransformation.η (Hmap (g ∘v f)) Xs x ≡
            NaturalTransformation.η (Hmap g) Xs (NaturalTransformation.η (Hmap f) Xs x) 

HFRESP : ∀ {k} → (H : HFOBJ k) → HFMAP H → Set₁
HFRESP {k} H Hmap = ∀ {A B : Functor (Sets^l k lzero) (Setsl lzero)} {f g : NaturalTransformation A B} 
          → (f≈g : {Xs : Vec Set k} {x : Functor.F₀ A Xs} → NaturalTransformation.η f Xs x ≡ NaturalTransformation.η g Xs x) 
          → {Xs : Vec Set k} {x : Functor.F₀ (H A) Xs} 
          → NaturalTransformation.η (Hmap f) Xs x ≡ NaturalTransformation.η (Hmap g) Xs x

mkHFunc : ∀ {k} 
         → (H0 : HFOBJ k)
         → (H1 : HFMAP H0)
         → (Hid : HFID H0 H1)
         → (Hhomo : HFHOMO H0 H1)
         → (Hresp : HFRESP H0 H1)
         → Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])
mkHFunc {k} H0 H1 Hid Hhomo Hresp = record
  { F₀ = H0
  ; F₁ = H1
  ; identity = Hid
  ; homomorphism = Hhomo
  ; F-resp-≈ = Hresp
  } 

  -- { F₀ = H0
  -- ; F₁ = H1
  -- ; identity = Hid
  -- ; homomorphism = Hhomo
  -- ; F-resp-≈ = Hresp
  -- } 



{-# NO_POSITIVITY_CHECK #-}
data HFixFunctor {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])): Vec Set k → Set 

{-# TERMINATING #-}
HFix-fmap : ∀ {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
            → FMAP (HFixFunctor H)

{-# TERMINATING #-}
HFix-id : ∀ {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
            → FID (HFixFunctor H) (HFix-fmap H)

{-# TERMINATING #-}
HFix-homo : ∀ {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
            → FHOMO (HFixFunctor H) (HFix-fmap H)

{-# TERMINATING #-}
HFix-resp : ∀ {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
            → FRESP (HFixFunctor H) (HFix-fmap H)

-------------------------------------------------------  
-- definitions
-----------------------------------------------------  

-- -- defined for convenience  
-- compute functorial fixpoint of higher order functor H 
fixHFunc : ∀ {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])) 
        → Functor (Sets^ k) Sets
fixHFunc H = (mkFunc (HFixFunctor H) (HFix-fmap H) (HFix-id H) (HFix-homo H) (HFix-resp H))


data HFixFunctor {k} H where
  hffin : ∀ {As : Set^ k}
          -- → Functor.F₀ (Functor.F₀ H 
          --         (mkFunc (HFixFunctor H) (HFix-fmap H) (HFix-id H) (HFix-homo H) (HFix-resp H))) As 
          → Functor.F₀ (Functor.F₀ H (fixHFunc H)) As 
          -- → HFixFunctor H As
          → HFixFunctor H As

-- use Functor.F₁ (H (μH)) : 
-- HFix-fmap {k} H {As} {Bs} gs (hffin {As} x) = hffin (Functor.F₁ (fixHFunc H) gs x)
-- 
-- have x : Functor.F₀ (Functor.F₀ H (fixHFunc H)) As
-- goal   : Functor.F₀ (Functor.F₀ H (fixHFunc H)) Bs
-- 
-- H0 (fixHFunc H) : [Set^ k ,Sets]
-- Functor.F₁ (H0 (fixHFunc H) ) : ∀ {As} {Bs} (gs : As → Bs) → H0 (fixHFunc H) As → H0 ()
HFix-fmap {k} H {As} {Bs} gs (hffin {As} x) = hffin (Functor.F₁ (Functor.F₀ H (fixHFunc H)) gs x)

HFix-id {k} H {As} {hffin x} = ≡.cong hffin (Functor.identity  (Functor.F₀ H (fixHFunc H)))

HFix-homo {k} H {As} {Bs} {Cs} {f} {g} {hffin x} = ≡.cong hffin (Functor.homomorphism (Functor.F₀ H (fixHFunc H)))

HFix-resp {k} H {As} {Bs} {f} {g} f≡g {hffin x} = ≡.cong hffin (Functor.F-resp-≈ (Functor.F₀ H (fixHFunc H)) f≡g)



-- higher-order map for fixHFunc
{-# TERMINATING #-}
HFix-hmap : ∀ {k} (H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
          → NaturalTransformation H1 H2
          → NaturalTransformation (fixHFunc H1) (fixHFunc H2)
HFix-hmap {k} H1 H2 η = record { η = hη ; commute = commutes ; sym-commute = λ f → ≡.sym (commutes f)  } 
      where hη : (Xs : Set^ k) → HFixFunctor H1 Xs → HFixFunctor H2 Xs
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

            commutes : ∀ {Xs Ys : Set^ k} → (f : VecFSpace Xs Ys)
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
HFix-hmap-identity : ∀ {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
                    → [Sets^ k ,Sets]  Categories.Category.[ 
                      HFix-hmap H H (Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] {H}) 
                      ≈ Category.id [Sets^ k ,Sets] {fixHFunc H}
                    ]
HFix-hmap-identity {k} H {As} {hffin x} = 
  let idH = Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] {H}
      idH-μH = NaturalTransformation.η idH (fixHFunc H)
      Hid≈id = Functor.identity H {fixHFunc H}

      μidH≈id : [Sets^ k ,Sets] Categories.Category.[
                    HFix-hmap H H (Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
                    ≈ Category.id [Sets^ k ,Sets] ] 
      μidH≈id = HFix-hmap-identity H 
      --
      μidH  = HFix-hmap H H idH
      Hid-resp = Functor.F-resp-≈ H {fixHFunc H} {fixHFunc H} {μidH} {Category.id [Sets^ k ,Sets]} μidH≈id
      -- HμidH = Functor.F₁ H μidH
      -- HμidH-As = NaturalTransformation.η HμidH As
    in ≡.cong hffin 
        (begin      
          NaturalTransformation.η (Functor.F₁ H μidH) As x
          ≡⟨ Hid-resp ⟩      
          NaturalTransformation.η (Functor.F₁ H (Category.id [Sets^ k ,Sets])) As x
          ≡⟨ Hid≈id {As} {x} ⟩      
          x    ∎) 



{-# TERMINATING #-}
HFix-hmap-homomorphism : ∀ {k} (H1 H2 H3 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
                    → (f : NaturalTransformation H1 H2) → (g : NaturalTransformation H2 H3)
                    → [Sets^ k ,Sets]  Categories.Category.[ 
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
        μg∘f≈μg∘μf : [Sets^ k ,Sets] Categories.Category.[ 
          HFix-hmap H1 H3 (g ∘v f) ≈ HFix-hmap H2 H3 g ∘v HFix-hmap H1 H2 f ]
        μg∘f≈μg∘μf     = HFix-hmap-homomorphism H1 H2 H3 f g 
        -- 
        H1μg∘f≈H1μg∘μf : [Sets^ k ,Sets] Categories.Category.[
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
HFix-hmap-F-resp : ∀ {k} (H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
                    → (f g : NaturalTransformation H1 H2) 
                    → [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] Categories.Category.[ f ≈ g ]
                    → [Sets^ k ,Sets]  Categories.Category.[ 
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
fixH : ∀ {k} → Functor [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] [Sets^ k ,Sets] 
fixH = record
  { F₀ = λ H → fixHFunc H
  ; F₁ = λ {H1} {H2} η → HFix-hmap H1 H2 η
  ; identity = λ {H} → HFix-hmap-identity H
  ; homomorphism = λ {H1} {H2} {H3} {f} {g} → HFix-hmap-homomorphism H1 H2 H3 f g
  ; F-resp-≈ = λ {H1} {H2} {f} {g} f≈g → HFix-hmap-F-resp H1 H2 f g f≈g
  } 





hin : ∀ {k} → (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) → NaturalTransformation (Functor.F₀ H (fixHFunc H)) (fixHFunc H)
hin H = record { η = λ { Xs x → hffin x  }
                ; commute = λ f → ≡.refl
                ; sym-commute = λ f → ≡.refl } 

hinv : ∀ {k} → (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) → NaturalTransformation (fixHFunc H) (Functor.F₀ H (fixHFunc H)) 
hinv H = 
  record { η = λ { X (hffin x) → x } 
         ; commute = λ { {Xs} {Ys} fs {hffin x} → ≡.refl  }
         ; sym-commute = λ { {Xs} {Ys} fs {hffin x}  → ≡.refl }  }

fix-iso : ∀ {k} (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
            (Xs : Vec Set k) 
            → Categories.Morphism.Iso Sets (NaturalTransformation.η (hinv H) Xs) (NaturalTransformation.η (hin H) Xs)
fix-iso H Xs = record { isoˡ = λ { {hffin x} → ≡.refl } 
                      ; isoʳ = ≡.refl } 


-- hin, hinv form natural isomorphism 
hhin : ∀ {k} → (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) → NaturalIsomorphism (fixHFunc H) (Functor.F₀ H (fixHFunc H))
hhin H = record { F⇒G = hinv H ; F⇐G = hin H ; iso = fix-iso H }



mutual 
  {-# TERMINATING #-}
  foldH-η : ∀ {k} (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
              (F : Functor (Sets^ k) Sets)
              (η : NaturalTransformation (Functor.F₀ H F) F)
              (Xs : Vec Set k)
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
  foldH-commute : ∀ {k} (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
                    → (F : Functor (Sets^ k) Sets)
                    → (η : NaturalTransformation (Functor.F₀ H F) F)
                    → {Xs Ys : Vec Set k}
                    → (f : VecFSpace Xs Ys)
                    → Sets Categories.Category.[
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


  foldH : ∀ {k} → (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) 
          → (F : Functor (Sets^ k) Sets)
          → NaturalTransformation (Functor.F₀ H F) F
          → NaturalTransformation (fixHFunc H) F
  foldH H F η = 
    record { η = foldH-η H F η  
           ; commute = foldH-commute H F η
           ; sym-commute = λ {Xs} {Ys} f {x} → ≡.sym (foldH-commute H F η f {x}) } 


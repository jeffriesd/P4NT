
-- {-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting --confluence-check #-}
-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite


-- open import Data.Nat

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
open ≡.≡-Reasoning

open import SetCats

open import Utils


module HFixFunctorLib where 

-- HFixObj -- data type , action on objects of the action on objects
-- fixHFunc -> rename to fixH₀ -- functor , action on objects of fixH
-- 


-- take a higher-order functor H and compute its fixpoint,
-- which is a first-order functor 
module object-fixpoint {k : ℕ} where 
-- (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])) where 

    HFunc : Set₁
    HFunc = Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]) 

    {-# NO_POSITIVITY_CHECK #-}
    data HFixObj (H : HFunc) : Vec Set k → Set 


    {-# TERMINATING #-}
    HFix-fmap : ∀ (H : HFunc) → {As Bs : Vec Set k} → VecMorph As Bs
                → HFixObj H As → HFixObj H Bs


    {-# TERMINATING #-}
    HFix-id : ∀ (H : HFunc) {As} {xs} → HFix-fmap H {As} {As} (Category.id (Sets^ k )) xs ≡ xs

    {-# TERMINATING #-}
    HFix-homo : ∀ (H : HFunc) {As Bs Cs} → {f : VecMorph As Bs} → {g : VecMorph Bs Cs}
                → ∀ {x} → HFix-fmap H (Category._∘_ (Sets^ k )  g f) x ≡ HFix-fmap H g (HFix-fmap H f x)

    {-# TERMINATING #-}
    HFix-resp : ∀ (H : HFunc) {As Bs} → {fs gs : VecMorph As Bs}
                → (Sets^ k) [ fs ≈  gs ]
                → ∀ {x : HFixObj H As} → HFix-fmap H fs x ≡ HFix-fmap H gs x

    fixH₀ : ∀ (H : HFunc) → Functor (Sets^ k) Sets

    data HFixObj H where
        hin : ∀ {As : Vec Set k}
                → Functor.F₀ (Functor.F₀ H (fixH₀ H)) As 
                → HFixObj H As

    HFix-fmap H {As} {Bs} gs (hin {As} x) = hin (Functor.F₁ (Functor.F₀ H (fixH₀ H)) gs x)

    HFix-id H {As} {hin x} = ≡.cong hin (Functor.identity  (Functor.F₀ H (fixH₀ H)))

    HFix-homo H {As} {Bs} {Cs} {f} {g} {hin x} = ≡.cong hin (Functor.homomorphism (Functor.F₀ H (fixH₀ H)))

    HFix-resp H {As} {Bs} {f} {g} f≡g {hin x} = ≡.cong hin (Functor.F-resp-≈ (Functor.F₀ H (fixH₀ H)) f≡g)

    fixH₀ H = record
                { F₀ = HFixObj H
                ; F₁ = HFix-fmap H
                ; identity = HFix-id H
                ; homomorphism = HFix-homo H
                ; F-resp-≈ = HFix-resp H
                }

open object-fixpoint public


-- take a higher-order natural transformation between H1 and H2 and
-- compute its fixpoint, which is a natural transformation
-- between the fixpoints of H1 and H2 
module morphism-fixpoint where 

  mutual 
      {-# TERMINATING #-}
      fixH₁-component : ∀ {k} {H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])}
                          → NaturalTransformation H1 H2 
                          → (Xs : Vec Set k) → HFixObj H1 Xs → HFixObj H2 Xs
      fixH₁-component {k} {H1} {H2} η Xs (hin x) = hin (NaturalTransformation.η ημH2 Xs (NaturalTransformation.η H1μη Xs x))
          where open Functor H1 renaming (F₀ to H1₀)
                open Functor H2 renaming (F₀ to H2₀)
                ημH2 : NaturalTransformation (H1₀ (fixH₀ H2)) (H2₀ (fixH₀ H2))
                ημH2 = NaturalTransformation.η η (fixH₀ H2) 
                H1μη : NaturalTransformation (H1₀ (fixH₀ H1)) (H1₀ (fixH₀ H2))
                H1μη = Functor.F₁ H1 (fixH₁ H1 H2 η)

                ημH1 : NaturalTransformation (H1₀ (fixH₀ H1)) (H2₀ (fixH₀ H1))
                ημH1 = NaturalTransformation.η η (fixH₀ H1) 
                H2μη : NaturalTransformation (H2₀ (fixH₀ H1)) (H2₀ (fixH₀ H2))
                H2μη = Functor.F₁ H2 (fixH₁ H1 H2 η)

      -- higher-order map for fixH₀
      {-# TERMINATING #-}
      fixH₁ : ∀ {k} (H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
              → NaturalTransformation H1 H2
              → NaturalTransformation (fixH₀ H1) (fixH₀ H2)
      fixH₁ {k} H1 H2 η = record { η = μη ; commute = commutes ; sym-commute = λ f → ≡.sym (commutes f)  } 
          where μη : (Xs : Vec Set k) → HFixObj H1 Xs → HFixObj H2 Xs
                μη = fixH₁-component η 
  
                commutes : ∀ {Xs Ys : Vec Set k} → (f : VecMorph Xs Ys)
                              → ∀ {x : HFixObj H1 Xs}
                              → μη Ys (Functor.F₁ (fixH₀ H1) f x) ≡ Functor.F₁ (fixH₀ H2) f (μη Xs x)
  
          -- Commutativity proof given by 'naturality cube' 
          -- where each face is a naturality square for a different n.t. 
          -- The front and back faces are the naturality squares for μη Xs
          -- and μη Ys, respectively. 
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
          -- goal : μη Ys (Functor.F₁ (fixH₀ H1) f x) 
          --        ≡ Functor.F₁ (fixH₀ H2) f (μη Xs x)
          -- 
          -- i.e. μη Ys (HFix-fmap H1 f x)
          --      ≡ HFix-fmap H2 f (μη Xs x)
                commutes {Xs} {Ys} fs {hin x} = 
                      let μη = fixH₁ H1 H2 η
                          -- H1μη : H1 μH1 => H1 μH2  ()
                          H1μη = Functor.F₁ H1 μη
                          -- commutativity of top face on cube 
                          H1μη-commutes = NaturalTransformation.commute H1μη {Xs} {Ys} fs {x}
                          -- H1μη-x : (H1 μH2) Xs
                          H1μη-x = NaturalTransformation.η H1μη Xs x
                          -- ημH2 : H1 μH2 => H2 μH2  (top right and bottom right vertical arrows)
                          ημH2 = NaturalTransformation.η η (fixH₀ H2)
                          -- commutativity of right face on cube
                          ημH2-commutes = NaturalTransformation.commute ημH2 {Xs} {Ys} fs {H1μη-x}
                          H1μH1-fs = Functor.F₁ (Functor.F₀ H1 (fixH₀ H1)) fs
                          H1μH2-fs = Functor.F₁ (Functor.F₀ H1 (fixH₀ H2)) fs
                          H2μH2-fs = Functor.F₁ (Functor.F₀ H2 (fixH₀ H2)) fs
                          in ≡.cong hin 
                          (begin 
                          NaturalTransformation.η ημH2 Ys (NaturalTransformation.η H1μη Ys (H1μH1-fs x))
                          ≡⟨ ≡.cong (NaturalTransformation.η ημH2 Ys) H1μη-commutes  ⟩ 
                          NaturalTransformation.η ημH2 Ys (H1μH2-fs (NaturalTransformation.η H1μη Xs x))
                          ≡⟨ ημH2-commutes ⟩ 
                          H2μH2-fs (NaturalTransformation.η ημH2 Xs (NaturalTransformation.η H1μη Xs x)) ∎)
  
open morphism-fixpoint public



module fixpoint-functor-laws where 
    
    {-# TERMINATING #-}
    fixH₁-identity : ∀ {k} (H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
                        → [Sets^ k ,Sets]  Categories.Category.[ 
                          fixH₁ H H (Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] {H}) 
                          ≈ Category.id [Sets^ k ,Sets] {fixH₀ H}
                        ]
    fixH₁-identity {k} H {As} {hin x} = 
      let idH = Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] {H}
          idH-μH = NaturalTransformation.η idH (fixH₀ H)
          Hid≈id = Functor.identity H {fixH₀ H}
    
          μidH≈id : [Sets^ k ,Sets] Categories.Category.[
                        fixH₁ H H (Category.id [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]])
                        ≈ Category.id [Sets^ k ,Sets] ] 
          μidH≈id = fixH₁-identity H 
          --
          μidH  = fixH₁ H H idH
          Hid-resp = Functor.F-resp-≈ H {fixH₀ H} {fixH₀ H} {μidH} {Category.id [Sets^ k ,Sets]} μidH≈id
          -- HμidH = Functor.F₁ H μidH
          -- HμidH-As = NaturalTransformation.η HμidH As
        in ≡.cong hin 
            (begin      
              NaturalTransformation.η (Functor.F₁ H μidH) As x
              ≡⟨ Hid-resp ⟩      
              NaturalTransformation.η (Functor.F₁ H (Category.id [Sets^ k ,Sets])) As x
              ≡⟨ Hid≈id {As} {x} ⟩      
              x    ∎) 
    
    {-# TERMINATING #-}
    fixH₁-homomorphism : ∀ {k} (H1 H2 H3 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
                        → (f : NaturalTransformation H1 H2) → (g : NaturalTransformation H2 H3)
                        → [Sets^ k ,Sets]  Categories.Category.[ 
                          fixH₁ H1 H3 (g ∘v f)  
                          ≈ fixH₁ H2 H3 g ∘v fixH₁ H1 H2 f
                        ]
    fixH₁-homomorphism {k} H1 H2 H3 f g {Xs} {hin x} = 
        let μg : NaturalTransformation (fixH₀ H2) (fixH₀ H3)
            μg       = fixH₁ H2 H3 g
            -- 
            μf : NaturalTransformation (fixH₀ H1) (fixH₀ H2)
            μf       = fixH₁ H1 H2 f
            -- 
            μg∘f : NaturalTransformation (fixH₀ H1) (fixH₀ H3)
            μg∘f     = fixH₁ H1 H3 (g ∘v f)
            -- 
            g-μH3 : NaturalTransformation 
                  (Functor.F₀ H2 (fixH₀ H3)) 
                  (Functor.F₀ H3 (fixH₀ H3))
            g-μH3    = NaturalTransformation.η g (fixH₀ H3) 
            -- 
            g-μH3-Xs : Functor.F₀ (Functor.F₀ H2 (fixH₀ H3)) Xs 
                     → Functor.F₀ (Functor.F₀ H3 (fixH₀ H3)) Xs 
            g-μH3-Xs = NaturalTransformation.η g-μH3 Xs
            --        
            f-μH1 : NaturalTransformation 
                  (Functor.F₀ H1 (fixH₀ H1))  
                  (Functor.F₀ H2 (fixH₀ H1))
            f-μH1    = NaturalTransformation.η f (fixH₀ H1) 
            --
            f-μH1-Xs : Functor.F₀ (Functor.F₀ H1 (fixH₀ H1)) Xs 
                     → Functor.F₀ (Functor.F₀ H2 (fixH₀ H1)) Xs 
            f-μH1-Xs = NaturalTransformation.η f-μH1 Xs
            --
            f-μH2 : NaturalTransformation
                  (Functor.F₀ H1 (fixH₀ H2)) 
                  (Functor.F₀ H2 (fixH₀ H2))
            f-μH2    = NaturalTransformation.η f (fixH₀ H2) 
            -- 
            f-μH2-Xs : Functor.F₀ (Functor.F₀ H1 (fixH₀ H2)) Xs 
                     → Functor.F₀ (Functor.F₀ H2 (fixH₀ H2)) Xs 
            f-μH2-Xs = NaturalTransformation.η f-μH2 Xs
            --
            f-μH3 : NaturalTransformation
                  (Functor.F₀ H1 (fixH₀ H3)) 
                  (Functor.F₀ H2 (fixH₀ H3))
            f-μH3    = NaturalTransformation.η f (fixH₀ H3) 
            -- 
            f-μH3-Xs : Functor.F₀ (Functor.F₀ H1 (fixH₀ H3)) Xs 
                     → Functor.F₀ (Functor.F₀ H2 (fixH₀ H3)) Xs 
            f-μH3-Xs = NaturalTransformation.η f-μH3 Xs
            --
            H1-μg∘f : NaturalTransformation
               (Functor.F₀ H1 (fixH₀ H1)) 
               (Functor.F₀ H1 (fixH₀ H3))
            H1-μg∘f  = Functor.F₁ H1 μg∘f
            -- 
            H1-μg∘μf : NaturalTransformation
                  (Functor.F₀ H1 (fixH₀ H1)) 
                  (Functor.F₀ H1 (fixH₀ H3))
            H1-μg∘μf = Functor.F₁ H1 (μg ∘v μf)
            -- 
            μg∘f≈μg∘μf : [Sets^ k ,Sets] Categories.Category.[ 
              fixH₁ H1 H3 (g ∘v f) ≈ fixH₁ H2 H3 g ∘v fixH₁ H1 H2 f ]
            μg∘f≈μg∘μf     = fixH₁-homomorphism H1 H2 H3 f g 
            -- 
            H1μg∘f≈H1μg∘μf : [Sets^ k ,Sets] Categories.Category.[
               Functor.F₁ H1 (fixH₁ H1 H3 (g ∘v f)) 
               ≈ Functor.F₁ H1 (fixH₁ H2 H3 g ∘v fixH₁ H1 H2 f) ]
            H1μg∘f≈H1μg∘μf = Functor.F-resp-≈ H1 {f = μg∘f} {g = μg ∘v μf} μg∘f≈μg∘μf
            --
            H2-μg : NaturalTransformation
                (Functor.F₀ H2 (fixH₀ H2))  
                (Functor.F₀ H2 (fixH₀ H3))
            H2-μg = Functor.F₁ H2 μg
            -- 
            H1-μf : NaturalTransformation
                (Functor.F₀ H1 (fixH₀ H1))  
                (Functor.F₀ H1 (fixH₀ H2))
            H1-μf = Functor.F₁ H1 μf
            --
            H2-μg-Xs : Functor.F₀ (Functor.F₀ H2 (fixH₀ H2)) Xs 
                     → Functor.F₀ (Functor.F₀ H2 (fixH₀ H3)) Xs 
            H2-μg-Xs = NaturalTransformation.η H2-μg Xs
    
          in ≡.cong (hin ∘' g-μH3-Xs) (begin 
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
    fixH₁-F-resp : ∀ {k} (H1 H2 : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets]))
                        → (f g : NaturalTransformation H1 H2) 
                        → [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] Categories.Category.[ f ≈ g ]
                        → [Sets^ k ,Sets]  Categories.Category.[ 
                          fixH₁ H1 H2 f ≈ fixH₁ H1 H2 g 
                        ]
    fixH₁-F-resp H1 H2 f g f≈g {Xs} {hin x} = 
      let f-μH2    = NaturalTransformation.η f (fixH₀ H2) 
          f-μH2-Xs = NaturalTransformation.η f-μH2 Xs
          g-μH2    = NaturalTransformation.η g (fixH₀ H2) 
          g-μH2-Xs = NaturalTransformation.η g-μH2 Xs
          μf       = fixH₁ H1 H2 f
          H1-μf    = Functor.F₁ H1 μf
          H1-μf-Xs = NaturalTransformation.η H1-μf Xs
          μg       = fixH₁ H1 H2 g
          H1-μg    = Functor.F₁ H1 μg
          H1-μg-Xs = NaturalTransformation.η H1-μg Xs
    
        in ≡.cong hin (begin  
                        f-μH2-Xs (H1-μf-Xs x) 
                        ≡⟨ ≡.cong f-μH2-Xs (Functor.F-resp-≈ H1 (fixH₁-F-resp H1 H2 f g f≈g)) ⟩   
                        f-μH2-Xs (H1-μg-Xs x) 
                        ≡⟨ f≈g ⟩   
                        g-μH2-Xs (H1-μg-Xs x) ∎) 

open fixpoint-functor-laws public 


-- fixpoint of a higher order functor H
fixH : ∀ {k} → Functor [[ [Sets^ k ,Sets] , [Sets^ k ,Sets] ]] [Sets^ k ,Sets] 
fixH = record
  { F₀ = λ H → fixH₀ H
  ; F₁ = λ {H1} {H2} η → fixH₁ H1 H2 η
  ; identity = λ {H} → fixH₁-identity H
  ; homomorphism = λ {H1} {H2} {H3} {f} {g} → fixH₁-homomorphism H1 H2 H3 f g
  ; F-resp-≈ = λ {H1} {H2} {f} {g} f≈g → fixH₁-F-resp H1 H2 f g f≈g
  } 


-- initial algebra for fixpoint of H 
in-nat : ∀ {k} → (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) → NaturalTransformation (Functor.F₀ H (fixH₀ H)) (fixH₀ H)
in-nat H = record { η = λ { Xs x → hin x  }
                  ; commute = λ f → ≡.refl
                  ; sym-commute = λ f → ≡.refl } 

-- other direction of initial algebra 
in-inv-nat : ∀ {k} → (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) → NaturalTransformation (fixH₀ H) (Functor.F₀ H (fixH₀ H)) 
in-inv-nat H = 
  record { η = λ { X (hin x) → x } 
         ; commute = λ { {Xs} {Ys} fs {hin x} → ≡.refl  }
         ; sym-commute = λ { {Xs} {Ys} fs {hin x}  → ≡.refl }  }


fix-iso : ∀ {k} (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
            (Xs : Vec Set k) 
            → Categories.Morphism.Iso Sets (NaturalTransformation.η (in-inv-nat H) Xs) (NaturalTransformation.η (in-nat H) Xs)
fix-iso H Xs = record { isoˡ = λ { {hin x} → ≡.refl } 
                      ; isoʳ = ≡.refl } 


-- in-nat, in-inv-nat form natural isomorphism 
in-nat-iso : ∀ {k} → (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]) → NaturalIsomorphism (fixH₀ H) (Functor.F₀ H (fixH₀ H))
in-nat-iso H = record { F⇒G = in-inv-nat H ; F⇐G = in-nat H ; iso = fix-iso H }


module fold where 
  
  mutual 
    {-# TERMINATING #-}
    foldH-η : ∀ {k} (H : Functor [Sets^ k ,Sets] [Sets^ k ,Sets])
                (F : Functor (Sets^ k) Sets)
                (η : NaturalTransformation (Functor.F₀ H F) F)
                (Xs : Vec Set k)
                → Functor.F₀ (fixH₀ H) Xs 
                → Functor.F₀ F Xs 
    foldH-η H F η Xs (hin x) = 
      let Hη : NaturalTransformation (Functor.F₀ H (Functor.F₀ H F))
                                    (Functor.F₀ H F)
          Hη = Functor.F₁ H η 
  
          Hfold : NaturalTransformation (Functor.F₀ H (fixH₀ H))
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
                      → (f : VecMorph Xs Ys)
                      → Sets Categories.Category.[
                          foldH-η H F η Ys ∘' (Functor.F₁ (fixH₀ H) f)
                          ≈ Functor.F₁ F f ∘' (foldH-η H F η Xs)
                      ]
    foldH-commute H F η {Xs} {Ys} f {hin x} = 
      let η-Ys = NaturalTransformation.η η Ys
          η-Xs = NaturalTransformation.η η Xs
          H-foldη = Functor.F₁ H (foldH H F η)
          H-foldη-Xs = NaturalTransformation.η H-foldη Xs
          H-foldη-Ys = NaturalTransformation.η H-foldη Ys
          HμH = Functor.F₀ H (fixH₀ H)
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
            → NaturalTransformation (fixH₀ H) F
    foldH H F η = 
      record { η = foldH-η H F η  
             ; commute = foldH-commute H F η
             ; sym-commute = λ {Xs} {Ys} f {x} → ≡.sym (foldH-commute H F η f {x}) } 
  
open fold public 


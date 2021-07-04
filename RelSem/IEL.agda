

-- open import RelSem.RelTypeSemantics using (RelSem ; RelSemVec ; MuRelSem ; module NormalTRel)
open import TypeSemantics.TypeSemantics -- using (SetSem ; SetSemVec ; RelSem ; RelSemVec ; MuRelSem )
open import RelSem.RelCats
open RelObj
open import RelEnvironments.Core
open import SetEnvironments.Core
open import Syntax.NestedTypeSyntax
open _≀_⊢_ -- import names of data constructors
open import HetEquality.Utils
open import HFixFunctorLib
open import RelSem.HFixRel
-- open FixRel
open import SetCats


open import Categories.Functor using (Functor ; _∘F_) renaming (id to idF)

open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_)
open _⊎_ 
open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt )
open import Data.Empty using (⊥)
import Relation.Binary.HeterogeneousEquality as Het
open import Agda.Builtin.Nat renaming (Nat to ℕ)
import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module RelSem.IEL where





-- to prove that R ≡ S for (R S : RelObj), we must be able to prove that
-- 1) fst R ≡ fst S
-- 2) snd R ≡ snd S
-- 3) rel R ≡ rel S
--
-- but for the paper, we are really only interested in proving 1) and 2)
-- and
-- 3') ∀ x y → x y ∈ rel R → x y ∈  rel S
-- 3'') ∀ x y → x y ∈ rel S → x y ∈  rel R
--
-- except x y ∈ rel S may not type-check since fst/snd of R and S don't match on the nose...
IEL-environments : ∀ {k : ℕ} {Γ} {Φ} {F} (ρ : SetEnv)
                   → (⊢F : Γ ≀ Φ ⊢ F)
                   → Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ)
                   ≡ Functor.F₀ Eq (Functor.F₀ (SetSem ⊢F) ρ)
IEL-environments ρ 𝟘-I = {!!}
IEL-environments ρ 𝟙-I = {!!}
IEL-environments ρ (AppT-I Γ∋φ Fs ⊢Fs) = {!!}
IEL-environments ρ (AppF-I Φ∋φ Fs ⊢Fs) = {!!}
IEL-environments ρ (+-I ⊢F ⊢F₁) = {!!}
IEL-environments ρ (×-I ⊢F ⊢F₁) = {!!}
IEL-environments ρ (Nat-I ⊢F ⊢F₁) = {!!}
IEL-environments ρ (μ-I ⊢F Gs ⊢Gs) = {!!}

open ≡.≡-Reasoning 
IEL-over1 : ∀ {k : ℕ} {Γ} {Φ} {F} (ρ : SetEnv)
                   → (⊢F : Γ ≀ Φ ⊢ F)
                   → RelObj.fst (Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ))
                   ≡ RelObj.fst (Functor.F₀ Eq (Functor.F₀ (SetSem ⊢F) ρ))
IEL-over1 ρ ⊢F =
  begin  RelObj.fst (Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ))
      ≡˘⟨ SetSem-over-1 ⊢F (Functor.F₀ EqEnv ρ) ⟩
       Functor.F₀ (SetSem ⊢F) (Functor.F₀ π₁Env (Functor.F₀ EqEnv ρ))
      ≡⟨ ≡.refl ⟩
       RelObj.fst (Functor.F₀ Eq (Functor.F₀ (SetSem ⊢F) ρ))
      ∎  

IEL-over2 : ∀ {k : ℕ} {Γ} {Φ} {F} (ρ : SetEnv)
                   → (⊢F : Γ ≀ Φ ⊢ F)
                   → RelObj.snd (Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ))
                   ≡ RelObj.snd (Functor.F₀ Eq (Functor.F₀ (SetSem ⊢F) ρ))
IEL-over2 ρ ⊢F =
  begin  RelObj.snd (Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ))
      ≡˘⟨ SetSem-over-2 ⊢F (Functor.F₀ EqEnv ρ) ⟩
       Functor.F₀ (SetSem ⊢F) (Functor.F₀ π₂Env (Functor.F₀ EqEnv ρ))
      ≡⟨ ≡.refl ⟩
       RelObj.snd (Functor.F₀ Eq (Functor.F₀ (SetSem ⊢F) ρ))
      ∎  



hffin-het-cong : ∀ {k : ℕ} {H : Functor ([Sets^ k ,Sets]) ([Sets^ k ,Sets])} {As Bs : Vec Set k}
                 {x : Functor.F₀ (Functor.F₀ H (fixH₀ H)) As}
                 {y : Functor.F₀ (Functor.F₀ H (fixH₀ H)) Bs}
                 → As Het.≅ Bs
                 → x Het.≅ y → hin {k} {H} x Het.≅ hin {k} {H} y
hffin-het-cong Het.refl Het.refl = Het.refl

-- different H, H'
hffin-het-cong' : ∀ {k : ℕ} {H H' : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]} {As Bs : Vec Set k}
                 {x : Functor.F₀ (Functor.F₀ H (fixH₀ H)) As}
                 {y : Functor.F₀ (Functor.F₀ H' (fixH₀ H')) Bs}
                 → As Het.≅ Bs
                 → H Het.≅ H'
                 → x Het.≅ y → hin {k} {H} x Het.≅ hin {k} {H'} y
hffin-het-cong' Het.refl Het.refl Het.refl = Het.refl


IEL-rel : ∀ {Γ} {Φ} {F} (ρ : SetEnv)
          → (⊢F : Γ ≀ Φ ⊢ F)
          → ∀ {x y}
          → x , y ∈ rel (Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ))
          → x Het.≅  y
IEL-rel ρ 𝟙-I tt = Het.refl
IEL-rel ρ (AppT-I {φ = φ} Γ∋φ Fs ⊢Fs) {x} {y} (fst₁ , ≡.refl) = {!!}
IEL-rel ρ (AppF-I Φ∋φ Fs ⊢Fs) (fst₁ , ≡.refl) = {!!}
IEL-rel ρ (+-I ⊢F ⊢G) {inj₁ x} {inj₁ x'} p = inj₁-het-cong' {x = x} {x' = x'} {!!}  {!!} (IEL-rel ρ ⊢F {x} {x'} p) 
IEL-rel ρ (+-I ⊢F ⊢G) {inj₂ y} {inj₂ y'} p = inj₂-het-cong' {x = y} {x' = y'} {!!} {!!} (IEL-rel ρ ⊢G p)
IEL-rel ρ (×-I ⊢F ⊢G) {x , x'} {y , y'} (xRy , x'Ry') =
  let x≅y : x Het.≅ y
      x≅y = IEL-rel ρ ⊢F  {x} {y} xRy
      x'≅y' : x' Het.≅ y'
      x'≅y' = IEL-rel ρ ⊢G  {x'} {y'} x'Ry'
   in pair-het x≅y x'≅y'
IEL-rel ρ (Nat-I ⊢F ⊢G) record { preserves = preserves } = {!!}
IEL-rel ρ (μ-I {k = k} ⊢F Gs ⊢Gs) {hin x} {hin y} (rhin p) = {!p!} 
{-
    let Tρ : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
        Tρ = Functor.F₀ (TSet ⊢F) (Functor.F₀ ForgetFVSetEnv ρ)
        Eq-ρ : RelEnv
        Eq-ρ = Functor.F₀ EqEnv ρ

        Tρ1 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
        Tρ1 = HRTObj.H1 (Functor.₀ (TEnvRT ⊢F) (Functor.₀ ForgetFVRelEnv (Functor.F₀ EqEnv ρ)))

        Tρ2 : Functor [Sets^ k ,Sets] [Sets^ k ,Sets]
        Tρ2 = HRTObj.H2 (Functor.₀ (TEnvRT ⊢F) (Functor.₀ ForgetFVRelEnv (Functor.F₀ EqEnv ρ)))

        Tρ1≅Tρ2 : Tρ1 Het.≅ Tρ2
        Tρ1≅Tρ2 = {! Het.refl !}

        Gs1 : Vec Set k
        Gs1 = vecfst (Functor.F₀ (RelSemVec ⊢Gs) Eq-ρ)
        Gs2 : Vec Set k
        Gs2 = vecsnd (Functor.F₀ (RelSemVec ⊢Gs) Eq-ρ)

        Gs1≅Gs2 : Gs1 Het.≅ Gs2
        Gs1≅Gs2 = {!p!}

        x≅y : x Het.≅ y
        x≅y = {!!}

        T-Eq-ρ : HRTObj k
        T-Eq-ρ = Functor.₀ (TEnvRT ⊢F) Eq-ρ

        Gsρ = Functor.F₀ (RelSemVec ⊢Gs) Eq-ρ
        μT = (fixHRT₀ (HRTObj.H1 T-Eq-ρ) (HRTObj.H2 T-Eq-ρ) (HRTObj.H*Data T-Eq-ρ))
        Tρ' = Functor.F₀ (Functor.F₀ (Functor.₀ (TRel ⊢F) Eq-ρ) μT) Gsρ

        test = {!Tρ'!}

        h' :   hin {k} {Tρ1} {vecfst (Functor.F₀ (RelSemVec ⊢Gs) Eq-ρ)} x
         Het.≅ hin {k} {Tρ2} {vecsnd (Functor.F₀ (RelSemVec ⊢Gs) Eq-ρ)} y
        h' = hffin-het-cong' {k} {Tρ1} {Tρ2} {Gs1} {Gs2} {x} {y} Gs1≅Gs2 Tρ1≅Tρ2 x≅y
        -- hffin-het-cong {x = x} {y = y} {!!} {!!}
     in h'

-}

-- type of x in hin x above:
{-
Have: Functor.F₀ (SetSem ⊢F)
      ((SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
        RTEnvironments.Core.[ φ :fv=
        (fixH₀
         (curry₀
          (SetSem ⊢F ∘F
           extendEnv-ρ×As αs ∘F
           (extendEnv2 φ
            ⁂ idF))
          ∘F
          (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
           ※ idF)))
        ])
       RTEnvironments.Core.[ αs :fvs=
       Data.Vec.map ConstF
       (vecfst
        (Functor.F₀ (RelSemVec ⊢Gs)
         SetEnv[
         (λ x₁ →
            RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
            Identities.idRT*Components (SetEnv.tc ρ x₁) ])
         ,
         (λ x₁ →
            RT[ SetEnv.fv ρ x₁ , SetEnv.fv ρ x₁ ,
            Identities.idRT*Components (SetEnv.fv ρ x₁) ])
         ]))
       ])
-}




-- non-normalized type of p in rhin p
{-

RTObj.F*Rel
 (HRTObj.HEndo-obj T-Eq-ρ
   (fixHRT₀ (HRTObj.H1 T-Eq-ρ) (HRTObj.H2 T-Eq-ρ) (HRTObj.H*Obj T-Eq-ρ))
 )
(Functor.F₀ (RelSemVec ⊢Gs) (Functor.F₀ EqEnv ρ)) x y

let T-Eq-ρ : HRTObj k
    T-Eq-ρ = (Functor.₀ (NormalTRel.TEnvRT ⊢F)
  (Functor.₀ ForgetFVRelEnv (Functor.F₀ EqEnv ρ)))


--
H : HRTObj k
Rt : RTObj k

HRTObj.HEndo-obj H Rt : RTObj
= RT [ H1 Rt1 , H2 Rt2 , HEndo-rel* Rt ]
where
HEndo-rel* Rt =
  record { F*Rel = HRTObj*.H*RTRel H*Obj Rt ; F*Rel-preserves = .... }
--


-- what is F*Rel .... ?
let μT = (fixHRT₀ (HRTObj.H1 T-Eq-ρ) (HRTObj.H2 T-Eq-ρ) (HRTObj.H*Obj T-Eq-ρ))
    Gsρ = (Functor.F₀ (RelSemVec ⊢Gs) (Functor.F₀ EqEnv ρ))
so (HEndo-obj T-Eq-ρ μT)
 = RT[ H1 T-Eq-ρ (H1 T-Eq-ρ) , H2 T-Eq-ρ (H2 T-Eq-ρ)
       , HEndo-rel* T-Eq-ρ μT ]
and
HEndo-rel* T-Eq-ρ μT =
  record { F*Rel = HRTObj*.H*RTRel (H*Obj T-Eq-ρ) μT
         ; ... }

-- F*Rel ... is
F*Rel (HEndo-obj T-Eq-ρ μT) Gsρ
= HRTObj*.H*RTRel (HRTObj.H*Obj T-Eq-ρ) μT Gsρ

H*Obj T-Eq-ρ = 3rd component of T-Eq-ρ : HRTObj* .. ..
H*RTRel (H*Obj T-Eq-ρ) μT Gsρ = ??? : REL (.. (vecfst Gsρ)) (.. (vecsnd Gsρ))
= (from make-HRTObj)

    T-Eq-ρ normalizes to
        make-HRT.make-HRTObj
        (Functor.₀ (TSet ⊢F ∘F π₁Env) Eq-ρ)
        (Functor.₀ (TSet ⊢F ∘F π₂Env) Eq-ρ)
        (Functor.₀ (TEnv ⊢F) Eq-ρ) h1 h2
    =
    HRT[ (Functor.₀ (TSet ⊢F ∘F π₁Env) Eq-ρ)
       , (Functor.₀ (TSet ⊢F ∘F π₂Env) Eq-ρ)
       , record {
         H*RTRel =
           λ Rt Rs x y → rel (H*Rel Rt Rs) (h1 Rt Rs x) (h2 Rt Rs y)
         ; ...
       }  ]

where H*Rel Rt Rs
  = (Functor.F₀ (Functor.F₀  (Functor.₀ (TEnv ⊢F) Eq-ρ) Rt) Rs)


so
F*Rel (HEndo-obj T-Eq-ρ μT) Gsρ
=
HRTObj*.H*RTRel (HRTObj.H*Obj T-Eq-ρ) μT Gsρ
=
λ x y → rel (H*Rel Rt Rs) (h1 Rt Rs x) (h2 Rt Rs y)
=
λ x y → rel (Functor.F₀ (Functor.F₀  (Functor.₀ (TEnv ⊢F) Eq-ρ) μT) Gsρ)
            (f1 μT Gsρ x) (f2 μT Gsρ y)

where f1 μT Gsρ = NaturalTransformation.η (h1 μT) Gsρ
      f2 μT Gsρ = NaturalTransformation.η (h2 μT) Gsρ


so p is a proof of
NaturalTransformation.η (h1 μT) Gsρ x
, NaturalTransformation.η (h2 μT) Gsρ y
∈ rel (Functor.F₀ (Functor.F₀ (Functor.₀ (TEnv ⊢F) Eq-ρ) μT) Gsρ)

maybe we can prove
NaturalTransformation.η (h1 μT) Gsρ x ≅ x
and similar for y
and use that to get a proof of
x , y ∈ ???

to get x ≅ y that we need

in particular, IH requires
    x , y ∈ rel (Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ))
for some ρ...
so we need to show that
(Functor.F₀ (Functor.F₀ (Functor.₀ (TEnv ⊢F) Eq-ρ) μT) Gsρ)
is equivalent to
(Functor.F₀ (RelSem ⊢F) (Functor.F₀ EqEnv ρ'))
for some ρ'...
-}


-- normalized type of p in rhin p
{-
rel
(Functor.F₀ (RelSem ⊢F)
 ((SetEnv[
   (λ x₁ →
      RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
      Identities.idRT*Components (SetEnv.tc ρ x₁) ])
   ,
   (λ _ →
      RT[ ConstF ⊤ , ConstF ⊤ ,
      record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
      ])
   ]
   [ φ :fv=
   RT[
   HFixFunctorLib.mkFunc
   (HFixFunctor
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-fmap
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-id
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-homo
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-resp
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   ,
   HFixFunctorLib.mkFunc
   (HFixFunctor
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-fmap
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-id
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-homo
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   (HFix-resp
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF)))
   ,
   μRT*
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF))
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF))
   (make-HRT.make-HRTObj*
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF))
    (Categories.Category.Construction.Functors.curry₀
     (SetSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
      Categories.Category.Product.※ idF))
    (Categories.Category.Construction.Functors.curry₀
     (RelSem ⊢F ∘F
      RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
      (RTEnvironments.EnvironmentExtension.extendEnv2 φ
       Categories.Category.Product.⁂ idF))
     ∘F
     (ConstF
      SetEnv[
      (λ x₁ →
         RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
         Identities.idRT*Components (SetEnv.tc ρ x₁) ])
      ,
      (λ _ →
         RT[ ConstF ⊤ , ConstF ⊤ ,
         record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
         ])
      ]
      Categories.Category.Product.※ idF))
    (record
     { η =
         RelSem.RelTypeSemantics.unsolved#meta.370 ⊢F
         SetEnv[
         (λ x₁ →
            RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
            Identities.idRT*Components (SetEnv.tc ρ x₁) ])
         ,
         (λ _ →
            RT[ ConstF ⊤ , ConstF ⊤ ,
            record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
            ])
         ]
     ; commute =
         RelSem.RelTypeSemantics.unsolved#meta.371 ⊢F
         SetEnv[
         (λ x₁ →
            RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
            Identities.idRT*Components (SetEnv.tc ρ x₁) ])
         ,
         (λ _ →
            RT[ ConstF ⊤ , ConstF ⊤ ,
            record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
            ])
         ]
     ; sym-commute =
         RelSem.RelTypeSemantics.unsolved#meta.372 ⊢F
         SetEnv[
         (λ x₁ →
            RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
            Identities.idRT*Components (SetEnv.tc ρ x₁) ])
         ,
         (λ _ →
            RT[ ConstF ⊤ , ConstF ⊤ ,
            record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
            ])
         ]
     })
    (RelSem.RelTypeSemantics.unsolved#meta.481 ⊢F
     SetEnv[
     (λ x₁ →
        RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
        Identities.idRT*Components (SetEnv.tc ρ x₁) ])
     ,
     (λ _ →
        RT[ ConstF ⊤ , ConstF ⊤ ,
        record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
        ])
     ]))
   ]
   ]Rel)
  [ αs :fvs=
  Data.Vec.map ConstRT
  (Functor.F₀ (RelSemVec ⊢Gs)
   SetEnv[
   (λ x₁ →
      RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
      Identities.idRT*Components (SetEnv.tc ρ x₁) ])
   ,
   (λ x₁ →
      RT[ SetEnv.fv ρ x₁ , SetEnv.fv ρ x₁ ,
      Identities.idRT*Components (SetEnv.fv ρ x₁) ])
   ])
  ]Rel))
(Categories.NaturalTransformation.Core.NaturalTransformation.η
 (RelSem.RelTypeSemantics.unsolved#meta.370 ⊢F
  SetEnv[
  (λ x₁ →
     RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
     Identities.idRT*Components (SetEnv.tc ρ x₁) ])
  ,
  (λ _ →
     RT[ ConstF ⊤ , ConstF ⊤ ,
     record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
     ])
  ]
  RT[
  HFixFunctorLib.mkFunc
  (HFixFunctor
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-fmap
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-id
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-homo
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-resp
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  ,
  HFixFunctorLib.mkFunc
  (HFixFunctor
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-fmap
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-id
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-homo
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  (HFix-resp
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF)))
  ,
  μRT*
  (Categories.Category.Construction.Functors.curry₀
   (SetSem ⊢F ∘F
    RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
    (RTEnvironments.EnvironmentExtension.extendEnv2 φ
     Categories.Category.Product.⁂ idF))
   ∘F
   (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
    Categories.Category.Product.※ idF))
  (Categories.Category.Construction.Functors.curry₀
   (SetSem ⊢F ∘F
    RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
    (RTEnvironments.EnvironmentExtension.extendEnv2 φ
     Categories.Category.Product.⁂ idF))
   ∘F
   (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
    Categories.Category.Product.※ idF))
  (make-HRT.make-HRTObj*
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF))
   (Categories.Category.Construction.Functors.curry₀
    (SetSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF SetEnv[ (λ x₁ → SetEnv.tc ρ x₁) , (λ x₁ → ConstF ⊤) ]
     Categories.Category.Product.※ idF))
   (Categories.Category.Construction.Functors.curry₀
    (RelSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF
     SetEnv[
     (λ x₁ →
        RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
        Identities.idRT*Components (SetEnv.tc ρ x₁) ])
     ,
     (λ _ →
        RT[ ConstF ⊤ , ConstF ⊤ ,
        record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
        ])
     ]
     Categories.Category.Product.※ idF))
   (record
    { η =
        RelSem.RelTypeSemantics.unsolved#meta.370 ⊢F
        SetEnv[
        (λ x₁ →
           RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
           Identities.idRT*Components (SetEnv.tc ρ x₁) ])
        ,
        (λ _ →
           RT[ ConstF ⊤ , ConstF ⊤ ,
           record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
           ])
        ]
    ; commute =
        RelSem.RelTypeSemantics.unsolved#meta.371 ⊢F
        SetEnv[
        (λ x₁ →
           RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
           Identities.idRT*Components (SetEnv.tc ρ x₁) ])
        ,
        (λ _ →
           RT[ ConstF ⊤ , ConstF ⊤ ,
           record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
           ])
        ]
    ; sym-commute =
        RelSem.RelTypeSemantics.unsolved#meta.372 ⊢F
        SetEnv[
        (λ x₁ →
           RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
           Identities.idRT*Components (SetEnv.tc ρ x₁) ])
        ,
        (λ _ →
           RT[ ConstF ⊤ , ConstF ⊤ ,
           record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
           ])
        ]
    })
   (RelSem.RelTypeSemantics.unsolved#meta.481 ⊢F
    SetEnv[
    (λ x₁ →
       RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
       Identities.idRT*Components (SetEnv.tc ρ x₁) ])
    ,
    (λ _ →
       RT[ ConstF ⊤ , ConstF ⊤ ,
       record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
       ])
    ]))
  ])
 (Functor.F₀ (RelSemVec ⊢Gs)
  SetEnv[
  (λ x₁ →
     RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
     Identities.idRT*Components (SetEnv.tc ρ x₁) ])
  ,
  (λ x₁ →
     RT[ SetEnv.fv ρ x₁ , SetEnv.fv ρ x₁ ,
     Identities.idRT*Components (SetEnv.fv ρ x₁) ])
  ])
 x)
(NaturalTransformation.η
 (NaturalTransformation.η
  (RelSem.RelTypeSemantics.unsolved#meta.481 ⊢F
   SetEnv[
   (λ x₁ →
      RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
      Identities.idRT*Components (SetEnv.tc ρ x₁) ])
   ,
   (λ _ →
      RT[ ConstF ⊤ , ConstF ⊤ ,
      record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
      ])
   ])
  RT[
  Functor.F₀ (NormalT.TEnv ⊢F) (Functor.F₀ ForgetFVSetEnv ρ)
  ,
  Functor.F₀ (NormalT.TEnv ⊢F) (Functor.F₀ ForgetFVSetEnv ρ)
  ,
  μRT*
  Functor.F₀ (NormalT.TEnv ⊢F) (Functor.F₀ ForgetFVSetEnv ρ)
  Functor.F₀ (NormalT.TEnv ⊢F) (Functor.F₀ ForgetFVSetEnv ρ)
  (make-HRT.make-HRTObj*
  Functor.F₀ (NormalT.TEnv ⊢F) (Functor.F₀ ForgetFVSetEnv ρ)
  Functor.F₀ (NormalT.TEnv ⊢F) (Functor.F₀ ForgetFVSetEnv ρ)
   (Categories.Category.Construction.Functors.curry₀
    (RelSem ⊢F ∘F
     RTEnvironments.EnvironmentExtension.extendEnv-ρ×As αs ∘F
     (RTEnvironments.EnvironmentExtension.extendEnv2 φ
      Categories.Category.Product.⁂ idF))
    ∘F
    (ConstF
     SetEnv[
     (λ x₁ →
        RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
        Identities.idRT*Components (SetEnv.tc ρ x₁) ])
     ,
     (λ _ →
        RT[ ConstF ⊤ , ConstF ⊤ ,
        record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
        ])
     ]
     Categories.Category.Product.※ idF))
   (record
    { η =
        RelSem.RelTypeSemantics.unsolved#meta.370 ⊢F
        SetEnv[
        (λ x₁ →
           RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
           Identities.idRT*Components (SetEnv.tc ρ x₁) ])
        ,
        (λ _ →
           RT[ ConstF ⊤ , ConstF ⊤ ,
           record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
           ])
        ]
    ; commute =
        RelSem.RelTypeSemantics.unsolved#meta.371 ⊢F
        SetEnv[
        (λ x₁ →
           RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
           Identities.idRT*Components (SetEnv.tc ρ x₁) ])
        ,
        (λ _ →
           RT[ ConstF ⊤ , ConstF ⊤ ,
           record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
           ])
        ]
    ; sym-commute =
        RelSem.RelTypeSemantics.unsolved#meta.372 ⊢F
        SetEnv[
        (λ x₁ →
           RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
           Identities.idRT*Components (SetEnv.tc ρ x₁) ])
        ,
        (λ _ →
           RT[ ConstF ⊤ , ConstF ⊤ ,
           record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
           ])
        ]
    })
   (RelSem.RelTypeSemantics.unsolved#meta.481 ⊢F
    SetEnv[
    (λ x₁ →
       RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
       Identities.idRT*Components (SetEnv.tc ρ x₁) ])
    ,
    (λ _ →
       RT[ ConstF ⊤ , ConstF ⊤ ,
       record { F*Rel = λ Rs x₁ y₁ → ⊤ ; F*Rel-preserves = λ ms _ → tt }
       ])
    ]))
  ])
 (Functor.F₀ (RelSemVec ⊢Gs)
  SetEnv[
  (λ x₁ →
     RT[ SetEnv.tc ρ x₁ , SetEnv.tc ρ x₁ ,
     Identities.idRT*Components (SetEnv.tc ρ x₁) ])
  ,
  (λ x₁ →
     RT[ SetEnv.fv ρ x₁ , SetEnv.fv ρ x₁ ,
     Identities.idRT*Components (SetEnv.fv ρ x₁) ])
  ])
 y)
 -}

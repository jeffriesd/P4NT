
open import Categories.Functor using (Functor ; _∘F_)
open import Categories.Category.Construction.Functors using (Functors ; eval ; module curry)
open import Categories.NaturalTransformation renaming (_∘ᵥ_ to _∘v_ ; _∘ₕ_  to _∘h_ ; id to idnat)
open import Categories.Category 
open import Categories.Category.Product 

open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (_because_ ; Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (isYes)
open import Agda.Builtin.Bool
open import Data.Unit renaming (⊤ to ⊤') 
open import Data.Empty renaming (⊥ to ⊥') 
open import Data.Vec using (Vec ; [] ; _∷_ ; _++_)
open import Data.Sum renaming ([_,_] to [_,⊎_])
open import Data.Product renaming (_×_ to _×'_  ; map to ×'-map) 
open import Function using (const ; flip) renaming (id to idf; _∘_ to _∘'_)

open import TypeSemantics.SetSemantics using (SetSem ; extendSetSem-αs)
open import SetEnvironments.Core
open import SetEnvironments.Properties
open import Syntax.NestedTypeSyntax 
open import SetCats 
open import Utils using (exFalso ; ×'-cong)
open import Syntax.TermSyntax

module TermSemantics.TermSetSemUtils where 



private 
  variable 
    o l e : Level 
    C : Category o l e 





-- define currying of nat types 

open import TypeSemantics.SetSemantics
open import SetEnvironments.EnvironmentExtension
open import Agda.Builtin.Nat renaming (Nat to ℕ ; _+_ to _+'_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_) 
import Categories.NaturalTransformation.NaturalIsomorphism as NI 



makeNat-gen' : ∀ {o l e} {S E : Category o l e}
               → (ext : Category.Obj E → Functor S E)
               → (D F G : Functor E Sets)
               → (∀ ρ → NaturalTransformation (ConstF {C = S} (Functor.F₀ D ρ)) (D ∘F (ext ρ)))
               → NaturalTransformation (D ×Set F) G
               → (ρ : Category.Obj E)
               → (Dρ : Functor.F₀ D ρ)
               → NaturalTransformation (F ∘F ext ρ) (G ∘F ext ρ)
makeNat-gen' ext D F G iso η ρ Dρ =
  let ηext : NaturalTransformation ((D ×Set F) ∘F ext ρ) (G ∘F ext ρ)
      ηext = η ∘ʳ (ext ρ)

      distr-extend : NaturalTransformation ((D ∘F ext ρ) ×Set (F ∘F ext ρ))
                                           ((D ×Set F) ∘F ext ρ)
      distr-extend = ×Set-compose-distr-sym D F (ext ρ)

      c : NaturalTransformation (F ∘F ext ρ) (D ∘F ext ρ)
      c = (iso ρ) ∘v toConstF (F ∘F ext ρ) (Functor.F₀ D ρ) Dρ   

    in ηext ∘v distr-extend ∘v prod-Nat c idnat    


makeNat-gen : ∀ {o l e} {C : Category o l e}
              → (F G : Functor C Sets)
              → (D : Set)
              → (d : D)
              → NaturalTransformation (ConstF D ×Set F) G
              → NaturalTransformation F G 
makeNat-gen F G D d η = η ∘v prod-Nat (toConstF F D d) idnat  
-- record { η = λ c Fc → NaturalTransformation.η η c (d , Fc)
--                                ; commute = λ f → NaturalTransformation.commute η f
--                                ; sym-commute = λ f → NaturalTransformation.sym-commute η f } 



-- this type checks in 30 seconds or so without abstract, so the abstract is just for speedup 
-- abstract 
postulate
    makeNat : ∀ {Γ} {k} (αs : Vec (FVar 0) k) {F} {G} (Δ : TermCtx Γ ∅)
            → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G)
            -- → (D F G : Functor SetEnvCat Sets)
            → (Diso : ∀ ρ → ConstF {C = Sets^ k} (Functor.F₀ (ContextInterp Δ) (ρ)) ≃  (ContextInterp Δ) ∘F (extendSetEnv-αs αs (NatEnv ρ)) )
            → (η : NaturalTransformation ((ContextInterp Δ) ×Set (SetSem ⊢F)) (SetSem ⊢G)) (ρ : SetEnv)
            → (Dρ : Functor.F₀ (ContextInterp Δ) ρ)
            → Functor.F₀ (NatTypeFunctor αs ⊢F ⊢G) ρ

{- This dfn typechecks, it's just slow 
    -- give a warning to indicate this definition is currently marked as abstract 
    -- {-# WARNING_ON_USAGE makeNat "makeNat is abstract" #-}
    makeNat {k} αs Δ F G Diso η ρ Dρ = 
        let F : Functor SetEnvCat Sets
            F = SetSem ⊢F
            G : Functor SetEnvCat Sets
            G = SetSem ⊢G
            D : Functor SetEnvCat Sets
            D = ContextInterp Δ

            extend : Functor (Sets^ k) SetEnvCat
            extend = extendSetEnv-αs αs (NatEnv ρ)

            extendF : Functor (Sets^ k) Sets
            -- extendF = extendSetSem-αs αs (NatEnv ρ) F
            extendF = F ∘F extend

            extendG : Functor (Sets^ k) Sets
            -- extendG = extendSetSem-αs αs (NatEnv ρ) G
            extendG = G ∘F extend

            extendD : Functor (Sets^ k) Sets
            -- extendD = extendSetSem-αs αs (NatEnv ρ) D
            extendD = D ∘F extend

            extendD×F : Functor (Sets^ k) Sets
            extendD×F = (D ×Set F) ∘F extend

            extendD×extendF : Functor (Sets^ k) Sets
            extendD×extendF = extendD ×Set extendF

            distr-extend : NaturalTransformation extendD×extendF extendD×F 
            distr-extend = ×Set-compose-distr-sym  D F extend    

            -- whisker η with environment extension functor
            whisker-η : NaturalTransformation extendD×F extendG
            whisker-η = Functor.F₁ (extendSetSem-αs-higher αs (NatEnv ρ)) η

            ConstD : Functor (Sets^ k) Sets
            ConstD = ConstF {C = Sets^ k} (Functor.F₀ D (ρ))

            K⊤ : Functor (Sets^ k) Sets
            K⊤ = ConstF {C = Sets^ k} ⊤'

            toK⊤ : NaturalTransformation extendF K⊤
            toK⊤ = ntHelper (record { η = λ Xs _ → tt ; commute = λ _ → ≡.refl }) 

            toConstD : NaturalTransformation K⊤ ConstD
            toConstD = ConstNat (const Dρ)

            ConstD⇒extendD : NaturalTransformation ConstD extendD
            ConstD⇒extendD = NI.NaturalIsomorphism.F⇒G (Diso ρ) 

            extendF⇒extendD : NaturalTransformation extendF extendD
            extendF⇒extendD =  ConstD⇒extendD ∘v toConstD ∘v toK⊤  

            F⇒D×F : NaturalTransformation extendF
                                            extendD×F 
            F⇒D×F = distr-extend ∘v prod-Nat extendF⇒extendD idnat 

            η : NaturalTransformation extendF extendG
            η = whisker-η ∘v F⇒D×F   

            in 
            NatT3[  η  ] 

-}




open ≡.≡-Reasoning
open import Relation.Binary.HeterogeneousEquality using (_≅_)
import Relation.Binary.HeterogeneousEquality as Het


-- this proof of naturality is easy because we only pass (NatEnv ρ) to makeNat,
-- and (NatEnv ρ) ≡ (NatEnv ρ') whenever there exists a morphism f : ρ → ρ'
-- also since ForgetFVSetEnv f always gives an identity morphism, proving
-- that D (ForgetFVSetEnv f) x = x is just a matter of functoriality 

{-
makeNat : ∀
{Γ Φ} {Δ : TermCtx Γ ∅} {k} {αs : Vec (FVar 0) k} {F} {G}
        → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G)
        -- → (D F G : Functor SetEnvCat Sets)
        → (Diso : ∀ ρ → ConstF {C = Sets^ k} (Functor.F₀ (ContextInterp Δ) (ρ)) ≃  (ContextInterp Δ) ∘F (extendSetEnv-αs αs (NatEnv ρ)) )
        → (η : NaturalTransformation ((ContextInterp Δ) ×Set (SetSem ⊢F)) G) (ρ : SetEnv) (Dρ : Functor.F₀ (ContextInterp Δ) ρ)
        → Functor.F₀ (NatTypeFunctor αs ⊢F ⊢G) ρ
        -}

curryNatType-commute : ∀ {Γ} {k} (αs : Vec (FVar 0) k) {F} {G} (Δ : TermCtx Γ ∅)
                       → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G)
                       → (Diso : ∀ ρ → ConstF {C = Sets^ k} (Functor.F₀ (ContextInterp Δ) (ρ)) ≃  (ContextInterp Δ) ∘F (extendSetEnv-αs αs (NatEnv ρ)) )
                       → (η : NaturalTransformation ((ContextInterp Δ) ×Set (SetSem ⊢F)) (SetSem ⊢G))
                       → {ρ ρ' : SetEnv}
                       → (f : SetEnvCat Categories.Category.[ ρ , ρ' ])
                       → (Sets Category.≈
                        (Sets Category.∘ (makeNat αs Δ ⊢F ⊢G Diso η (NatEnv ρ')))
                        (Functor.F₁ ((ContextInterp Δ) ∘F ForgetFVSetEnv) f))
                       ((Sets Category.∘ Functor.F₁ (NatTypeFunctor αs ⊢F ⊢G) f)
                        (makeNat αs Δ ⊢F ⊢G Diso η (NatEnv ρ)))
curryNatType-commute αs Δ ⊢F ⊢G Diso η {ρ@(SetEnv[ tc , fv ])} {ρ'@(SetEnv[ tc , fv' ])} f@(record { eqTC = ≡.refl ; fv = fvmorph }) {x} =  
    begin
      makeNat αs Δ ⊢F ⊢G Diso η (NatEnv ρ) (Functor.F₁ ((ContextInterp Δ) ∘F ForgetFVSetEnv) f x) 
    ≡⟨ ≡.cong (makeNat αs Δ ⊢F ⊢G Diso η (NatEnv ρ)) (Functor.identity (ContextInterp Δ)) ⟩ 
--       makeNat αs D F G Diso η (NatEnv ρ) x
--     -- ≡⟨  ≡.sym (Het.≅-to-≡ (NatTypeSem3-map-id αs F G f)) ⟩
--     ≡⟨  ≡.sym (Het.≅-to-≡ _≅_.refl) ⟩
      Functor.F₁ (NatTypeFunctor αs ⊢F ⊢G) f (makeNat αs Δ ⊢F ⊢G Diso η (NatEnv ρ) x)
    ∎ 


curryNatType : ∀ {Γ} {k} (αs : Vec (FVar 0) k) {F} {G} (Δ : TermCtx Γ ∅)
               → (⊢F : Γ ≀ ∅ ,++ αs ⊢ F) (⊢G : Γ ≀ ∅ ,++ αs ⊢ G)
               -- → (D F G : Functor SetEnvCat Sets)
               → (Diso : ∀ ρ → ConstF {C = Sets^ k} (Functor.F₀ (ContextInterp Δ) (ρ)) ≃  (ContextInterp Δ) ∘F (extendSetEnv-αs αs (NatEnv ρ)) )
--               → (D F G : Functor SetEnvCat Sets)
  --             → (Diso : ∀ ρ → ConstF {C = Sets^ k} (Functor.F₀ D (ρ)) ≃  D ∘F (extendSetEnv-αs αs (NatEnv ρ)) )
               → NaturalTransformation ((ContextInterp Δ) ×Set (SetSem ⊢F)) (SetSem ⊢G)
               → NaturalTransformation ((ContextInterp Δ) ∘F ForgetFVSetEnv) (NatTypeFunctor αs ⊢F ⊢G)
curryNatType αs Δ ⊢F ⊢G Diso η = 
  ntHelper (record { η = λ ρ → makeNat αs Δ ⊢F ⊢G Diso η (NatEnv ρ) 
                   ; commute =  curryNatType-commute αs Δ ⊢F ⊢G Diso η } )







-- applyNat-η : ∀ {k} {αs : Vec (FVar 0) k} {F} {G} (ρ : SetEnv)
--              → Functor.F₀ (NatTypeFunctor αs F G ×Set F) ρ
--              → Functor.F₀ G ρ 
-- applyNat-η ρ (NatT3[ nat ] , Fρ) = {!!}




{-

open import TypeSemantics.SetSemExtendEnvVec using (extendEnvFVarVec) 
open import Utils using (foreach)


-- some hackery to pick the right component of natural transformation in applyNat 
interpVec : ∀ {k} {Γ} {Φ} (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
             → (⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks)
             → SetEnv
             → Vec Set k
interpVec [] {[]} tt _ = []
interpVec {k = suc k} (α ∷ αs) {K ∷ Ks} (⊢K , ⊢Ks) ρ =
  let ρ-ext = ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks ρ) ] 
      ks : Vec Set k 
      ks = interpVec αs ⊢Ks ρ
    in (Functor.F₀ (SetSem ⊢K) ρ-ext) ∷ ks  



interpVec-lem : ∀ {k} {Γ} {Φ} (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
                → (⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks)
                → (ρ : SetEnv)
                → ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks ρ) ]
                ≡ (Functor.F₀ (extendEnvFVarVec αs ⊢Ks) ρ)
interpVec-lem [] {[]} tt ρ = ≡.refl
interpVec-lem (α ∷ αs) {K ∷ Ks} (⊢K , ⊢Ks) ρ =
  let
      ρ-lhs = ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks ρ) ] 
      SemK-lhs = Functor.F₀ (SetSem ⊢K) ρ-lhs 

      lhs  =  ρ [ α ∷ αs :fvs= ConstF SemK-lhs ∷ to0Functors (interpVec αs ⊢Ks ρ) ]

      ρ-rhs = Functor.F₀ (extendEnvFVarVec αs ⊢Ks) ρ 
      SemK-rhs = Functor.F₀ (SetSem ⊢K) ρ-rhs

      rec : (ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks ρ) ])
          ≡ Functor.F₀ (extendEnvFVarVec αs ⊢Ks) ρ
      rec = interpVec-lem αs ⊢Ks ρ

      SemK-lhs≡SemK-rhs : SemK-lhs ≡ SemK-rhs 
      SemK-lhs≡SemK-rhs = ≡.cong (Functor.F₀ (SetSem ⊢K)) rec 
  in  begin lhs
          ≡⟨ :fv=-unwind ρ α αs (ConstF SemK-lhs) (to0Functors (interpVec αs ⊢Ks ρ)) ⟩ -- just need proof that ρ [ α ∷ αs :fvs= ... ] ≡ ρ [ αs :fvs= ... ] [ α :fv= .. ] 
          ρ-lhs [ α :fv= ConstF SemK-lhs ]
          ≡⟨ :fv=-cong ρ-lhs ρ-rhs  α (ConstF SemK-lhs) (ConstF SemK-rhs) rec (≡.cong ConstF SemK-lhs≡SemK-rhs)    ⟩
          ρ-rhs [ α :fv= ConstF SemK-rhs ]
          ∎   


-- we have an issue here:
--
-- we have FρKs : Functor.F₀ F (Functor.F₀ (extendEnvFVarVec αs ⊢Ks) ρ)
-- which, when αs = α ∷ αs, = Functor.F₀ F (Functor.F₀ (extendEnvFVarVec αs ⊢Ks) (ρ [ α :fv= to0Functors (Functor.F₀ (SetSem ⊢K) (Functor.F₀ (extendEnvFVarVec αs ⊢Ks) ρ)) ]))
-- 
-- and ηKs which expects an argument of type
--
-- Functor.F₀ F ((NatEnv ρ) [ αs :fvs= to0Functors (Functor.F₀ (SetSemVec ⊢Ks) ρ) ])

-- 
--


-- applyNat-η : ∀ {k} {Γ} {Φ} (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
--              → (⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks)
--              → (F G : Functor SetEnvCat Sets)
--              → (ρ : SetEnv) 
--              → Functor.F₀ (NatTypeFunctor αs F G ×Set (F ∘F extendEnvFVarVec αs ⊢Ks)) (NatEnv ρ)
--              → Functor.F₀ (G ∘F extendEnvFVarVec αs ⊢Ks) (NatEnv ρ)
-- applyNat-η αs {Ks} ⊢Ks F G ρ (NatT3[ nat ] , FρKs) rewrite (≡.sym (interpVec-lem αs ⊢Ks (NatEnv ρ))) = 
--     let 
--         nat-Ks : Functor.F₀ F (NatEnv ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks (NatEnv ρ)) ])
--                → Functor.F₀ G (NatEnv ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks (NatEnv ρ)) ])
--         nat-Ks = NaturalTransformation.η nat ( interpVec αs ⊢Ks (NatEnv ρ) ) 
-- 
--      in nat-Ks FρKs 





applyNat-η-forget : ∀ {k} {Γ} {Φ} (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
             → (⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks)
             → (F G : Functor SetEnvCat Sets)
             → (ρ : SetEnv) 
             → Functor.F₀ (NatTypeFunctor αs F G ×Set (F ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)) ρ
             → Functor.F₀ (G ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv) ρ 
applyNat-η-forget αs {Ks} ⊢Ks F G ρ (NatT3[ nat ] , FρKs) rewrite (≡.sym (interpVec-lem αs ⊢Ks (NatEnv ρ))) = 
    let 
        nat-Ks : Functor.F₀ F (NatEnv ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks (NatEnv ρ)) ])
               → Functor.F₀ G (NatEnv ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks (NatEnv ρ)) ])
        nat-Ks = NaturalTransformation.η nat ( interpVec αs ⊢Ks (NatEnv ρ) ) 

     in nat-Ks FρKs 

        -- FρKs : proj₂ (Functor.₀ (NatTypeFunctor αs F G ※ F ∘F extendEnvFVarVec αs ⊢Ks) ρ)
        --      = Functor.F₀ F (Functor.F₀ (extendEnvFVarVec αs ⊢Ks) ρ)


-- make naturality/commutativity proof easy by taking only tc part of environment as argument.
-- then in naturality proof, we have a morphism of environments, which gives a proof that
-- tc parts of environments are equal 
applyNat-η2 : ∀ {k} {Γ} {Φ} (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
             → (⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks)
             → (F G : Functor SetEnvCat Sets)
             -- → (ρ : SetEnv) 
             → (tc : SetEnvTC) 
             → Functor.F₀ (NatTypeFunctor αs F G ×Set (F ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)) (NatEnvTC tc)
             → Functor.F₀ (G ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv) (NatEnvTC tc)
applyNat-η2 αs {Ks} ⊢Ks F G tc (NatT3[ nat ] , FρKs) rewrite (≡.sym (interpVec-lem αs ⊢Ks (NatEnvTC tc))) = 
    let 
        nat-Ks : Functor.F₀ F (NatEnvTC tc [ αs :fvs= to0Functors (interpVec αs ⊢Ks (NatEnvTC tc)) ])
               → Functor.F₀ G (NatEnvTC tc [ αs :fvs= to0Functors (interpVec αs ⊢Ks (NatEnvTC tc)) ])
        nat-Ks = NaturalTransformation.η nat ( interpVec αs ⊢Ks (NatEnvTC tc) ) 

     in nat-Ks FρKs 


applyNat-commute : ∀ {k} {Γ} {Φ} (αs : Vec (FVar 0) k)
                     {Ks : Vec TypeExpr k}
                     → (⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks)
                     → (F G : Functor SetEnvCat Sets)
                     → {ρ ρ' : SetEnv}
                     → (f : SetEnvCat Categories.Category.[ ρ , ρ' ])
                     → Sets [
                        (applyNat-η2 αs ⊢Ks F G (SetEnv.tc ρ'))
                        ∘' (Functor.F₁ (NatTypeFunctor αs F G ×Set (F ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)) f)
                     ≈ 
                        (Functor.F₁ (G ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv) f)
                        ∘' (applyNat-η2 αs ⊢Ks F G (SetEnv.tc ρ))
                     ]

-- matching on (with NatEnv-eq f ) is very slow.. 
applyNat-commute αs ⊢Ks F G {ρ@(Env[ tc , fv ])} {ρ'@(Env[ tc , fv' ])} f@( record { eqTC = ≡.refl ; fv = fvm}) {NatT3[ nat ] , FρKs} =
  let
      -- Ff  
      extend-f : SetEnvMorph (Functor.F₀ (extendEnvFVarVec αs ⊢Ks) (NatEnv ρ))
                             (Functor.F₀ (extendEnvFVarVec αs ⊢Ks) (NatEnv ρ'))
      extend-f = Functor.F₁ (extendEnvFVarVec αs ⊢Ks) (Functor.F₁ ForgetFVSetEnv f)

      Forget-f≈id : SetEnvCat [ Functor.F₁ ForgetFVSetEnv f ≈ idSetEnv ]
      Forget-f≈id = ≡.refl

      -- propagate identity with functor laws 
      extend-f≈id : SetEnvCat [ extend-f ≈ idSetEnv ]
      extend-f≈id = SECHR.begin extend-f
                            SECHR.≈⟨ Functor.F-resp-≈ (extendEnvFVarVec αs ⊢Ks) Forget-f≈id ⟩
                                Functor.F₁  (extendEnvFVarVec αs ⊢Ks) idSetEnv
                            SECHR.≈⟨ Functor.identity (extendEnvFVarVec αs ⊢Ks) ⟩
                                idSetEnv
                                SECHR.∎

      Ff≈id : Sets [ Functor.F₁ F extend-f ≈ idf ]
      Ff≈id = SHR.begin  Functor.F₁ F extend-f 
                SHR.≈⟨ Functor.F-resp-≈ F extend-f≈id ⟩
                    Functor.F₁  F idSetEnv
                SHR.≈⟨ Functor.identity F ⟩
                    idf
                    SHR.∎

      Gf≈id : Sets [ Functor.F₁ G extend-f ≈ idf ]
      Gf≈id = SHR.begin Functor.F₁ G extend-f
                SHR.≈⟨ Functor.F-resp-≈ G extend-f≈id ⟩
                    Functor.F₁  G idSetEnv
                SHR.≈⟨ Functor.identity G ⟩
                    idf
                    SHR.∎

      prod-id : ∀ {A : Set} → Sets [ funcprod (idf {A = A} , Functor.F₁ F extend-f) ≈ funcprod (idf , idf) ]
      prod-id {A} {x} = ≡.cong (_,_ (proj₁ x)) Ff≈id

      apply-tc  = applyNat-η2 αs ⊢Ks F G tc

      apply-tc-≈ : Sets [ (apply-tc ∘' funcprod (idf , Functor.F₁ F extend-f) ) ≈  (apply-tc ∘' funcprod (idf , idf) ) ]
      apply-tc-≈  {x} = ≡.cong apply-tc prod-id 

      Gf-sym-≈ : Sets [ apply-tc ≈ Functor.F₁ G extend-f ∘' apply-tc ]
      Gf-sym-≈ {x} = ≡.sym Gf≈id 
      
    in SHR.begin (apply-tc ∘' funcprod (idf , Functor.F₁ F extend-f) )
              SHR.≈⟨ apply-tc-≈  ⟩
                (apply-tc ∘' funcprod (idf , idf) )
              SHR.≈⟨ ≡.refl ⟩
                (apply-tc)
              SHR.≈⟨ Gf-sym-≈  ⟩ 
                (Functor.F₁ G extend-f ∘' apply-tc)
              SHR.∎ 

  where module SEC = Category SetEnvCat
        module SECHR = SEC.HomReasoning
        module S = Category Sets
        module SHR = S.HomReasoning


applyNat : ∀ {k : ℕ} {Γ} {Φ} → (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
              → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
              → (F G : Functor SetEnvCat Sets)
              → NaturalTransformation ((NatTypeFunctor αs F G) ×Set (F ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv))
                                      (G ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)
applyNat αs ⊢Ks F G = ntHelper
    (record { η = λ ρ →  applyNat-η2 αs ⊢Ks F G (SetEnv.tc ρ)
            ; commute =  applyNat-commute αs ⊢Ks F G  } )


-- goal, simplified:  
-- applyNat-η αs ⊢Ks F G ρ'
--        (NatT3[ nat ] ,
--         Functor.F₁ F (Functor.F₁ (extendEnvFVarVec αs ⊢Ks) (Functor.F₁ ForgetFVSetEnv f)) FρKs)
-- ≡
-- Functor.F₁ G (Functor.F₁ (extendEnvFVarVec αs ⊢Ks) (Functor.F₁ ForgetFVSetEnv f))
--       (applyNat-η αs ⊢Ks F G ρ (NatT3[ nat ] , FρKs)




open Utils.≃-Reasoning 

αs∋φ-diff-arity : ∀ {k j : ℕ} → (αs : Vec (FVar 0) k)
              → (φ : FVar j) 
              → j ≢ 0 
              → (∅fv ,++ αs) ∋ φ → ⊥' 
-- first two cases match j to 0, so we have j≢0 : 0 ≢ 0  
αs∋φ-diff-arity (α ∷ αs) .α j≢0 lookupZ = exFalso (j≢0 ≡.refl)
αs∋φ-diff-arity (α ∷ αs) φ j≢0 (lookupS _ αs∋φ) = exFalso (j≢0 ≡.refl)
-- this case uses induction 
αs∋φ-diff-arity (α ∷ αs) φ j≢0 (lookupDiffArity _ αs∋φ) = αs∋φ-diff-arity αs φ j≢0 αs∋φ
              

VarSem-FV-extend-≃ : ∀ {k j : ℕ} {Γ} {Φ} → (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
              → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
              → (φ : FVar j) 
              → (∅fv ,++ αs) ∋ φ 
              → VarSem-FV φ ∘F extendEnvFVarVec αs ⊢Ks
              ≃ VarSem-FV φ ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv 

-- Goal: VarSem-FV α ∘F extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks
--       ≃
--       VarSem-FV α ∘F
--       (extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks) ∘F ForgetFVSetEnv

-- can we prove this case??? 
-- seems like maybe not... without knowing that Ks don't depend on αs  
VarSem-FV-extend-≃ (α ∷ αs) {Ks = K ∷ Ks} (⊢K , ⊢Ks) .α lookupZ =
  let
      -- h : VarSem-FV α ∘F extendEnvFVar α ⊢K ≃ SetSem ⊢K
      -- h = ? 

      rec = VarSem-FV-extend-≃ αs {Ks = Ks} ⊢Ks α {!!}

    in {!!} 
    {-
      begin≃
            VarSem-FV α ∘F (extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks)
            ≃⟨ ? ⟩
            (VarSem-FV α ∘F extendEnvFVar α ⊢K) ∘F extendEnvFVarVec αs ⊢Ks
            ≃⟨ ? ⟩
            SetSem ⊢K ∘F extendEnvFVarVec αs ⊢Ks
            ≃⟨ ? ⟩
            VarSem-FV α ∘F (extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks) ∘F ForgetFVSetEnv
            ≃∎ 
            -}
            


VarSem-FV-extend-≃ (α ∷ αs) {Ks = K ∷ Ks} (⊢K , ⊢Ks) φ (lookupS φ≢α  αs∋φ) =
    let rec  : VarSem-FV φ ∘F extendEnvFVarVec αs ⊢Ks
             ≃ VarSem-FV φ ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv
        rec = VarSem-FV-extend-≃ αs {Ks = Ks} ⊢Ks φ αs∋φ

        diff-id-≃ : VarSem-FV φ ∘F extendEnvFVar α ⊢K
                  ≃ VarSem-FV φ 
        diff-id-≃ = {! _ⓘˡ_   !} 
    in begin≃  VarSem-FV φ ∘F (extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks)
            ≃˘⟨   NI.associator (extendEnvFVarVec αs ⊢Ks)  (extendEnvFVar α ⊢K) (VarSem-FV φ)    ⟩
               (VarSem-FV φ ∘F extendEnvFVar α ⊢K) ∘F extendEnvFVarVec αs ⊢Ks
            -- VarSem-FV φ absorbs extendEnvFVar α ⊢K 
            ≃⟨   diff-id-≃ NI.ⓘʳ (extendEnvFVarVec αs ⊢Ks)    ⟩
               VarSem-FV φ ∘F extendEnvFVarVec αs ⊢Ks
            -- inductive step 
            ≃⟨ rec ⟩
               VarSem-FV φ ∘F (extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)
            -- VarSem-FV φ absorbs extendEnvFVar α ⊢K 
            ≃˘⟨  diff-id-≃ NI.ⓘʳ (extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)    ⟩
               (VarSem-FV φ ∘F extendEnvFVar α ⊢K) ∘F (extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)
            -- assoc 
            ≃⟨ NI.associator (extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv) (extendEnvFVar α ⊢K) (VarSem-FV φ)   ⟩
               VarSem-FV φ ∘F (extendEnvFVar α ⊢K ∘F (extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv))
            -- assoc 
            ≃˘⟨  (VarSem-FV φ) NI.ⓘˡ (NI.associator (ForgetFVSetEnv) (extendEnvFVarVec αs ⊢Ks) (extendEnvFVar α ⊢K))  ⟩
               VarSem-FV φ ∘F  ((extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks) ∘F ForgetFVSetEnv)
            ≃∎  

-- impossible case because have j≢0 and αs∋φ 
VarSem-FV-extend-≃ (α ∷ αs) {Ks = K ∷ Ks} (⊢K , ⊢Ks) φ (lookupDiffArity j≢0 αs∋φ) = exFalso (αs∋φ-diff-arity αs φ j≢0 αs∋φ) 


extendEnvFVarVec-Forget-≃ : ∀ {k : ℕ} {Γ} {Φ} → (αs : Vec (FVar 0) k) {F : TypeExpr} {Ks : Vec TypeExpr k}
              → (⊢F : Γ ≀ (∅ ,++ αs) ⊢ F)
              → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
              → SetSem ⊢F ∘F extendEnvFVarVec αs ⊢Ks
              ≃ SetSem ⊢F ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv 
extendEnvFVarVec-Forget-≃ αs {Ks = Ks} 𝟘-I ⊢Ks = {!!}
extendEnvFVarVec-Forget-≃ αs {Ks = Ks} 𝟙-I ⊢Ks = {!!}
extendEnvFVarVec-Forget-≃ αs {Ks = Ks} (AppT-I Γ∋φ Fs ⊢Fs) ⊢Ks = {!!}
extendEnvFVarVec-Forget-≃ (α ∷ αs) {Ks = K ∷ Ks} (AppF-I {φ = φ} Φ∋φ Fs ⊢Fs) (⊢K , ⊢Ks) = {!!}

-- AppF case 
-- Goal:
-- eval ∘F (VarSem-FV φ ※ SetSemVec ⊢Fs) ∘F extend
-- ≃
-- eval ∘F ((VarSem-FV φ ∘F extend) ※ (SetSemVec ⊢Fs ∘F extend)) 
-- ≃
-- eval ∘F ((VarSem-FV φ ∘F extend ∘F ForgetFVSetEnv) ※ (SetSemVec ⊢Fs ∘F extend ∘F ForgetFVSetEnv)) 
-- ≃
-- eval ∘F (VarSem-FV φ ※ SetSemVec ⊢Fs) ∘F extend ∘F ForgetFVSetEnv

extendEnvFVarVec-Forget-≃ αs {Ks = Ks} (+-I ⊢F ⊢G) ⊢Ks = {!!}
extendEnvFVarVec-Forget-≃ αs {Ks = Ks} (×-I ⊢F ⊢G) ⊢Ks = {!!}
-- can prove Nat case if we have proof that extension functors preserves SetEnv.tc 
extendEnvFVarVec-Forget-≃ αs {Ks = Ks} (Nat-I ⊢F ⊢G) ⊢Ks = {!!}
extendEnvFVarVec-Forget-≃ αs {Ks = Ks} (μ-I F ⊢F Gs ⊢Gs) ⊢Ks = {!!}

-- let extend =  extendEnvFVarVec αs ⊢Ks
-- ((fixH ∘F TEnv ⊢F) ∘F ForgetFVSetEnv ※ SetSemVec ⊢Gs)
-- ∘F extend
-- ≃ 
-- ((fixH ∘F TEnv ⊢F) ∘F ForgetFVSetEnv ∘F extend ※ SetSemVec ⊢Gs ∘F extend)
-- ≃ 
-- -- left component absorbs extend 
-- -- use IH on right component 
-- ((fixH ∘F TEnv ⊢F) ∘F ForgetFVSetEnv ∘F (extend ∘F ForgetFVSetEnv)) ※ (SetSemVec ⊢Gs ∘F (extend ∘F ForgetFVSetEnv))
-- ≃ 
-- ((fixH ∘F TEnv ⊢F) ∘F ForgetFVSetEnv ※ SetSemVec ⊢Gs)
-- ∘F (extend ∘F ForgetFVSetEnv)
-- 
-- 
-- 
-- ((eval ∘F
-- ((fixH ∘F TEnv ⊢F) ∘F ForgetFVSetEnv ※ SetSemVec ⊢Gs))
-- ∘F extendEnvFVarVec αs ⊢Ks)
-- ≃ 
-- ((eval ∘F
-- ((fixH ∘F TEnv ⊢F) ∘F ForgetFVSetEnv ※ SetSemVec ⊢Gs))
-- ∘F extendEnvFVarVec αs ⊢Ks ∘F ForgetFVSetEnv)




{-
extendEnvFVarVec-Forget-≃ [] {Ks = []} ⊢F tt = {!      !} 
extendEnvFVarVec-Forget-≃ (α ∷ αs) {F = F} {Ks = K ∷ Ks} ⊢F (⊢K , ⊢Ks) =
  let
       extendF = fo-subst-preserves-typing F K ⊢F {!  !} 

       -- rec = extendEnvFVarVec-Forget-≃ αs ⊢Ks 
    in {!!} 
-}


-- cons case: 
-- Goal: SetSem ⊢F ∘F extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks ≃
--       SetSem ⊢F ∘F
--       (extendEnvFVar α ⊢K ∘F extendEnvFVarVec αs ⊢Ks) ∘F ForgetFVSetEnv
-- ————————————————————————————————————————————————————————————
-- ⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks
-- ⊢K  : Γ ≀ Φ ⊢ K
-- ⊢G  : Γ ≀ (∅ ,++ αs) ,, α ⊢ G
-- ⊢F  : Γ ≀ (∅ ,++ αs) ,, α ⊢ F
-- Ks  : Vec TypeExpr n
-- K   : TypeExpr
-- G   : TypeExpr   (not in scope)
-- F   : TypeExpr   (not in scope)
-- αs  : Vec (FVar 0) n
-- α   : FVar 0
-- n   : ℕ   (not in scope)
-- Φ   : FunCtx   (not in scope)
-- Γ   : TCCtx   (not in scope)





{- try to make it work without inserting ForgetFVSetEnv 
applyNat-η : ∀ {k} {Γ} {Φ} (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
             → (⊢Ks : foreach (_≀_⊢_ Γ Φ) Ks)
             → (F G : Functor SetEnvCat Sets)
             → (ρ : SetEnv) 
             → Functor.F₀ (NatTypeFunctor αs F G ×Set (F ∘F extendEnvFVarVec αs ⊢Ks)) ρ
             → Functor.F₀ (G ∘F extendEnvFVarVec αs ⊢Ks) ρ
applyNat-η αs {Ks} ⊢Ks F G ρ (NatT3[ nat ] , FρKs) = -- rewrite (≡.sym (interpVec-lem αs ⊢Ks (ρ))) = 
    let 
        nat-Ks : Functor.F₀ F (NatEnv ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks (ρ)) ])
               → Functor.F₀ G (NatEnv ρ [ αs :fvs= to0Functors (interpVec αs ⊢Ks (ρ)) ])
        nat-Ks = NaturalTransformation.η nat ( interpVec αs ⊢Ks (ρ) ) 

     in {!!} 

applyNat : ∀ {k : ℕ} {Γ} {Φ} → (αs : Vec (FVar 0) k) {Ks : Vec TypeExpr k}
              → (⊢Ks : foreach (λ K → Γ ≀ Φ ⊢ K) Ks)
              → (F G : Functor SetEnvCat Sets)
              → NaturalTransformation ((NatTypeFunctor αs F G) ×Set (F ∘F extendEnvFVarVec αs ⊢Ks))
                                      (G ∘F extendEnvFVarVec αs ⊢Ks)
applyNat αs ⊢Ks F G = ntHelper
    -- (record { η = λ ρ →  applyNat-η2 αs ⊢Ks F G (SetEnv.tc ρ)
    --        ; commute =  applyNat-commute αs ⊢Ks F G  } )
    (record { η = λ ρ →  {!applyNat-η !} 
           ; commute =  {!!} } )

-}

-}

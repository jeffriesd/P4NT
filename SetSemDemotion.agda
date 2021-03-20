
module SetSemDemotion where 



mutual
  SetSem-demotion-Vec : ∀ {n : ℕ} {Γ : TCCtx} → {Φ : FunCtx} → {Fs : Vec TypeExpr n}
                        → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
                        → (⊢Fs : foreach (λ F → Γ ≀ Φ ,, φ ⊢ F) Fs)
                        → VarSem-FV φ ≡ VarSem-TC ψ
                      → SetSemVec ⊢Fs
                        ≡ SetSemVec (demoteVec-preserves-typing {φ = φ} {ψ} Fs ⊢Fs)
  SetSem-demotion-Vec {zero} {Fs = []} φ ψ Data.Unit.tt e = ≡.refl
  -- ≡.refl
  SetSem-demotion-Vec {suc n} {Fs = F ∷ Fs} φ ψ (⊢F , ⊢Fs) e = 
    let Fs≡wFs = SetSem-demotion-Vec φ ψ ⊢Fs e 
        F※Fs≡wF※wFs = ≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F e) Fs≡wFs
        in ≡.cong (_∘F_ (Sets^cons n)) F※Fs≡wF※wFs


  SetSem-demotion : ∀ {Γ : TCCtx} → {Φ : FunCtx} → {F : TypeExpr}
                    → {k : ℕ} → (φ : FVar k) → (ψ : TCVar k)
                    → (⊢F : Γ ≀ Φ ,, φ ⊢ F)
                    → VarSem-FV φ ≡ VarSem-TC ψ
                    -- maybe relax this and use ≈ from SEC 
                    → SetSem ⊢F
                      ≡ SetSem (demotion-preserves-typing {φ = φ} {ψ} F ⊢F)
  SetSem-demotion φ ψ 𝟘-I ρφ≡ρψ = ≡.refl
  SetSem-demotion φ ψ 𝟙-I ρφ≡ρψ = ≡.refl
  SetSem-demotion φ ψ (AppT-I {φ = ϕ} Γ∋p  Fs ⊢Fs) ρφ≡ρψ = 
  -- goal : eval ∘F (VarSem-TC p ※ SetSemVec ⊢Fs) 
  --        ≡ eval ∘F (VarSem-TC p ※ SetSemVec (demoteVec-preserves-typing Fs ⊢Fs))
    let Fs≡wFs = SetSem-demotion-Vec φ ψ ⊢Fs ρφ≡ρψ
        eq-※ = ≡.cong (_※_ (VarSem-TC ϕ)) Fs≡wFs
        in ≡.cong (_∘F_ eval) eq-※
-- goal : eval ∘F (VarSem-FV p ※ SetSemVec ⊢Fs) ≡ 
-- SetSem
--       (demotion-preserves-typing AppF p [ Fs ] (AppF-I Γ∋p Fs ⊢Fs))

  SetSem-demotion (φ ^F k) (ψ ^T k) (AppF-I {φ = ϕ ^F j} Γ∋p  Fs ⊢Fs) ρφ≡ρψ rewrite (SetSem-demotion-Vec (φ ^F k) (ψ ^T k) ⊢Fs ρφ≡ρψ)
      with eqNat j k | ϕ ≟ φ

--   SetSem-demotion {k = k} (φ ^F k) ψ (AppF-I {φ = φ2 ^F j} Φ∋φ2 Fs ⊢Fs) ρ ρφ≡ρψ with eqNat j k | φ2 ≟ φ
-- 
--
-- yes yes goal : 
-- eval ∘F (VarSem-FV (φ ^F k) ※ SetSemVec ⊢Fs) 
-- ≡ eval ∘F (VarSem-TC (ψ ^T k) ※ SetSemVec (demoteVec-preserves-typing Fs ⊢Fs))
  ... | yes ≡.refl | yes ≡.refl rewrite ρφ≡ρψ = ≡.refl
  ... | yes ≡.refl | no _  = ≡.refl
  ... | no _ | yes ≡.refl   = ≡.refl
  ... | no _ | no _  = ≡.refl
-- -- SetSum ∘F (SetSem ⊢F ※ SetSem ⊢G) ≡
--     SetSum ∘F
--     (SetSem (demotion-preserves-typing F ⊢F) ※
--      SetSem (demotion-preserves-typing G ⊢G))
  SetSem-demotion φ ψ (+-I ⊢F ⊢G) ρφ≡ρψ = ≡.cong (_∘F_ SetSum)  (≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F ρφ≡ρψ ) (SetSem-demotion φ ψ ⊢G ρφ≡ρψ ))
  SetSem-demotion φ ψ (×-I ⊢F ⊢G) ρφ≡ρψ = ≡.cong (_∘F_ SetProd) (≡.cong₂ _※_ (SetSem-demotion φ ψ ⊢F ρφ≡ρψ ) (SetSem-demotion φ ψ ⊢G ρφ≡ρψ ))
  SetSem-demotion {Γ} {Φ} φ ψ (Nat-I ⊢F ⊢G) ρφ≡ρψ = SetSem-weaken {Γ} {Φ} ψ (Nat-I ⊢F ⊢G)
  SetSem-demotion φ ψ (μ-I {φ = ϕ} {αs = αs} F ⊢F Gs ⊢Gs) ρφ≡ρψ 
        rewrite (SetSem-weaken-TEnv ϕ αs ψ ⊢F) | (SetSem-demotion-Vec φ ψ ⊢Gs ρφ≡ρψ) = ≡.refl 

  -- {! eval ∘F (fixH ∘F TEnv ⊢F ※ SetSemVec ⊢Gs) ≡ eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (demoteVec-preserves-typing Gs ⊢Gs)) !} 
-- goal : eval ∘F (fixH ∘F TEnv ⊢F                   ※ SetSemVec ⊢Gs) ≡
--        eval ∘F (fixH ∘F TEnv (weakenTCCtx ψ F ⊢F) ※ SetSemVec (demoteVec-preserves-typing Gs ⊢Gs))



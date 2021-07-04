-- definitions about het equality that are not being used elsewhere 


module HetNaturality (F G : Functor C Sets) where 
-- not used as of 5/02 

  module F = Functor F 
  module G = Functor G 

  open Het.≅-Reasoning

  -- if F and G are pointwise-equal 
  postulate 
    eqFG : ∀ X → F.₀ X ≡ G.₀ X


  f-η : ∀ (X : Category.Obj C) 
        → Functor.F₀ F X →  Functor.F₀ G X 
  f-η X = ≡.subst (λ x → x) (eqFG X) 


  -- and both paths through the naturality square are identities
  postulate 
    -- eqnat : ∀ f X x → f-η X (F.₁ f x) ≅ x 
    eqnat : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → f-η Y (Functor.F₁ F f x) ≅ x
    eqnat2 : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → x ≅ Functor.F₁ G f (f-η X x)



  -- then we can prove naturality 
  f-commute-het : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x}
              → f-η Y (Functor.F₁ F f x)
              ≅ Functor.F₁ G f (f-η X x)
  f-commute-het {X} {Y} f {x} = begin
      f-η Y (Functor.F₁ F f x)
    ≅⟨ eqnat ⟩ 
      x
    ≅⟨ eqnat2 ⟩
      Functor.F₁ G f (f-η X x)
    ∎ 

  f-commute : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x}
              → f-η Y (Functor.F₁ F f x)
              ≡ Functor.F₁ G f (f-η X x)
  f-commute {X} {Y} f {x} = Het.≅-to-≡ (f-commute-het f) 


  nattr : NaturalTransformation F G 
  nattr = record { η = f-η 
             ; commute = f-commute 
             ; sym-commute = λ f → ≡.sym (f-commute f) } 



-- slight variant where instead of asking for Heterogeneous equality for Fmap, Gmap, we 
-- ask for equality with a subst. 
-- 
-- we also have additional hypotheses of eqF and eqG being constant on all objects in C 
module HetNaturality3 (F G : Functor C Sets) 
-- NOT USED as of 5/02 
    (eqFG   : ∀ X   → Functor.F₀ F X ≡ Functor.F₀ G X)
    (eqF    : ∀ X Y → Functor.F₀ F X ≡ Functor.F₀ F Y)
    (eqG    : ∀ X Y → Functor.F₀ G X ≡ Functor.F₀ G Y)
    (eqFmap : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → Functor.F₁ F f x ≡ (≡.subst idf (eqF X Y) x))
    (eqGmap : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → Functor.F₁ G f x ≡ (≡.subst idf (eqG X Y) x))
  where 

  module F = Functor F 
  module G = Functor G 
  open Het.≅-Reasoning

  f-η : ∀ (X : Category.Obj C) 
        → Functor.F₀ F X →  Functor.F₀ G X 
  f-η X = ≡.subst (λ x → x) (eqFG X) 

  eqnat-comp : ∀ {X : Category.Obj C} {x} → f-η X x ≅ x
  eqnat-comp {X} rewrite eqFG X = Het.refl 

  tohet : ∀ {X Y : Set} (e : X ≡ Y) → ∀ {x : X} → (≡.subst idf e x) ≅ x 
  tohet e {x} = Het.≡-subst-removable idf e x

  eqFmap' : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → Functor.F₁ F f x ≅ x 
  eqFmap' {X} {Y} = Het.trans (Het.≡-to-≅ eqFmap) (tohet (eqF X Y)) 

  eqGmap' : ∀ {X Y : Category.Obj C} {f : C Categories.Category.[ X , Y ]} {x} → Functor.F₁ G f x ≅ x 
  eqGmap' {X} {Y} = Het.trans (Het.≡-to-≅ eqGmap) (tohet (eqG X Y)) 


  -- -- then we can prove naturality still 
  f-commute-het : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x}
              → f-η Y (Functor.F₁ F f x)
              ≅ Functor.F₁ G f (f-η X x)
  f-commute-het {X} {Y} f {x} =  
      begin
          f-η Y (Functor.F₁ F f x)
        ≅⟨ eqnat-comp {Y} ⟩ 
          (Functor.F₁ F f x)
        ≅⟨ eqFmap' ⟩ 
          x 
        ≅⟨ Het.sym (eqnat-comp {X}) ⟩
          f-η X x
        -- ≅⟨ Het.sym eqGmap ⟩
        ≅⟨ Het.sym eqGmap' ⟩ 
          Functor.F₁ G f (f-η X x)
        ∎ 


  F⇒G : NaturalTransformation F G 
  F⇒G = ntHelper (record { η = f-η ; commute = λ f → Het.≅-to-≡ (f-commute-het f) })


  g-η : ∀ (X : Category.Obj C) 
        → Functor.F₀ G X →  Functor.F₀ F X 
  g-η X = ≡.subst (λ x → x) (≡.sym (eqFG X))

  g-eqnat-comp : ∀ {X : Category.Obj C} {x} → g-η X x ≅ x
  g-eqnat-comp {X} rewrite (≡.sym (eqFG X)) = Het.refl 

  -- then we can prove naturality still 
  g-commute-het : ∀  {X Y : Category.Obj C}
              (f : C Categories.Category.[ X , Y ]) 
              → ∀ {x : Functor.F₀ G X}
              → g-η Y (Functor.F₁ G f x)
              ≅ Functor.F₁ F f (g-η X x)
  g-commute-het {X} {Y} f {x} = begin
      g-η Y (Functor.F₁ G f x)
    ≅⟨ g-eqnat-comp ⟩ 
      (Functor.F₁ G f x)
    ≅⟨ eqGmap' ⟩ 
      x 
    ≅⟨ Het.sym g-eqnat-comp ⟩ 
      g-η X x
    ≅⟨ Het.sym eqFmap' ⟩ 
      Functor.F₁ F f (g-η X x)
    ∎ 



  G⇒F : NaturalTransformation G F 
  G⇒F = ntHelper (record { η = g-η ; commute = λ f → Het.≅-to-≡ (g-commute-het f) })


  f-η∘g-η : ∀ {X : Category.Obj C} → ∀ {x} 
            → f-η X (g-η X x)
            ≡ x 
  f-η∘g-η {X} {x} rewrite (eqFG X) = ≡.refl 

  g-η∘f-η : ∀ {X : Category.Obj C} → ∀ {x} 
            → g-η X (f-η X x)
            ≡ x 
  g-η∘f-η {X} {x} rewrite (eqFG X) = ≡.refl 


  F≃G : NaturalIsomorphism F G 
  F≃G = record { F⇒G = F⇒G ; F⇐G = G⇒F ; iso = λ X → record { isoˡ = g-η∘f-η ; isoʳ = f-η∘g-η } } 




module HetFunctoriality (F : Functor Sets Sets) 
-- not used as of 5/02 
  (X Y : Set) (f : X → Y) (fid : ∀ x → f x ≅ x)
  where 

  open ≡.≡-Reasoning 

  Fmap-id : ∀ z → (e : X ≡ Y) → Functor.F₁ F f z ≅ z 
  Fmap-id z ≡.refl = 
    let feq : ∀ x → f x ≡ x 
        feq x = Het.≅-to-≡ (fid x) 

        f≈id : Sets Categories.Category.[ f ≈ idf ] 
        f≈id {x} = feq x 

        Ff≈Fid : Sets Categories.Category.[ Functor.F₁ F f ≈ Functor.F₁ F idf ] 
        Ff≈Fid {x} = Functor.F-resp-≈ F f≈id 

        Ff≈id : Sets Categories.Category.[ Functor.F₁ F idf ≈ idf ] 
        Ff≈id {x} = Functor.identity F 

      in Het.≡-to-≅ (≡.trans Ff≈Fid Ff≈id) 


-- variant on HetFunctoriality for arbitrary source category C 
-- 
-- since morphisms in C aren't necessarily functions, we can't ask that f 
-- is extensionally equal to the identity morphism.. we have to ask for a proof
-- of (heteregeneous) intensional equality 
module HetFunctoriality2 (F : Functor C Sets) 
  (X Y : C.Obj) (f : C Categories.Category.[ X , Y ]) (fid : f ≅ C.id {A = X})
-- not used as of 5/02 
  where 
  
  open ≡.≡-Reasoning 

  Fmap-id : (e : X ≡ Y) → ∀ {x} → Functor.F₁ F f x ≅ x
  Fmap-id ≡.refl {x} = 
    let feq : f ≡ C.id
        feq = Het.≅-to-≡ fid 

        f≈id : C Categories.Category.[ f ≈ C.id ] 
        f≈id = ≡.subst (λ g → C Categories.Category.[ g ≈ C.id ]) (≡.sym feq) C.Equiv.refl 

        Ff≈Fid : Sets Categories.Category.[ Functor.F₁ F f ≈ Functor.F₁ F C.id ] 
        Ff≈Fid {x} = Functor.F-resp-≈ F f≈id 

        Ff≈id : Sets Categories.Category.[ Functor.F₁ F C.id ≈ idf ] 
        Ff≈id {x} = Functor.identity F 

      in Het.≡-to-≅ (≡.trans {i = Functor.F₁ F f x} {j = Functor.F₁ F C.id x} {k = x} Ff≈Fid Ff≈id)


-- want to use 'extensional equality' in Sets^ k
module HetFunctoriality3 (k : ℕ) (F : Functor (Sets^ k) Sets) 
  (Xs Ys : Vec Set k) (fs : (Sets^ k) Categories.Category.[ Xs , Ys ]) (fid : pointwise-het-id fs)
  where 
-- not used 
  
  open ≡.≡-Reasoning 

  idXs : VecMorph Xs Xs
  idXs = makeIdTuple Xs


  gs≈id : ∀ {j} {As : Vec Set j} (gs : VecMorph As As) → pointwise-het-id gs → (Sets^ j) Categories.Category.[ gs ≈ Category.id (Sets^ j) ] 
  gs≈id {As = []} bigtt _ = bigtt
  gs≈id {As = A ∷ As} (g , gs) (gx≅x , gseq) = (Het.≅-to-≡ gx≅x) , (gs≈id gs gseq) 


  Fmap-id : (e : Xs ≡ Ys) → ∀ {x} → Functor.F₁ F fs x ≅ x
  Fmap-id ≡.refl {x} = 
    let 
        -- feq : (Sets^ k) Categories.category
        -- feq = Het.≅-to-≡ fid 

        fs≈id : (Sets^ k) Categories.Category.[ fs ≈ idXs ]
        fs≈id = gs≈id fs fid

        Ff≈Fid : Sets Categories.Category.[ Functor.F₁ F fs ≈ Functor.F₁ F idXs ]
        Ff≈Fid {x} = Functor.F-resp-≈ F fs≈id

        Ff≈id : Sets Categories.Category.[ Functor.F₁ F idXs ≈ idf ] 
        Ff≈id {x} = Functor.identity F 

      in Het.≡-to-≅ (≡.trans Ff≈Fid Ff≈id)



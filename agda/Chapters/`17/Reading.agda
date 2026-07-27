module Chapters.`17.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises
open import Chapters.`12.Reading
open import Chapters.`13.Reading
open import Chapters.`14.Reading
open import Chapters.`15.Reading

 
private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ι ι₁ ι₂ ι₃ : Level
    A B C : Set ℓ 
    𝐁 : A → Set ℓ

--------------------------------------------------------------------------------
-- AH> Before going any further, there are a handful of properties about 
-- type equivalence that will prove necessary. I'm not sure a better place to put
-- these.

module _ where 
  open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)  
  
  ×-is-contr : is-contr A → is-contr B → is-contr (A × B)
  ×-is-contr = {!!} 

  section-is-contr : (f : A → B) → is-equiv f → is-contr (section f)
  section-is-contr f eqv@((σ , sec) , _) with is-equiv⇒is-contr-map (f ∘_) {!!} id
  ... | ((g , eq) , contr) = (g , htpy-eq _ _ eq) , {!eq!} -- is-equiv⇒is-contr-map (_∘ f) ? id

  retraction-is-contr : (f : A → B) → is-equiv f → is-contr (retraction f)
  retraction-is-contr f eqv = {!!} , {!!} 
  
  -- Being an equivalence is a prop.
  -- A better proof route:
  -- 1. Show that section f and retraction f are contractible:
  --    - retraction f → is-contr (section f)
  --    - section f → is-contr (retraction f)
  --    These proofs follow from how post-composition (f ∘_) is an equivalence
  --    if f is an equivalence.
  -- 2. Therefore is-equiv f := section f × retraction f is contractible,
  --    as the product of contractible types is contractible.
  -- 3. Therefore is-equiv f is a prop. 
  is-prop-is-equiv : (f : A → B) → is-prop (is-equiv f)
  is-prop-is-equiv {A = A} {B = B} f = 
    (const⋆-embedding⇒is-prop ∘
      contractibleIfInhabited→const⋆-embedding {A = is-equiv f})
      ifInhabited 
    where
      ifInhabited : is-equiv f → is-contr (is-equiv f)
      ifInhabited eqv = ×-is-contr (section-is-contr f eqv) (retraction-is-contr f eqv) 
    -- Irrelevant⇒is-prop irrelevant-is-equiv
    -- where 
    --   eq-sections : (σ₁ σ₂ : B → A) (sec₁ : f ∘ σ₁ ∼ id) (sec₂ : f ∘ σ₂ ∼ id)
    --                 (ret₁ : σ₁ ∘ f ∼ id) → 
    --                 σ₁ ∼ σ₂ 
    --   eq-sections σ₁ σ₂ sec₁ sec₂ ret₁ = begin 
    --         σ₁          ∼⟨ ap σ₁ ∘ sec₁ ⁻¹ ⟩ 
    --         σ₁ ∘ f ∘ σ₁ ∼⟨ σ₁ ·ₗ (sec₁ ○ (sec₂ ⁻¹)) ⟩ 
    --         σ₁ ∘ f ∘ σ₂ ∼⟨ ret₁ ·ᵣ σ₂ ⟩ 
    --         σ₂ ∎
    --     where open HomReasoning 

    --   special-p : ∀ {y z : B} → ((σ , sec) : section f) → (p : y ≡ z) → p ≡ sec y ⁻¹ ○ ap (f ∘ σ) p ○ sec z
    --   special-p {y = y} {z} (σ , sec) refl = sym (begin
    --     ((sec y ⁻¹) ○ refl) ○ (sec y) ≡⟨ (right-identity (sec y ⁻¹) ⋆ₗ (sec y)) ⟩ 
    --     sec y ⁻¹ ○ sec y ≡⟨ left-inv (sec y) ⟩ 
    --     refl ∎) 
    --     where open PathReasoning

    --   irrelevant-is-equiv : Irrelevant (is-equiv f) 
    --   irrelevant-is-equiv eqv₁@((σ₁ , sec₁) , ρ₁ , ret₁) eqv₂@((σ₂ , sec₂) , ρ₂ , ret₂) 
    --     with fun-ext _ _ (is-equiv⇒equalSplits eqv₁) 
    --        | fun-ext _ _ (is-equiv⇒equalSplits eqv₂)
    --   ... | refl | refl with fun-ext _ _ (eq-sections σ₁ σ₂ sec₁ sec₂ ret₁)
    --   ... | refl   = ap₂ _,_ (ap (σ₁ ,_) (fun-ext _ _ (λ x → special-p (σ₁ , sec₁) (sec₁ x) ○ {! (special-p (σ₁ , sec₁) (sec₁ x) ⁻¹)  !}))) {!   !} 

  -- Because (is-equiv f) is a prop, it's sufficent to compare
  -- just the maps of given equivalences.
  eq-≃ : {e₁ e₂ : A ≃ B} → (fst e₁ ≡ fst e₂) → e₁ ≡ e₂ 
  eq-≃ {e₁ = (f , eqv₁)} {(.f , eqv₂)} refl = ap (f ,_) (is-prop⇒Irrelevant (is-prop-is-equiv f) eqv₁ eqv₂) 

  sym-≃-involutive : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → sym-≃ ∘ (sym-≃ {A = A} {B = B}) ∼ id
  sym-≃-involutive x = eq-≃ refl 
  
  sym-≃² : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → (A ≃ B) ≃ (B ≃ A) 
  sym-≃² = sym-≃ , has-inverse⇒is-equiv (sym-≃ , sym-≃-involutive , sym-≃-involutive) 


--------------------------------------------------------------------------------
-- Ch. 17 The Univalence Axiom
  
--------------------------------------------------------------------------------
-- §17.1 Equivalence forms of the Univalence Axiom 
-- AH> I will first characterize each equivalent form. That they are equivalent
--     follows form the fundamental theorem of identity types.

module _ {ℓ} where
  
  private
    𝒰 = Set ℓ 
    𝒰₁ = Set (lsuc ℓ)

  equiv-eq : ∀ {A B : 𝒰} → A ≡ B → A ≃ B
  equiv-eq refl = refl-≃

  -- Formulation (i): 𝒰 is univalent if equiv-eq is an equivalence.
  Univalence : 𝒰₁
  Univalence = ∀ {A B : 𝒰} → is-equiv (equiv-eq {A = A} {B})

  -- Formulation (ii)
  EquivContractible : 𝒰₁
  EquivContractible = (A : 𝒰) → is-contr (Σ[ B ∈ 𝒰 ] (A ≃ B))

  -- Formulation (iii)
  module _ (A : 𝒰) (P : (X : 𝒰) → A ≃ X → Set ℓ₃) where
    equiv-eval : ((X : 𝒰) (e : A ≃ X) → P X e) → 
                 P A refl-≃  
    equiv-eval f = f A refl-≃

    EquivInduction : Set (lsuc ℓ ⊔ ℓ₃)
    EquivInduction = section equiv-eval

  -- That these three are equivalent follows from the fundamental theorem of identity types
  module _ {A : 𝒰} (pf : IdFundProof {𝐁 = A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B})) where
    univalence-forms : IdFund {A = 𝒰} {A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B}) 
    univalence-forms = fund-thm-id A refl-≃ (λ B → equiv-eq {A = A} {B}) pf 


--------------------------------------------------------------------------------
-- Axiom 17.1.2: The univalence axiom

module _ {ℓ} where
  private
    𝒰 = Set ℓ 
    𝒰₁ = Set (lsuc ℓ)

  postulate 
    -- AH> We are postulating that all universes
    --     (Set ℓ), for any ℓ, are *univalent*.
    univalence : Univalence {ℓ} 

  -- The juicy bit
  eq-equiv : ∀ {A B : 𝒰} → A ≃ B → A ≡ B
  eq-equiv = `sec univalence  


  -- When we want to explicitly specify the equivalence
  univ : ∀ (A B : 𝒰) → (A ≡ B) ≃ (A ≃ B) 
  univ A B = (equiv-eq , univalence)

  -- A proof we can use to derive the rest of the equivalent forms
  univ-proof : ∀ {A : 𝒰} → IdFundProof {𝐁 = A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B})
  univ-proof = familyEquivalence λ _ → univalence
  
  -- The other forms
  univ-forms : IdFund {A = 𝒰} {A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B}) 
  univ-forms = univalence-forms univ-proof

  -- The total space is contractible
  equiv-contractible : EquivContractible {ℓ}
  equiv-contractible A = univ-forms .space-contractible 

  -- We have an identity system
  equiv-induction : (A : 𝒰) (P : (X : 𝒰) → A ≃ X → Set (lsuc ℓ)) → EquivInduction A P
  equiv-induction A P = univ-forms .id-system P  

--------------------------------------------------------------------------------
-- Def 17.1.3: A type X is said to be 𝒰-small if it comes equipped with an element of type:
--   is-small 𝒰 A := Σ[ X ∈ 𝒰 ] (A ≃ X).

module _ {ℓ} where
  private
    𝒰 = Set ℓ
  -- A type is 𝒰 small if it is equivalent to a 𝒰-type.
  is-small : Set ι → Set _
  is-small A = Σ[ X ∈ 𝒰 ] (A ≃ X)

  -- Similarly, a map f : A → B is said to be 𝒰-small
  -- if all of its fibers are 𝒰-small.
  is-small-map : ∀ {A : Set ι₁} {B : Set ι₂} → 
                   (f : A → B) → Set _
  is-small-map {B = B} f = ∀ (b : B) → is-small (fib f b)

  -- AH> N.b. We have to be very careful with universes.
  -- The relation 
  --   _≃_ : Set ℓ₁ → Set ℓ₂ → Set _
  -- relates different universes; the relation 
  --   _≡_ : {A : Set ℓ} → A → A → Set 
  -- homogeneously relates types in the same universe.
  -- Let me demonstrate. Below, we have
  -- - A : Set ι 
  -- - X : Set ℓ
  -- - eq : A ≃ X 
  -- but (eq-equiv eq) is ill-formed, as
  -- the type A ≡ X is ill-formed.
  bad : ∀ (A : Set ι) → ((X , _) : is-small A) → Set {! !}
  bad A (X , eq) = {!eq-equiv eq !}

  --------------------------------------------------------------------------------
  -- Example 17.1.4
  -- AH> Here Rijke claims some examples, which we'll prove.

  -- (1) Any type in 𝒰 is 𝒰-small.
  all-𝒰 : (A : 𝒰) → is-small A
  all-𝒰 A = A , refl-≃
  
  open is-contr
  -- (ii) Any contractible type is 𝒰-small with respect to any universe 𝒰
  -- the idea: every contractible type is isomorphic to the unit type 
  -- (at any universe level). We've proven this fact for ⊤ at level lzero elsewhere;
  -- I'll reprove it here.
  ⊤-≃-contr : ∀ (A : Set ι) → is-contr A → A ≃ (⊤ₚ {ℓ})
  ⊤-≃-contr A (c , C) = 
    (const ttₚ , 
    has-inverse⇒is-equiv (const c , (λ { ttₚ → refl } ) , C))  
  
  -- Proof of (ii)
  contractible-small : ∀ (A : Set ι) → is-contr A → is-small A
  contractible-small A C = ⊤ₚ , ⊤-≃-contr A C 

  -- (iii) For any family P of 𝒰-small types over a 𝒰-small type A, the dependent
  --       product (x : A) → B x is 𝒰-small.
  family-small : ∀ {ι₁ ι₂} → 
                   (A : Set ι₁) →
                   is-small A → 
                   (P : A → Set ι₂) → 
                   -- P is a family of 𝒰 small types
                   ((x : A) → is-small (P x)) → 
                   is-small ((x : A) → P x)
  family-small A (X , (f , eq)) P sm-P with is-equiv⇒has-inverse eq
  ... | f⁻¹ , f∘f⁻¹ , f⁻¹∘f = 
      -- I can't be bothered to prove these inverses.
      Y , (g , has-inverse⇒is-equiv (g⁻¹ , {!!} , {!!}))
      where
        Y : 𝒰 
        Y = (x : X) → sm-P (f⁻¹ x) .fst
        g : ((x : A) → P x) → Y
        g h x = sm-P (f⁻¹ x) .snd .fst (h (f⁻¹ x))

        g⁻¹ : Y → ((x : A) → P x)
        g⁻¹ h a = `inv (sm-P a .snd) (tr (fst ∘ sm-P) (f⁻¹∘f a) (h (f a)) ) 
        
  -- AH> I can't be bothered with the rest of the examples.

  --------------------------------------------------------------------------------
  -- Proposition 17.1.5: For any univalent universe 𝒰 and any type A, the type
  -- is-small 𝒰 A is a proposition.

  -- AH> I would be shocked if this isn't proven somewhere, but I can't find it.
  is-contr-≃ : ∀ (A : Set ι₁) (B : Set ι₂) → A ≃ B → is-contr A → is-contr B
  is-contr-≃ A B (f , eq) (c , C) with is-equiv⇒has-inverse eq 
  ... | f⁻¹ , f∘f⁻¹ , f⁻¹∘f  = (f c) , λ b → begin
      f c       ≡⟨ ap f (C (f⁻¹ b)) ⟩ 
      f (f⁻¹ b) ≡⟨ f∘f⁻¹ b ⟩ 
      b ∎ 
    where
      open PathReasoning

  -- Likewise, we need to prove That _≃_ distributes over Σ---which is a consequence
  -- of Thm 11.1.6. Unfortunately, Thm 1.1.6 (as it is proven) is not universe polymorphic,
  -- and I don't have it in me to rectify that.
  postulate 
    ≃-distrib-Σ : ∀ {A₁ : Set ℓ₁} {A₂ : Set ℓ₂}
                  {B₁ : A₁ → Set ι₁} {B₂ : A₂ → Set ι₂} →
                  ((f , e) : A₁ ≃ A₂) → 
                  ((x : A₁) → B₁ x ≃ B₂ (f x)) → 
                  Σ A₁ B₁ ≃ Σ A₂ B₂ 
    -- ≃-distrib-Σ (f , e) b  = {!11•1•6 !} 

  -- We're learning that we haven't really catalogued a number of 
  -- congruences over _≃_. Above, we need congruence over Σ; 
  -- Here, we need congruence over _≃_.
  -- Note that univalence is restricted to specific *universes*:
  -- We **cannot** simply prove this via
  --   ap (_≃ Y) ∘ eq-equiv 
  -- because A and B are not in the same universe.
  -- 
  -- Proofs are left as exercise to the reader. (Apoorv?)
  postulate
    ≃-distribₗ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {Y : Set ι} → 
                 A ≃ B → (A ≃ Y) ≃ (B ≃ Y)
    -- ≃-distribₗ e = {!!}    

  -- Some more definitions 
                                 

  is-small-prop : ∀ (A : Set ι) → is-prop (is-small A)
  is-small-prop A = (const⋆-embedding⇒is-prop ∘
                       contractibleIfInhabited→const⋆-embedding {A = is-small A})
                      ifInhabited
    where
      ifInhabited : is-small A → is-contr (is-small A)
      ifInhabited (X , e) = 
        is-contr-≃ 
          (is-small X) 
          (is-small A) 
          (≃-distrib-Σ refl-≃ (λ Y → ≃-distribₗ (sym-≃ e))) 
          is-contr-is-small-X
        where
          is-contr-is-small-X : is-contr (is-small X)
          is-contr-is-small-X = equiv-contractible X 
  --------------------------------------------------------------------------------
  -- Corollary 17.1.6: Consider a univalent universe 𝒰 and univalent universe 𝒱 
  -- containing all types in 𝒰. Then the universe inclusion i : 𝒰 → 𝒱 is an embedding.
  -- 
  -- AH> I don't know of a good way to formalize that 𝒾 : 𝒰 → 𝒱 is an inclusion.
  --     Ch. 6 assumes a cumulative hierarchy of universes:
  --       X : 𝒰 ⊢ 𝒯(X) : 𝒰' 
  --     i.e, that if X : Set ℓ then X : Set (lsuc ℓ). 
  --     We don't have cumulativity to play with, really. (Enabling it causes Agda to loop.)
  --     We can fuck with intensional cumulativity---that is, an inclusion operator
  --       𝒾 : Set ℓ → Set (lsuc ℓ)
  --     where lift : A → 𝒾 A is an equivalence.

  data 𝒾 (A : Set ℓ) : Set (lsuc ℓ) where 
    lift : (x : A) → 𝒾 A 
  
  unlift : 𝒾 A → A 
  unlift (lift x) = x 

  𝒾so : ∀ {ℓ} → is-equiv (lift {ℓ})
  𝒾so = has-inverse⇒is-equiv (unlift , (λ { (lift x) → refl }) , Refl)

  module _ where 
    𝒱 = Set (lsuc ℓ) 
    
    -- "Since 𝒱 is assumed to be univalent, it follows that 
    --   fib 𝒾 A ≃ is-small A". Observe that
    --     fib 𝒾 A 
    --   ≡ Σ[ X ∈ 𝒰 ] (𝒾 X ≡ A) 
    -- and 
    --     is-small A 
    --   ≡ Σ[ X ∈ 𝒰 ] (A ≃ X) 
    -- The proof is that, by ≃-distrib-Σ, we need only prove second
    -- components are equivalent. Then:
    --   (𝒾 X ≡ A) 
    --   {by univalence}
    -- ≃ (𝒾 X ≃ A)
    --    {as 𝒾 X ≃ X}
    -- ≃ (X ≃ A) 
    --    {by symmetry}
    -- ≃ (A ≃ X)

    fib≃is-small : (A : 𝒱) → fib 𝒾 A ≃ is-small A
    fib≃is-small A = ≃-distrib-Σ refl-≃ s
      where
        𝒾-eqv : (X : 𝒰) → X ≃ 𝒾 X
        𝒾-eqv X = (lift , 𝒾so)       

        s : (X : 𝒰) → (𝒾 X ≡ A) ≃ (A ≃ X)
        s X = 
          (𝒾 X ≡ A) ≃⟨ univ (𝒾 X) A ⟩ 
          (𝒾 X ≃ A) ≃⟨ ≃-distribₗ (sym-≃ (𝒾-eqv X)) ⟩ 
          (X ≃ A)   ≃⟨ sym-≃² ⟩
          (A ≃ X) ∎
          where 
            open ≃-Reasoning
    
    --  Equivalent types are the same k-types; since (is-small A) is a prop (proven above),
    -- we know that fib 𝒾 A is a prop.
    𝒾-prop-fibers : (A : 𝒱) → is-prop (fib 𝒾 A) 
    𝒾-prop-fibers A = ≃-is-prop (sym-≃ (fib≃is-small A)) (is-small-prop A) 
    
    -- AH> This is Theorem 12.2.3, which isn't proven over heterogeneous universes.
    --     I am done refactoring levels in old theorems!
    postulate 
      prop-fibers⇒is-emb : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → 
                              ((b : B) → is-prop (fib f b)) → is-emb f
    
    -- Having propositional fibers is equivalent to being an embedding,
    -- completing the proof.
    𝒾-emb : is-emb 𝒾 
    𝒾-emb = prop-fibers⇒is-emb 𝒾 𝒾-prop-fibers  
    
  --------------------------------------------------------------------------------
  -- § 17.2 Propositional Extensionality

  --------------------------------------------------------------------------------
  -- Proposition 17.2.1: Let P be a family of propositions over 𝒰. Then
  -- the family of maps
  --   equiv-eq : A ≡ B → pr₁ A ≃ pr₁ B 
  -- where A , B : Σ[ X ∈ 𝒰 ] (P X) given by equiv-eq refl = refl-≃ is an equivalence.

  module _ (P : 𝒰 → Set ℓ) (prop-P : ∀ (X : 𝒰) → is-prop (P X)) where
    equiv-eq′ : ∀ {A B : Σ[ X ∈ 𝒰 ] (P X)} → A ≡ B → fst A ≃ fst B 
    equiv-eq′ refl = refl-≃   


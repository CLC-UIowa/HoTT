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
-- We will need a handful of lemmas about type equivalence. 
--------------------------------------------------------------------------------
-- Congruence properties of _≃_ 
-- 1. Congruence w.r.t. Σ 
-- 2. Congruence w.r.t. _≃_ 

-- Postulated because lazy
postulate 
  -- Likewise, _≃_ is congruent over _≃_. 
  -- Not certain if this is proven elsewhere.
  cong-≃ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ι₁} {Y : Set ι₂} → 
                 A ≃ X → 
                 B ≃ Y → 
                 (A ≃ B) ≃ (X ≃ Y)                                   

--------------------------------------------------------------------------------
-- Contractibility is closed under _×_ and _≃_ 

-- contractability is closed under _×_ 
open Chapters.`10.Exercises ; open 10-5
×-is-contr : is-contr A → is-contr B → is-contr (A × B)
×-is-contr = curry 10-5-i⇒ii 

--------------------------------------------------------------------------------
-- The next main result is that:
-- - is-equiv f is a prop, meaning
-- - we have (f , 

module _ (f : A → B) where 
  open ≃-Reasoning
--------------------------------------------------------------------------------
--   
  -- We will prove that, if f is an equivalence, then
  -- the sections/retractions of f are contractible. 
  -- The trick is to observe that the type (fib (f ∘_) id) is *almost*
  -- exactly what we need.
  --     is-contr (fib (f ∘_) id)
  --   ≡ is-contr (Σ[ g ∈ B → A ] (f ∘ g ≡ id))
  -- Unfortunately, fibers are w.r.t. equality and sections are w.r.t. homotopy:
  --   is-contr (section f) 
  -- ≡ is-contr (Σ[ g ∈ B → A ] (f ∘ g ∼ id))
  -- Fortunately, by functional extensionality, we have: 
  --   f ∘ g ≡ id ≃ f ∘ g ∼ id 
  fib-≃-section : fib (f ∘_) id ≃ section f 
  fib-≃-section = 
    fib (f ∘_) id                 ≃⟨ refl-≃ ⟩ 
    Σ[ g ∈ (B → A) ] (f ∘ g ≡ id) ≃⟨ ≃-distrib-Σ refl-≃ (λ g → eq-≃-htpy (f ∘ g) id) ⟩ 
    Σ[ g ∈ (B → A) ] (f ∘ g ∼ id) ≃⟨ refl-≃ ⟩
    section f ∎ 

  -- likewise, the fibers of precomposition are equivalent to retractions
  fib-≃-retraction : fib (_∘ f) id ≃ retraction f 
  fib-≃-retraction = 
    fib (_∘ f) id                 ≃⟨ refl-≃ ⟩ 
    Σ[ g ∈ (B → A) ] (g ∘ f ≡ id) ≃⟨ ≃-distrib-Σ refl-≃ (λ g → eq-≃-htpy (g ∘ f) id) ⟩ 
    Σ[ g ∈ (B → A) ] (g ∘ f ∼ id) ≃⟨ refl-≃ ⟩
    retraction f ∎ 

  -- Observe that f is an equivalence iff (f ∘_) is an equivalence.
  -- Since (f ∘_) is an equivalence, its fibers are contractible. Notably,
  -- we have 
  --   is-contr (fib (f ∘_) id)
  -- which we show above is equivalent to
  --  is-contr (section f). 
  section-is-contr : is-equiv f → is-contr (section f)
  section-is-contr eqv = ≃-is-contr fib-≃-section contr-fibers
    where 
      contr-fibers : is-contr (fib (f ∘_) id) 
      contr-fibers = is-equiv⇒is-contr-map (f ∘_) (post-composition-equiv f ._↔_.from eqv B) id


  retraction-is-contr : is-equiv f → is-contr (retraction f)
  retraction-is-contr eqv = ≃-is-contr fib-≃-retraction contr-fibers
    where 
      contr-fibers : is-contr (fib (_∘ f) id) 
      contr-fibers = is-equiv⇒is-contr-map (_∘ f) (is-equiv⇒Hom-equiv f eqv) id

  -- Being an equivalence is a prop.
  is-prop-is-equiv : is-prop (is-equiv f)
  is-prop-is-equiv = 
    (const⋆-embedding⇒is-prop ∘
      contractibleIfInhabited→const⋆-embedding {A = is-equiv f})
      ifInhabited 
    where
      ifInhabited : is-equiv f → is-contr (is-equiv f)
      ifInhabited eqv = ×-is-contr (section-is-contr eqv) (retraction-is-contr eqv) 

-- It immediately follows that is-equiv is a subtype of (A → B)
is-equiv-subtype : ⟨ is-equiv f ∣ f ∈ (A → B) ⟩ ⊆ (A → B) 
is-equiv-subtype = is-prop-is-equiv

≃-subtype : ⟨ is-equiv (fst e) ∣ e ∈ (A ≃ B) ⟩ ⊆ (A ≃ B)
≃-subtype = is-prop-is-equiv ∘ fst 

-- Because (is-equiv f) is a prop, it's sufficient to compare
-- just the maps of given equivalences.
eq-≃ : {e₁ e₂ : A ≃ B} → (fst e₁ ≡ fst e₂) → e₁ ≡ e₂ 
eq-≃ {e₁ = e₁} {e₂}  = fst-inj is-equiv-subtype

-- sym-≃ is involutive
sym-≃-involutive : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → sym-≃ ∘ (sym-≃ {A = A} {B = B}) ∼ id
sym-≃-involutive x = eq-≃ refl 

-- Which is needed to show the following 
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
  is-small A = ⟨ X ∈ 𝒰 ∣ A ≃ X ⟩

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
  -- bad : ∀ (A : Set ι) → ((X , _) : is-small A) → Set {! cong-≃ !}
  -- bad A (X , eq) = {!eq-equiv eq !}

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
          (≃-distrib-Σ refl-≃ (λ Y → cong-≃ (sym-≃ e) refl-≃)) 
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

  module 𝒱-inclusion₁ where 
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
            (𝒾 X ≃ A) ≃⟨ cong-≃ (sym-≃ (𝒾-eqv X)) refl-≃ ⟩ 
            (X ≃ A)   ≃⟨ sym-≃² ⟩
            (A ≃ X) ∎
            where 
              open ≃-Reasoning
      
      --  Equivalent types are the same k-types; since (is-small A) is a prop (proven above),
      -- we know that fib 𝒾 A is a prop.
      𝒾-prop-fibers : (A : 𝒱) → is-prop (fib 𝒾 A) 
      𝒾-prop-fibers A = ≃-is-prop (sym-≃ (fib≃is-small A)) (is-small-prop A) 
      
      -- Having propositional fibers is equivalent to being an embedding,
      -- completing the proof.
      𝒾-emb : is-emb 𝒾 
      𝒾-emb = prop-fibers⇒is-emb 𝒾 𝒾-prop-fibers  

  --------------------------------------------------------------------------------
  -- The only aspect of "intensional cumulativity" we really needed was
  -- that 𝒾 X ≃ X, so let's just generalize that. 

  module 𝒱-inclusion₂ 
    {ι} 
    (𝒾 : 𝒰 → Set ι) 
    (𝒾-eqv : (X : 𝒰) → X ≃ 𝒾 X) where 

    𝒱 = Set ι

    fib≃is-small : (A : 𝒱) → fib 𝒾 A ≃ is-small A
    fib≃is-small A = ≃-distrib-Σ refl-≃ (λ X → 
       (𝒾 X ≡ A)    ≃⟨ univ (𝒾 X) A ⟩ 
       (𝒾 X ≃ A) ≃⟨ cong-≃ (sym-≃ (𝒾-eqv X)) refl-≃ ⟩ 
       (X ≃ A)   ≃⟨ sym-≃² ⟩
       (A ≃ X) ∎)
      where   
        open ≃-Reasoning
    
    --  Equivalent types are the same k-types; since (is-small A) is a prop (proven above),
    -- we know that fib 𝒾 A is a prop.
    𝒾-prop-fibers : (A : 𝒱) → is-prop (fib 𝒾 A) 
    𝒾-prop-fibers A = ≃-is-prop (sym-≃ (fib≃is-small A)) (is-small-prop A) 
    
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
  -- 

  module _ (P : 𝒰 → Set ℓ) 
           (prop-P : ∀ (X : 𝒰) → is-prop (P X)) where

    equiv-eq′ : {A  B : ⟨ X ∈ 𝒰 ∣ (P X) ⟩}  → A ≡ B → fst A ≃ fst B 
    equiv-eq′ = equiv-eq ∘ ap fst   

    -- AH> Rijke defines equiv-eq′(refl) := refl-≃.
    --     Either def'n will do! But defining it as above 
    --     makes the proof more straightforward.
    _ : ∀ {A  : ⟨ X ∈ 𝒰 ∣ (P X) ⟩} → 
          equiv-eq′ {A = A} refl ≡ refl-≃ 
    _ = refl 

    eq′-equiv : {A  B : ⟨ X ∈ 𝒰 ∣ (P X) ⟩} → fst A ≃ fst B → A ≡ B 
    eq′-equiv = fst-inj prop-P ∘ eq-equiv 
    
    fst-≃ : {A  B : ⟨ X ∈ 𝒰 ∣ (P X) ⟩} → is-equiv (equiv-eq′ {A = A} {B})
    fst-≃ {A = A} {B} = univalence ∘ₑ (fst-emb prop-P A B)

--------------------------------------------------------------------------------
-- Theorem 17.2.3 (Propositional Extensionality): 
-- the canonical map
--   iff-eq : P ≡ Q → (P ↔ Q) 
-- is an equivalence.

  module _ (P Q : 𝒰) 
           (prop-P : is-prop P) 
           (prop-Q : is-prop Q)  where 
    open _↔_
    iff-eq : P ≡ Q → P ↔ Q 
    iff-eq refl = (id , id) 

    ↔-prop : is-prop (P ↔ Q) 
    ↔-prop = {! propositionalEquivalence    !} -- Irrelevant⇒is-prop λ { (to₁ , from₁) (to₂ , from₂) → {!   !}  }

    iff-eq-eqv : is-equiv iff-eq 
    iff-eq-eqv = tr is-equiv same (chain .snd)
      where 
        open ≃-Reasoning 
        chain : (P ≡ Q) ≃ (P ↔ Q)
        chain = 
          P ≡ Q ≃⟨ univ P Q ⟩ 
          (P ≃ Q) ≃⟨ propositionalEquivalence (≃-prop prop-P prop-Q) ↔-prop .from (propositionalEquivalence prop-P prop-Q) ⟩ 
          (P ↔ Q) ∎ 
        
        

        same : chain .fst ≡ iff-eq 
        same = fun-ext (chain .fst) iff-eq (λ { refl → refl }) 
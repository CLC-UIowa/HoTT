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

    EquivInduction : Set _
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
    -- AH> We are also postulating that all universes
    --     (Set ℓ), for any ℓ, are *univalent*.
    univalence : Univalence {ℓ} 

  -- The juicy bit
  eq-equiv : ∀ {A B : 𝒰} → A ≃ B → A ≡ B
  eq-equiv = `sec univalence  

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

  -- AH> N.b. this will be problematic with univalence.
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
  bad : ∀ (A : Set ι) → ((X , _) : is-small A) → Set {!!}
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
  -- of Thm 1.1.6.
  ≃-distrib-Σ : ∀ {A₁ : Set ℓ₁} {A₂ : Set ℓ₂}
                  {B₁ : A₁ → Set ι₁} {B₂ : A₂ → Set ι₂} →
                  ((f , e) : A₁ ≃ A₂) → 
                  ((x : A₁) → B₁ x ≃ B₂ (f x)) → 
                  Σ A₁ B₁ ≃ Σ A₂ B₂ 
  ≃-distrib-Σ = {!!} 

  -- We're learning that we haven't really catalogued a number of 
  -- congruences over _≃_. Above, we need congruence over Σ; 
  -- Here, we need congruence over _≃_.
  -- Note that univalence is restricted to specific *universes*:
  -- We **cannot** simply prove this via
  --   ap (_≃ Y) ∘ eq-equiv 
  -- because A and B are not in the same universe.
  -- 
  -- Proofs are left as exercise to the reader. (Apoorv?)
  ≃-distribₗ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {Y : Set ι} → 
                 A ≃ B → (A ≃ Y) ≃ (B ≃ Y)
  ≃-distribₗ e = {!!}                                   

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


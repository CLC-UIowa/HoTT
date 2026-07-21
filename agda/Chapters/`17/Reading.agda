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
  is-small : Set ι → Set _
  is-small A = Σ[ X ∈ 𝒰 ] (A ≃ X)

  -- Similarly, a map f : A → B is said to be 𝒰-small
  -- if all of its fibers are 𝒰-small.
  is-small-map : ∀ {A : Set ι₁} {B : Set ι₂} → 
                   (f : A → B) → Set _
  is-small-map {B = B} f = ∀ (b : B) → is-small (fib f b)

  --------------------------------------------------------------------------------
  -- Example 17.1.4
  -- AH> Here Rijke claims some examples, which we'll prove.

  -- (1) Any type in 𝒰 is 𝒰-small.
  all-𝒰 : (A : 𝒰) → is-small A
  all-𝒰 A = A , refl-≃

  -- (ii) Any contractible type is 𝒰-small with respect to any universe 𝒰
  contractible-small : ∀ (A : Set ι) → is-contr A → is-small A
  contractible-small A contr = {!!} 



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
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ 
    𝐁 : A → Set ℓ

--------------------------------------------------------------------------------
-- Ch. 17 The Univalence Axiom
  
--------------------------------------------------------------------------------
-- §17.1 Equivalence forms of the Univalence Axiom 
-- AH> I will first characterize each equivalent form. That they are equivalent
--     follows form the fundamental theorem of identity types.

module _ {ℓ} where
  𝒰 = Set ℓ 
  𝒰₁ = Set (lsuc ℓ)

  equiv-eq : ∀ {A B : 𝒰} → A ≡ B → A ≃ B
  equiv-eq refl = refl-≃

  -- Formulation (i): 𝒰 is univalent if equiv-eq is an equivalence.
  Univalence : 𝒰₁
  Univalence = ∀ {A B : 𝒰} → is-equiv (equiv-eq {A = A} {B})

  -- Formulation (ii)
  EquivContractible : 𝒰₁
  EquivContractible = (A : 𝒰) → Σ[ B ∈ 𝒰 ] (A ≃ B)

  -- Formulation (iii)
  module _ (A : 𝒰) (P : (X : 𝒰) → A ≃ X → 𝒰) where
    equiv-eval : ((X : 𝒰) (e : A ≃ X) → P X e) → 
                 P A refl-≃  
    equiv-eval f = f A refl-≃

    EquivInduction : Set _
    EquivInduction = section equiv-eval

  -- That these three are equivalent follows from the fundamental theorem of identity types
  module _ {A : 𝒰} (pf : IdFundProof {𝐁 = A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B})) where
    univalence-forms : IdFund {A = 𝒰} {A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B}) 
    univalence-forms = fund-thm-id A refl-≃ (λ B → equiv-eq {A = A} {B}) pf 
  


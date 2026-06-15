module Chapters.`13.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises
open import Chapters.`12.Reading

open import Function
--------------------------------------------------------------------------------
-- 13.1 Equivalent forms of function extensionality

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ 
    𝐁 : A → Set ℓ

----------------------------------------
-- Proposition 13.1.1

-- We've three equivalent characterizations of the function extensionality principle.
-- AH> N.b. Rijke chooses to treat f as a module parameter, which is equivalent. I
--     prefer letting f and g both be components of the definition.
module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {𝐁 : A → Set ℓ₂} where

  htpy-eq : (f : (x : A) → 𝐁 x) (g : (x : A) → 𝐁 x) → f ≡ g → f ∼ g 
  htpy-eq f g refl = refl-∼ 
 
  -- ------------------------------
  -- 1. The *function extensionality principle* 
  -- asserts that the function htpy-eq f g is an equivalence for any g.
  FunctionExtensionality : Set _
  FunctionExtensionality = ∀ (f : (x : A) → 𝐁 x) (g : (x : A) → 𝐁 x) → is-equiv (htpy-eq f g)

  -- ------------------------------
  -- 2. The total space Σ[ g ∈ ((x : A) → 𝐁 x) ] is contractible
  HtpyContractible : (f g : (x : A) → 𝐁 x) → Set _
  HtpyContractible f g = is-contr (Σ[ g ∈ ((x : A) → 𝐁 x) ] (f ∼ g))

  -- ------------------------------
  -- 3. The principle of *homotopy induction*: 
  -- the function htpy-eval has a section. 
  --    AH> I'd like to unpack this nonsense a bit...
  --        First: "has a section" ≡ "is a retraction".
  --        A section, let's call it htpy-ind, for htpy-eval would have the type:
  --          htpy-ind : P f refl-∼ → (g : (x : A) → 𝐁 x) → (H : f ∼ g) → P g H
  --        which resembles an induction principle: show that P holds for the
  --        base case (refl-∼) and it holds for the general case.
  --        That this is a section means
  --          htpy-eval ∘ htpy-ind ∼ id 
  module _ {ℓ} (f : (x : A) → 𝐁 x) (P : (g : (x : A) → 𝐁 x) → f ∼ g → Set ℓ) where
    htpy-eval : ((g : (x : A) → 𝐁 x) → (H : f ∼ g) → P g H) → 
               P f refl-∼
    htpy-eval s = s f Refl    

    HtpyInduction : Set _
    HtpyInduction = section htpy-eval

-- data FunExtProof {ℓ} : Set ℓ where 

--   function-extensionality : ∀ (f : (x : A) → 𝐁 x) → FunctionExtensionality f → FunExtProof



----------------------------------------
-- Theorem 13.1.2


----------------------------------------
-- Axiom 13.1.3 (Function Extensionality)
-- and Proof of 13.1.1

postulate
  Fun-Ext : FunctionExtensionality {A = A} {𝐁 = 𝐁}

-- AH> The straightforward use of this axiom
fun-ext : (f g : (x : A) → 𝐁 x)  → (f ∼ g) → f ≡ g
fun-ext f g = `sec (Fun-Ext f g)  

-- We bundle the equivalent forms of functional extensionality
-- by invoking the fundamental theorem of identity types.
fun-ext-proof : (f : (x : A) → 𝐁 x) → IdFundProof f refl-∼ (htpy-eq f) 
fun-ext-proof f = familyEquivalence (Fun-Ext f)

-- All forms
fun-ext-forms : (f : (x : A) → 𝐁 x) → IdFund f refl-∼ (htpy-eq f)
fun-ext-forms f = fund-thm-id f refl-∼ (htpy-eq f) (fun-ext-proof f) 

-- (ii) The total space Σ[ g ∈ (x : A) → 𝐁 x ] (f ∼ g) is contractible.
fun-ext-HtpyContractible : ∀ (f g : (x : A) → 𝐁 x) → HtpyContractible f g
fun-ext-HtpyContractible f g = fun-ext-forms f .space-contractible 


-- (iii) The principle of homotopy induction
-- AH> Good luck proving this! It's "true" in the text, but
--     I suspect differences between the formalization of an "identity system"
--     and my def'n of HtpyInduction are mechanically incongruent.
--     Problems arise in that the inductive-hypothesis provided by the identity
--     system is not strong (that is, generalized) enough to prove HptyInduction f P.
fun-ext-induction : ∀ {ℓ} {A : Set ℓ} {𝐁 : A → Set ℓ} → 
                    (f : (x : A) → 𝐁 x) (P : (g : (x : A) → 𝐁 x) → f ∼ g → Set ℓ) → 
                    HtpyInduction f P 
fun-ext-induction f P = fun-ext-forms f .id-system P

           
----------------------------------------
-- ¬ P is a prop for any type P. (Requires functional extensionality, as we
--  have to prove f ≡ g for f , g : P → ⊥.
¬P-prop : ∀ (P : Set ℓ) → is-prop (¬ P)
¬P-prop P f g = 
  Irrelevant⇒is-prop (λ f g → fun-ext f g (λ p → ⊥-elim (f p)) ) f g

----------------------------------------
-- Thm 13.2.1 (Axiom of choice)

module _ (C : (x : A) → 𝐁 x → Set ℓ) where 
  choice : ((x : A) → (Σ[ y ∈ 𝐁 x ] (C x y))) →  
           Σ[ f ∈ ((x : A) → 𝐁 x) ] ((x : A) → C x (f x))
  choice h = fst ∘ h , snd ∘ h

  choice⁻¹ : (Σ[ f ∈ ((x : A) → 𝐁 x) ] ((x : A) → C x (f x))) → 
             (x : A) → (Σ[ y ∈ 𝐁 x ] (C x y))
  choice⁻¹ (f , h) =  < f , h >

  choice-equiv : is-equiv choice
  choice-equiv = has-inverse⇒is-equiv (choice⁻¹ , refl-∼ , refl-∼)
           

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
-- AH> The proof of equivalence folloes from the fundamental theorem of identity types,
--     which I'd still like to clean up to be more reusable. I'm not a fan of these
--     large implication chain theorems, as they're difficult to name and reuse.
module _ (f : (x : A) → 𝐁 x) where

  htpy-eq : (g : (x : A) → 𝐁 x) → f ≡ g → f ∼ g 
  htpy-eq g refl = refl-∼ 
 
  -- ------------------------------
  -- 1. The *function extensionality principle* 
  -- asserts that the function htpy-eq g is an equivalence for any g.
  FunctionExtensionality : Set _
  FunctionExtensionality = ∀ (g : (x : A) → 𝐁 x) → is-equiv (htpy-eq g)

  -- AH> How you would actually use this axiom
  fun-ext : FunctionExtensionality → (g : (x : A) → 𝐁 x) → (f ∼ g) → f ≡ g
  fun-ext fn g = `sec (fn g)  

  -- ------------------------------
  -- 2. The total space Σ[ g ∈ ((x : A) → 𝐁 x) ] is contractible
  HtpyContractible : Set _
  HtpyContractible = is-contr (Σ[ g ∈ ((x : A) → 𝐁 x) ] (f ∼ g))

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
  --        I'm not sure the significance we gain from this added identity...
  --        To me, it feels sufficient to have simply asked that we have
  --        the witness htpy-ind?
  module _ {ℓ} (P : (g : (x : A) → 𝐁 x) → f ∼ g → Set ℓ) where
    htpy-eval : ((g : (x : A) → 𝐁 x) → (H : f ∼ g) → P g H) → 
               P f refl-∼
    htpy-eval s = s f refl-∼ 

    HtpyInduction : Set _
    HtpyInduction = retraction htpy-eval

  -- It follows from the fundamental theorem of identity types that these three
  -- characterizations are equivalent.
  -- TODO: Refactor said theorem to be used here.


----------------------------------------
-- Theorem 13.1.2


----------------------------------------
-- Axiom 13.1.3 (Function Extensionality)

postulate
  Fun-Ext : ∀ (f : (x : A) → 𝐁 x) → FunctionExtensionality f

-- ¬ P is a prop for any type P. (Requires functional extensionality, as we
--  have to prove f ≡ g for f , g : P → ⊥.
¬P-prop : ∀ (P : Set ℓ) → is-prop (¬ P)
¬P-prop P f g = Irrelevant⇒is-prop 
  (λ f g → fun-ext f (Fun-Ext f) g (λ p → ⊥-elim (f p) )) f g

----------------------------------------
-- Thm 13.2.1

module _ (C : (x : A) → 𝐁 x → Set ℓ) where 
  choice : ((x : A) → (Σ[ y ∈ 𝐁 x ] (C x y))) →  
           Σ[ f ∈ ((x : A) → 𝐁 x) ] ((x : A) → C x (f x))
  choice h = (fst ∘ h) , (snd ∘ h)

  choice⁻¹ : (Σ[ f ∈ ((x : A) → 𝐁 x) ] ((x : A) → C x (f x))) → 
             (x : A) → (Σ[ y ∈ 𝐁 x ] (C x y))
  choice⁻¹ (f , h) x  = (f x) , (h x)    

  choice-equiv : is-equiv choice
  choice-equiv = has-inverse⇒is-equiv (choice⁻¹ , refl-∼ , refl-∼)
           

{-# OPTIONS --allow-unsolved-metas #-} 
module Prelude.Paths where 

open import Prelude.Base public 
open GVars 

--------------------------------------------------------------------------------
-- Cubical Agda
-- 
-- We will be using the standard cubical agda library. 
--   - https://github.com/agda/cubical
--   - https://agda.readthedocs.io/en/latest/language/cubical.html

open import Cubical.Foundations.Prelude 
  renaming (I to 𝕀 ; i0 to i₀ ; i1 to i₁) 
  hiding (module Σ ; Σ-syntax ; Σ) public
open import Cubical.Foundations.Univalence public 
open import Cubical.Foundations.Equiv public 
open import Cubical.Foundations.Isomorphism public 

{- -----------------------------------------------------------------------------
# Definitions and notation from Rijke 

Some definitions we have grown accustomed to are not in the Cubical library,
and so will have to be redefined with respect to path equality.

----------------------------------------------------------------------------- -}
-- ap and transport, other notations

module _ where 
  private 
    variable
      x y z w : A

  infixr 30 _⁻¹
  _⁻¹ : x ≡ y → y ≡ x
  _⁻¹ = sym 

  infixr 29 _○_
  _○_ : x ≡ y → y ≡ z → x ≡ z 
  (p ○ q) = refl ∙∙ p ∙∙ q

  ap : {B : A → Set ℓ} (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
  ap = cong 

  -- Star notation for mapping 
  _·_ : (f : A → B) → x ≡ y → f x ≡ f y
  _·_ = ap

  tr : (P : A → Set ℓ) → x ≡ y → P x → P y
  tr P e = transp (λ i → P (e i)) i₀ 
 
  -- transports 
  -- syntactic sugar for transports (\tb2)
  infixr 5 _▸_ 
  _▸_ : A ≡ B → A → B
  p ▸ x = tr _ p x 

  coerce : A ≡ B → A → B 
  coerce = _▸_

  -- Transport with explicit motive 
  infixr 5 _⟨_⟩▸_
  _⟨_⟩▸_ :  ∀ (P : A → Set ℓ) → x ≡ y → P x → P y
  _⟨_⟩▸_ = tr

--------------------------------------------------------------------------------
-- Homotopies 

infixr 5 _∼_
_∼_ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → ((x : A) → B x) → ((x : A) → B x) → Set _
_∼_ {A = A} f g = (x : A) → f x ≡ g x

--------------------------------------------------------------------------------
-- Decidability 

data Dec (A : Set ℓ) : Set ℓ where 
  yes : (p : A)   → Dec A 
  no  : (q : ¬ A) → Dec A 

-- squashing 
∣_∣  : Dec A → Set
∣ yes _ ∣ = ⊤ 
∣ no  _ ∣ = ⊥

Discrete : Set ℓ → Set ℓ 
Discrete A = (x y : A) → Dec (x ≡ y) 

module _ {A : Set ℓ} (D : Discrete A)  where

  -- Collapse every path to that produced by D 
  collapse : (x y : A) → x ≡ y → x ≡ y 
  collapse x y p with D x y
  ... | yes p = p 
  ... | no  q = ⊥-elim (q p)

  collapse-const : {x y : A} (p q : x ≡ y) → 
                  collapse x y p ≡ collapse x y q 
  collapse-const {x = x} {y} p q with D x y 
  ... | yes p = refl                   
  ... | no q = refl 


  -- The proof is:
  -- Start with 
  --   r ≡ refl ⁻¹ ○ r?
  Hedberg : {x y : A} → (r : x ≡ y) → 
            r ≡ collapse x x refl ⁻¹ ○ collapse x y r
  Hedberg {x = x} {y} r = {! _⋆_  !} 

  Discrete⇒isSet : isSet A 
  Discrete⇒isSet x y p q = 
    p 
      ≡⟨ Hedberg p ⟩ 
    collapse x x refl ⁻¹ ○ collapse x y p 
      ≡⟨ ap (λ e → collapse x x refl ⁻¹ ○ e) (collapse-const p q) ⟩ 
    collapse x x refl ⁻¹ ○ collapse x y q 
      ≡⟨ Hedberg q ⁻¹ ⟩ 
    q ∎ 
      
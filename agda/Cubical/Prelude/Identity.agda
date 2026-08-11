module Prelude.Identity where

open import Prelude.Base public 

--------------------------------------------------------------------------------
-- # The propositional identity type

open import Relation.Binary using (IsEquivalence) public 
open import Relation.Binary.PropositionalEquality
    using (_≡_ ; trans ; sym ; refl ; module ≡-Reasoning ; cong) public 
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Relation.Nullary using (¬_) public  


-----------------------------------------------------------------------------
-- Syntax for groupoids



record GroupoidSyntax {ℓ₁} {ℓ₂} {A : Set ℓ₁} (_≈_ : A → A → Set ℓ₂)  : Set (ℓ₁ ⊔ lsuc ℓ₂)  where
  infixl 30 _⁻¹
  infixl 25 _○_
  field
    Refl : {x : A} →  x ≈ x
    _⁻¹ : {x y : A} → x ≈ y → y ≈ x
    _○_ : {x y z : A} → x ≈ y → y ≈ z → x ≈ z

    -- The type of paths between paths. This abstraction is
    -- unfortunately necessary if we want to also
    -- abstract over groupoid properties.
    _~_ : ∀ {x y : A} → x ≈ y → x ≈ y → Set ℓ₂
    eqv : ∀ {x y} → IsEquivalence (_~_ {x} {y})

    -- Congruence
    _⋆_ : ∀ {x y z : A} {p h : x ≈ y} {q k : y ≈ z} →
          (H : p ~ h) → (K : q ~ k) →
          p ○ q ~ h ○ k

    -- properties
    left-inv : ∀ {x y : A} (p : x ≈ y) → p ⁻¹ ○ p ~ Refl
    right-inv : ∀ {x y : A} (p : x ≈ y) → p ○ p ⁻¹ ~ Refl
    involution : ∀ {x y : A} (p : x ≈ y) → (p ⁻¹) ⁻¹ ~ p
    left-identity : {x y : A} (p : x ≈ y) → Refl ○ p ~ p
    right-identity : {x y : A} (p : x ≈ y) → p ○ Refl ~ p
    assoc : {x y z w : A} → (p : x ≈ y) → (q : y ≈ z) → (r : z ≈ w) → (p ○ q) ○ r ~ p ○ (q ○ r)

  -- -- left congruence
  _⋆ₗ_ : ∀ {x y z : A} {p h : x ≈ y} →
          (H : p ~ h) (q : y ≈ z) →
          p ○ q ~ h ○ q
  H ⋆ₗ q = H ⋆ refl-~
    where
      open IsEquivalence eqv renaming (refl to refl-~)

  _⋆ᵣ_ : ∀ {x y z : A} {q h : y ≈ z} →
          (p : x ≈ y) (H : q ~ h)  →
          p ○ q ~ p ○ h
  p ⋆ᵣ H = refl-~ ⋆ H
    where
      open IsEquivalence eqv renaming (refl to refl-~)

open GroupoidSyntax {{...}} public

-----------------------------------------------------------------------------
-- The identity type (ported from Part 1)

module Paths where
  private
    variable
      ℓ ℓ₁ ℓ₂ : Level
      A B : Set ℓ
      x y z w : A

  -- based path induction
  ind≡ : (a : A) →
         (P : (x : A) → a ≡ x → Set ℓ) →
         P a refl → (x : A) → (p : a ≡ x) →
         P x p
  ind≡ _ _ p _ refl = p

  -- The MLTT J eliminator (equivalent to based path induction)
  J : ∀ (C : (x y : A) → x ≡ y → Set ℓ) →
        (∀ (x : A) → C x x refl) →
        (x y : A) (p : x ≡ y) →
        C x y p
  J C pf x = ind≡ x (C x) (pf x)

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl
  
  ap-app : {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x 
  ap-app e x = ap (λ h → h x) e 

  ap₂ : {C : Set ℓ} → (f : A → B → C) → {x y : A} {a b : B} → x ≡ y → a ≡ b → f x a ≡ f y b 
  ap₂ f refl refl = refl 

  ap-id : (p : x ≡ y) → p ≡ ap id p
  ap-id refl = refl

  ap-comp : {C : Set ℓ} (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) → ap g (ap f p) ≡ ap (g ∘ f) p
  ap-comp f g refl = refl

  tr : (B : A → Set ℓ) → x ≡ y → B x → B y
  tr B refl b = b

  apd : {B : A → Set ℓ} (f : (x : A) → B x) (p : x ≡ y) → tr B p (f x) ≡ f y
  apd f refl = refl
  
  -----------------------------------------------------------------------------
  -- Some helpful syntax

  -- Mapping f 
  infixr 5 _*
  _* : (f : A → B) → x ≡ y → f x ≡ f y
  f * = ap f 

  -- transports 
  -- syntactic sugar for transports (\tb2)
  infixr 5 _▸_ 
  _▸_ : ∀ {P : A → Set ℓ} → x ≡ y → P x → P y
  p ▸ x = tr _ p x 

  -- With explicit motive 
  infixr 5 _⟨_⟩▸_
  _⟨_⟩▸_ :  ∀ (P : A → Set ℓ) → x ≡ y → P x → P y
  _⟨_⟩▸_ = tr

  -------------------------------------------------------------------------------
  -- The groupoidal structure of types

  -- _≡_ is an equivalence relation
  ≡-equiv : IsEquivalence (_≡_ {A = A})
  ≡-equiv = record { refl = refl ; sym = sym ; trans = trans }

  instance
    PathGroupoid : GroupoidSyntax {A = A} (_≡_)
    PathGroupoid = record
      { Refl = refl ;
        _⁻¹ = sym ;
        _○_ = trans ;
        _~_ = _≡_ ;
        eqv = ≡-equiv ;
        _⋆_ = λ { refl refl → refl } ;
        left-inv = λ { refl → refl } ;
        right-inv = λ { refl → refl } ;
        involution = λ { refl → refl } ;
        left-identity = λ { refl → refl } ;
        right-identity = λ { refl → refl } ;
        assoc = λ { refl refl refl → refl } }

open Paths public


--------------------------------------------------------------------------------
-- Some laws about transport. (Lemma 2.11.2 in HoTT book).

module _ {ℓ} {A : Set ℓ} (a x₁ x₂ : A) where
  post-comp-law : (p : x₁ ≡ x₂) (q : a ≡ x₁) → tr (λ x → a ≡ x) p q ≡ q ○ p
  post-comp-law refl q = (right-identity q) ⁻¹
  
  pre-comp-law : (p : x₁ ≡ x₂) (q : x₁ ≡ a) → tr (λ x → x ≡ a) p q ≡ p ⁻¹ ○ q
  pre-comp-law refl q = refl

  refl-law : (p : x₁ ≡ x₂) (q : x₁ ≡ x₁) → tr (λ x → x ≡ x) p q ≡ p ⁻¹ ○ q ○ p 
  refl-law refl q = (right-identity q) ⁻¹ 

-----------------------------------------------------------------------------
-- Pointwise equivalence of functions (homotopy equivalence)

module Homotopies where
  open import Relation.Binary using (IsEquivalence ; Setoid) public
  private
    variable
      ℓ ℓ₁ ℓ₂ ℓ₃ : Level
      A B C D : Set ℓ
      𝐁 𝐂 𝐃 : A → Set ℓ
      f g h i : (x : A) → 𝐁 x

  -- Definition 9.1.2
  infix 4 _∼_
  _∼_ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → ((x : A) → B x) → ((x : A) → B x) → Set _
  _∼_ {A = A} f g = (x : A) → f x ≡ g x

  -- Definition 9.1.5

  refl-∼ : {f : (x : A) → 𝐁 x} → f ∼ f
  refl-∼ _ = refl

  sym-∼ : f ∼ g → g ∼ f
  sym-∼ f∼g = sym ∘ f∼g

  trans-∼ : f ∼ g → g ∼ h → f ∼ h
  trans-∼ f∼g g∼h x = (f∼g x) ○ (g∼h x)


  -- _∼_ is an equivalence relation
  ∼-equiv : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → IsEquivalence (_∼_ {A = A} {B = B})
  ∼-equiv = record { refl = refl-∼ ; sym = sym-∼ ; trans = trans-∼ }


  -- ((x : A) → B x , _∼_) is a setoid on any type A and family B.
  ∼-setoid : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → Setoid (ℓ₁ ⊔ ℓ₂) _
  ∼-setoid {A = A} {B} .Setoid.Carrier = (x : A) → B x
  ∼-setoid {A = A} {B} .Setoid._≈_ = _∼_ {A = A} {B = B}
  ∼-setoid .Setoid.isEquivalence = ∼-equiv

  instance
    HtpyGroupoid : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → GroupoidSyntax {A = (x : A) → B x} (_∼_)
    HtpyGroupoid = record {
      Refl = refl-∼ ;
      _⁻¹ = sym-∼ ;
      _○_ = trans-∼ ;
      _~_ = _∼_ ;
      eqv = ∼-equiv ;
      _⋆_ = λ p∼h q∼k x → _⋆_ {{PathGroupoid}} (p∼h x) (q∼k x) ;
      left-inv = λ H → left-inv {{PathGroupoid}} ∘ H ;
      right-inv = λ H → right-inv {{PathGroupoid}} ∘ H ;
      involution = λ p x → involution {{PathGroupoid}} (p x) ;
      left-identity = λ _ _ → refl  ;
      right-identity = λ H → right-identity {{PathGroupoid}} ∘ H ;
      assoc = λ { H K L x → assoc {{PathGroupoid}} (H x) (K x) (L x) }
      }

  transport-fusion : ∀ {ℓ₁ ℓ₂} { A : Set ℓ₁} {B : A → Set ℓ₂} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) →
                     tr B (p ○ q) ∼ (tr B q) ∘ (tr B p)
  transport-fusion refl refl = refl-∼

  -- replace a transport equality with an equal one
  tr-tr : ∀ {ℓ₁ ℓ₂} { A : Set ℓ₁} {B : A → Set ℓ₂} {x y : A} {t : B x} → 
          (p q : x ≡ y) → 
          (p ≡ q) → tr B p t ≡ tr B q t
  tr-tr p q refl = refl 

  -- Composing transport with ap
  tr-ap : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {P : B → Set ℓ₃} {x y : A} → (f : A → B) → (p : x ≡ y) → 
            tr P (ap f p) ∼ tr (P ∘ f) p
  tr-ap f refl = Refl 


  -- -- Definition 9.1.7

  -- Left whiskering
  infixl 25 _·ₗ_
  _·ₗ_ : (h : B → C) → (H : f ∼ g) → (h ∘ f) ∼ (h ∘ g)
  h ·ₗ H = ap h ∘ H

  -- Right whiskering
  infixl 25 _·ᵣ_
  _·ᵣ_ : (H : g ∼ h) → (f : A → B) → (g ∘ f) ∼ (h ∘ f)
  H ·ᵣ f = H ∘ f

open Homotopies public

-----------------------------------------------------------------------------
-- Reasoning syntax over _≡_

module PathReasoning where
  -- Open reasoning syntax over _≡_. Usage:
  -- f : foo ≡ bar
  -- f = begin
  --   foo ≡⟨ ? ⟩
  --   ...
  --   ?   ≡⟨ ? ⟩
  --   bar ∎
  open ≡-Reasoning public

-----------------------------------------------------------------------------
-- Reasoning syntax over _∼_

module HomReasoning {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} where
  -- Open setoid reasoning syntax with carriers A and B. Usage:
  -- f : foo ∼ bar
  -- f = begin
  --   foo ∼⟨ ? ⟩
  --   ...
  --   ?   ∼⟨ ? ⟩
  --   bar ∎
  open Homotopies
  open import Relation.Binary.Reasoning.Base.Single (_∼_ {A = A} {B = B})
    refl-∼
    trans-∼ public

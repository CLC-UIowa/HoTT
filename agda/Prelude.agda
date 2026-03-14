module Prelude where

open import Agda.Primitive public

open import Data.Bool using (true ; false ; Bool ; not) public
open import Data.Product
    renaming (proj₁ to fst ; proj₂ to snd)
    using (_×_ ; Σ ; Σ-syntax ; ∃ ; ∃-syntax ; _,_) public
open import Data.Sum
    using (inj₁ ; inj₂ ; [_,_])
    renaming (_⊎_ to _+_) public
open import Data.Unit using (⊤ ; tt) public
open import Data.Empty using (⊥ ; ⊥-elim) public
open import Data.Fin
  using (Fin ; fromℕ)
  renaming (zero to fzero ; suc to fsuc) public
open import Data.Nat using (ℕ ; suc ; zero) public

open import Function hiding (_↔_) public

open import Relation.Binary.PropositionalEquality
    using (_≡_ ; trans ; sym ; refl ; module ≡-Reasoning ; cong) public
open import Relation.Nullary using (¬_) public

open import Data.String using (String)

-----------------------------------------------------------------------------
-- Bi-implication
-- (the std. library defines _↔_ instead as isomorphism.)

record _↔_ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    to : A → B
    from : B → A

-----------------------------------------------------------------------------
-- Syntax for groupoids 



record GroupoidSyntax {ℓ} {A : Set ℓ} (_≈_ : A → A → Set ℓ)  : Set (lsuc ℓ)  where 
  infixl 30 _⁻¹
  infixl 25 _○_  
  field 
    Refl : {x : A} →  x ≈ x 
    _⁻¹ : {x y : A} → x ≈ y → y ≈ x 
    _○_ : {x y z : A} → x ≈ y → y ≈ z → x ≈ z
  -- todo: add properties

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

  instance 
    PathGroupoid : GroupoidSyntax {A = A} (_≡_)
    PathGroupoid = record { Refl = refl ; _⁻¹ = sym ; _○_ = trans } 

  ap : (f : A → B) → x ≡ y → f x ≡ f y
  ap f refl = refl 

  ap-id : (p : x ≡ y) → p ≡ ap id p
  ap-id refl = refl

  tr : (B : A → Set ℓ) → x ≡ y → B x → B y
  tr B refl b = b

  apd : {B : A → Set ℓ} (f : (x : A) → B x) (p : x ≡ y) → tr B p (f x) ≡ f y
  apd f refl = refl

  -------------------------------------------------------------------------------
  -- The groupoidal structure of types

  left-inv : {A : Set ℓ} {x y : A} (p : x ≡ y) → p ⁻¹ ○ p ≡ refl
  left-inv {x = x} {y} refl = refl

  right-inv : {A : Set ℓ} {x y : A} (p : x ≡ y) → p ○ p ⁻¹ ≡ refl
  right-inv {x = x} {y} refl = refl

  involution : {A : Set ℓ} {x y : A} (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
  involution {x = x} {y} refl = refl

  left-identity : {A : Set ℓ} {x y : A} (p : x ≡ y) → refl ○ p ≡ p
  left-identity {x = x} {y}  refl = refl

  right-identity : {A : Set ℓ} {x y : A} (p : x ≡ y) → p ○ refl ≡ p
  right-identity {x = x} {y} refl = refl

  assoc : {A : Set ℓ} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → (p ○ q) ○ r ≡ p ○ (q ○ r)
  assoc refl refl refl = refl

open Paths public

-----------------------------------------------------------------------------
-- Pointwise equivalence of functions (homotopy equivalence)

module Homotopies where
  open import Relation.Binary using (IsEquivalence ; Setoid) public
  private
    variable
      ℓ ℓ₁ ℓ₂ ℓ₃ : Level
      A : Set ℓ
      B : A → Set ℓ

  -- Definition 9.1.2
  infix 4 _∼_
  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Set _
  _∼_ {A = A} f g = (x : A) → f x ≡ g x

  -- Definition 9.1.5

  refl-∼ : {f : (x : A) → B x} → f ∼ f
  refl-∼ _ = refl
  
  private
    variable
      f g h : (x : A) → B x

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
    HtpyGroupoid : GroupoidSyntax {A = (x : A) → B x} (_∼_)
    HtpyGroupoid = record { Refl = refl-∼ ; _⁻¹ = sym-∼ ; _○_ = trans-∼ } 

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

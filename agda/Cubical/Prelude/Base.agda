module Prelude.Base where

open import Agda.Primitive public

open import Data.Bool using (true ; false ; Bool ; not) public
open import Data.Product
    renaming (proj₁ to fst ; proj₂ to snd)
    using (_×_ ; Σ ; Σ-syntax ; _,_ ; <_,_> ; curry ; uncurry ; map₂ ; assocˡ ; assocʳ) public
open import Data.Product.Properties using (Σ-≡,≡→≡) public
open import Data.Sum
    using (inj₁ ; inj₂ ; [_,_])
    renaming (_⊎_ to _+_) public
open import Data.Unit using (⊤ ; tt) public
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ₚ ; tt to ttₚ) public
open import Data.Empty using (⊥ ; ⊥-elim) public
open import Data.Empty.Polymorphic renaming (⊥ to ⊥ₚ ; ⊥-elim to ⊥ₚ-elim) public
open import Data.Fin
  using (Fin ; fromℕ)
  renaming (zero to fzero ; suc to fsuc) public
open import Data.Nat using (ℕ ; suc ; zero ; _≤_ ; z≤n ; s≤s) public
open import Data.Nat.Properties using (≤-irrelevant ; ≤-antisym) public

open import Function hiding (_↔_ ; _↪_ ; Surjective ; _⇔_) public

open import Data.String using (String)
-----------------------------------------------------------------------------
module GVars where 
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ

-----------------------------------------------------------------------------
-- Rewriting  

open import Agda.Builtin.Equality.Rewrite public 

-----------------------------------------------------------------------------
-- set comprehensions

comprehension-syntax₁ : ∀ {ℓ₁ ℓ₂} → {A : Set ℓ₁} (P : A → Set ℓ₂) → Set _ 
comprehension-syntax₁ {A = A} P = Σ A P  

syntax comprehension-syntax₁ (λ x → P) = ⟨ x ∣ P ⟩

comprehension-syntax₂ : ∀ {ℓ₁ ℓ₂} → (A : Set ℓ₁) (P : A → Set ℓ₂) → Set _ 
comprehension-syntax₂ = Σ 

syntax comprehension-syntax₂ A (λ x → P) = ⟨ x ∈ A ∣ P ⟩


-----------------------------------------------------------------------------
-- Bi-implication
-- (the std. library defines _↔_ instead as isomorphism.)

record _↔_ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    to : A → B
    from : B → A

sym-↔ : {ℓ₁ : Level} {ℓ₂ : Level} → {A : Set ℓ₁} {B : Set ℓ₂} → (A ↔ B) → (B ↔ A)
sym-↔ ( to , from ) = from , to

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

open GroupoidSyntax {{...}} public
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

open import Function hiding (_↔_) public 

open import Relation.Binary.PropositionalEquality 
    using (_≡_ ; trans ; sym ; refl ; module ≡-Reasoning ; cong) public 
open import Relation.Nullary using (¬_) public

-----------------------------------------------------------------------------
-- Bi-implication
-- (the std. library defines _↔_ instead as isomorphism.)

record _↔_ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor _,_
  field 
    to : A → B 
    from : B → A 

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

  infixr 5 _○_
  _○_ : x ≡ y → y ≡ z → x ≡ z
  _○_ = trans 

  !_ : x ≡ y → y ≡ x
  !_ = sym 

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

  left-inv : {x y : A} (p : x ≡ y) → (! p) ○ p ≡ refl
  left-inv {x = x} {y} refl = refl 

  right-inv : {x y : A} (p : x ≡ y) → p ○ ! p ≡ refl
  right-inv {x = x} {y} refl = refl 

  involution : {x y : A} (p : x ≡ y) → ! (! p) ≡ p
  involution {x = x} {y} refl = refl 

  left-identity : {x y : A} (p : x ≡ y) → refl ○ p ≡ p
  left-identity {x = x} {y}  refl = refl 

  right-identity : {x y : A} (p : x ≡ y) → p ○ refl ≡ p
  right-identity {x = x} {y} refl = refl 

  assoc : {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → (p ○ q) ○ r ≡ p ○ (q ○ r)
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

  refl-htpy : (f : (x : A) → B x) → f ∼ f
  refl-htpy f _ = refl

  private 
    variable 
      f g h : (x : A) → B x 

  inv-htpy : f ∼ g → g ∼ f
  inv-htpy f∼g = sym ∘ f∼g

  concat-htpy : f ∼ g → g ∼ h → f ∼ h
  concat-htpy f∼g g∼h x = trans (f∼g x) (g∼h x)

  infixl 30 inv-htpy
  syntax inv-htpy H = H ⁻¹         
  infixl 25 concat-htpy
  syntax concat-htpy G H = G · H

  -- _∼_ is an equivalence relation
  ∼-equiv : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → IsEquivalence (_∼_ {A = A} {B = B})
  ∼-equiv .IsEquivalence.refl {f} = refl-htpy f
  ∼-equiv .IsEquivalence.sym = inv-htpy
  ∼-equiv .IsEquivalence.trans = concat-htpy

  -- ((x : A) → B x , _∼_) is a setoid on any type A and family B.
  ∼-setoid : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} → Setoid (ℓ₁ ⊔ ℓ₂) _ 
  ∼-setoid {A = A} {B} .Setoid.Carrier = (x : A) → B x
  ∼-setoid {A = A} {B} .Setoid._≈_ = _∼_ {A = A} {B = B} 
  ∼-setoid .Setoid.isEquivalence = ∼-equiv 

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
    (refl-htpy _) 
    concat-htpy public

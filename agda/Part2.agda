module Part2 where
  open import Agda.Primitive
  open import Data.Bool
  open import Data.Product
  open import Data.Sum
  open import Function
  open import Relation.Binary.PropositionalEquality  

  module Homotopies where 
    open import Relation.Binary using (IsEquivalence ; Setoid) public
    private 
      variable 
        ℓ ℓ₁ ℓ₂ ℓ₃ : Level 
        A : Set ℓ
        B : A → Set ℓ 

    -- Definition 9.1.2
    infix 4 _∼_
    _∼_ : {A : Set ℓ₁} {B : A → Set ℓ₂} → ((x : A) → B x) → ((x : A) → B x) → Set (ℓ₁ ⊔ ℓ₂)
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

  module HomotopyReasoning {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) where 
    -- Open setoid reasoning syntax with carriers A and B
    open Homotopies 
    open import Relation.Binary.Reasoning.Setoid (∼-setoid {A = A} {B}) public

  module Chapter9 where

    open Homotopies 
    private variable
      ℓ : Level

    -- Example 9.1.3

    neg-bool-id : not ∘ not ∼ id
    neg-bool-id = λ { false → refl ; true → refl}

    -- Proposition 9.1.6

    assoc-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g h i : (x : A) → B x} →
                 (H : f ∼ g) → (K : g ∼ h) → (L : h ∼ i) → (H · K) · L ∼ H · (K · L)
    assoc-htpy H K L = λ x → trans-assoc (H x)

    left-unit-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
                     (H : f ∼ g) → refl-htpy f · H ∼ H
    left-unit-htpy H = λ x → refl

    right-unit-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
                      (H : f ∼ g) → H · refl-htpy g ∼ H
    right-unit-htpy H = λ x → trans-reflʳ (H x)

    left-inv-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
                    (H : f ∼ g) → H ⁻¹ · H ∼ refl-htpy g
    left-inv-htpy H = λ x → trans-symˡ (H x)

    right-inv-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x}
                     (H : f ∼ g) → H · H ⁻¹ ∼ refl-htpy f
    right-inv-htpy H = λ x → trans-symʳ (H x)

    -- Definition 9.1.7

    -- Can't overload (I think) ·, so just using names for now

    whˡ : {A B C : Set ℓ} {f g : A → B} → (h : B → C) → (H : f ∼ g) → (h ∘ f) ∼ (h ∘ g)
    whˡ h H = λ x → cong h (H x)

    infixl 25 whˡ
    syntax whˡ h H = h ·ₗ H

    whʳ : {A B C : Set ℓ} {g h : B → C} → (H : g ∼ h) → (f : A → B) → (g ∘ f) ∼ (h ∘ f)
    whʳ H f = λ x → H (f x)

    infixl 25 whʳ
    syntax whʳ H f = H ·ᵣ f

    -- Definition 9.2.1

    sec : {A B : Set ℓ} (f : A → B) → Set ℓ
    sec {A = A} {B} f = Σ[ g ∈ (B → A) ] f ∘ g ∼ id

    retr : {A B : Set ℓ} (f : A → B) → Set ℓ
    retr {A = A} {B} f = Σ[ h ∈ (B → A) ] h ∘ f ∼ id

    is-equiv : {A B : Set ℓ} (f : A → B) → Set ℓ
    is-equiv f = sec f × retr f

    _≃_ : Set ℓ → Set ℓ → Set ℓ
    A ≃ B = Σ[ f ∈ (A → B) ] is-equiv f

    not-quite-triviality : Bool ≃ Bool
    not-quite-triviality = not , ((not , neg-bool-id) , (not , neg-bool-id))

    -- Skipping examples for now, that would require sorting out the Part 1 work...

    -- Remark 9.2.6

    has-inverse : {A B : Set ℓ} → (A → B) → Set ℓ
    has-inverse {A = A} {B} f = Σ[ g ∈ (B → A) ] (f ∘ g ∼ id) × (g ∘ f ∼ id)

    has-inverse⇒is-equiv : {A B : Set ℓ} {f : A → B} → has-inverse f → is-equiv f
    has-inverse⇒is-equiv (g , (H , K)) = (g , H) , (g , K)

    -- Proposition 9.2.7

    is-equiv⇒has-inverse : {A B : Set ℓ} {f : A → B} → is-equiv f → has-inverse f
    is-equiv⇒has-inverse {f = f} ((g , G) , (h , H)) = g , (G , L)
      where K : g ∼ h
            K = (H ·ᵣ g) ⁻¹ · (h ·ₗ G)
            L : (g ∘ f) ∼ id
            L = K ·ᵣ f · H

    -- Corollary 9.2.8

    equivalence-inverse-equivalence : {A B : Set ℓ} {f : A → B} →
                                      (p : is-equiv f) →
                                      is-equiv (p .proj₁ .proj₁)
    equivalence-inverse-equivalence {f = f} p@((g , G) , (h , H)) =
      has-inverse⇒is-equiv (f , L , G)
      where K : g ∼ h
            K = (H ·ᵣ g) ⁻¹ · (h ·ₗ G)

            L : g ∘ f ∼ id
            L = K ·ᵣ f · H

    -- Example 9.2.9

    open import Data.Empty

    ⊥-unit-+ : {A : Set ℓ} → (A ⊎ ⊥) ≃ A
    ⊥-unit-+ {A = A} = α , has-inverse⇒is-equiv (β , (G , H)) where
      α : A ⊎ ⊥ → A
      α = λ { (inj₁ x) → x }
      β : A → A ⊎ ⊥
      β = inj₁
      G : α ∘ β ∼ id
      G = λ x → refl
      H : β ∘ α ∼ id
      H = λ { (inj₁ x) → refl }


    ×-distrib-+ : {A B C : Set ℓ} → (A × (B ⊎ C)) ≃ ((A × B) ⊎ (A × C))
    ×-distrib-+ {A = A} {B} {C} = α , has-inverse⇒is-equiv (β , (G , H)) where
      α : A × (B ⊎ C) → (A × B) ⊎ (A × C)
      α (x , inj₁ y) = inj₁ (x , y)
      α (x , inj₂ y) = inj₂ (x , y)
      β : (A × B) ⊎ (A × C) → A × (B ⊎ C)
      β (inj₁ (x , y)) = (x , inj₁ y)
      β (inj₂ (x , y)) = (x , inj₂ y)
      G : α ∘ β ∼ id
      G = λ { (inj₁ x) → refl ; (inj₂ y) → refl}
      H : β ∘ α ∼ id
      H = λ { (fst , inj₁ x) → refl ; (fst , inj₂ y) → refl}

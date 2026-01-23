module Part2 where

  module Chapter9 where

    open import Agda.Primitive
    open import Data.Product
    open import Data.Sum
    open import Function
    open import Relation.Binary.PropositionalEquality

    private variable
      ℓ : Level

    infix 4 _∼_
    _∼_ : {A : Set ℓ} {B : A → Set ℓ} → ((x : A) → B x) → ((x : A) → B x) → Set ℓ
    _∼_ {A = A} f g = (x : A) → f x ≡ g x


    -- Definition 9.1.5

    refl-htpy : {A : Set ℓ} {B : A → Set ℓ} → (f : (x : A) → B x) → f ∼ f
    refl-htpy f = λ x → refl

    inv-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} → f ∼ g → g ∼ f
    inv-htpy f∼g = λ x → sym (f∼g x)

    concat-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
    concat-htpy f∼g g∼h = λ x → trans (f∼g x) (g∼h x)

    infixl 30 inv-htpy
    syntax inv-htpy H = H ⁻¹         -- this is \^-\^1. This feels like a bad idea.
    infixl 25 concat-htpy
    syntax concat-htpy G H = G · H

    -- Proposition 9.1.6

    assoc-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g h i : (x : A) → B x} → (H : f ∼ g) → (K : g ∼ h) → (L : h ∼ i) → (H · K) · L ∼ H · (K · L)
    assoc-htpy H K L = λ x → trans-assoc (H x)

    left-unit-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} (H : f ∼ g) → refl-htpy f · H ∼ H
    left-unit-htpy H = λ x → refl

    right-unit-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} (H : f ∼ g) → H · refl-htpy g ∼ H
    right-unit-htpy H = λ x → trans-reflʳ (H x)

    left-inv-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} (H : f ∼ g) → H ⁻¹ · H ∼ refl-htpy g
    left-inv-htpy H = λ x → trans-symˡ (H x)

    right-inv-htpy : {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} (H : f ∼ g) → H · H ⁻¹ ∼ refl-htpy f
    right-inv-htpy H = λ x → trans-symʳ (H x)

    -- Definition 9.1.7

    -- Can't overload (I think) ·, so just using names for now

    whˡ : {A B C : Set ℓ} {f g : A → B} → (h : B → C) → (H : f ∼ g) → (h ∘ f) ∼ (h ∘ g)
    whˡ h H = λ x → cong h (H x)

    whʳ : {A B C : Set ℓ} {g h : B → C} → (H : g ∼ h) → (f : A → B) → (g ∘ f) ∼ (h ∘ f)
    whʳ H f = λ x → H (f x)

    -- Definition 9.2.1

    sec : {A B : Set ℓ} (f : A → B) → Set ℓ
    sec {A = A} {B} f = Σ[ g ∈ (B → A) ] f ∘ g ∼ id

    retr : {A B : Set ℓ} (f : A → B) → Set ℓ
    retr {A = A} {B} f = Σ[ h ∈ (B → A) ] h ∘ f ∼ id

    is-equiv : {A B : Set ℓ} (f : A → B) → Set ℓ
    is-equiv f = sec f × retr f

    _≃_ : Set ℓ → Set ℓ → Set ℓ
    A ≃ B = Σ[ f ∈ (A → B) ] is-equiv f

    -- Skipping examples for now, that would require sorting out the Part 1 work...

    -- Remark 9.2.6

    has-inverse : {A B : Set ℓ} → (A → B) → Set ℓ
    has-inverse {A = A} {B} f = Σ[ g ∈ (B → A) ] (f ∘ g ∼ id) × (g ∘ f ∼ id)

    has-inverse⇒is-equiv : {A B : Set ℓ} {f : A → B} → has-inverse f → is-equiv f
    has-inverse⇒is-equiv {f} (g , (H , K)) = (g , H) , (g , K)

    -- Proposition 9.2.7

    is-equiv⇒has-inverse : {A B : Set ℓ} {f : A → B} → is-equiv f → has-inverse f
    is-equiv⇒has-inverse {f = f} ((g , G) , (h , H)) = g , (G , (λ x → trans (K (f x)) (H x)))
      where K : g ∼ h
            K = λ x → trans (sym (H (g x))) (cong h (G x))

    -- Corollary 9.2.8

    equivalence-inverse-equivalence : {A B : Set ℓ} {f : A → B} → (p : is-equiv f) → is-equiv (p .proj₁ .proj₁)
    equivalence-inverse-equivalence {f = f} p@((g , G) , (h , H)) = has-inverse⇒is-equiv (f , ((λ x → trans (K (f x)) (H x)) , G))
      where K : g ∼ h
            K = λ x → trans (sym (H (g x))) (cong h (G x))

    -- Example 9.2.9

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

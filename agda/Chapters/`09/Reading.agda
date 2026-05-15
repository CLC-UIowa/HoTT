{-# OPTIONS --without-K #-}
module Chapters.`09.Reading where

open import Prelude

open import Relation.Binary.PropositionalEquality
    using (trans-assoc ; trans-reflʳ ; trans-symˡ ; trans-symʳ)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C D : Set ℓ
  𝐁 𝐂 𝐃 : A → Set ℓ
  f g h i : (x : A) → 𝐁 x

--------------------------------------------------------------------
-- §9.1 

-- Example 9.1.3

neg-bool-id : not ∘ not ∼ id
neg-bool-id = λ { false → refl ; true → refl}

--------------------------------------------------------------------
-- §9.2

-- Definition 9.2.1

section : (f : A → B) → Set _
section {A = A} {B = B} f = Σ[ g ∈ (B → A) ] f ∘ g ∼ id

retraction : (f : A → B) → Set _
retraction {A = A} {B = B} f = Σ[ h ∈ (B → A) ] h ∘ f ∼ id

is-equiv : (f : A → B) → Set _
is-equiv f = section f × retraction f

-- Accessors for sections and retractions from is-equiv
`sec : {f : A → B} → is-equiv f → B → A
`sec = fst ∘ fst

`retr : {f : A → B} → is-equiv f → B → A
`retr = fst ∘ snd

_≃_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
A ≃ B = Σ[ f ∈ (A → B) ] is-equiv f

-- "For any equivalence e : A ≃ B, we define e⁻¹ to be the
--  section of e."
`inv : A ≃ B → B → A
`inv = `sec ∘ snd

not-quite-triviality : Bool ≃ Bool
not-quite-triviality = not , ((not , neg-bool-id) , (not , neg-bool-id))

-- Skipping examples for now, that would require sorting out the Part 1 work...

-- Remark 9.2.6

has-inverse : (A → B) → Set _
has-inverse {A = A} {B = B} f = Σ[ g ∈ (B → A) ] (f ∘ g ∼ id) × (g ∘ f ∼ id)

has-inverse⇒is-equiv : has-inverse f → is-equiv f
has-inverse⇒is-equiv (g , (H , K)) = (g , H) , (g , K)

-- Proposition 9.2.7

-- if f has a section g and retraction h then g ∼ h.
is-equiv⇒equalSplits : ∀ {f : A → B} (p : is-equiv f) → `sec p ∼ `retr p
is-equiv⇒equalSplits {f = f} ((g , G) , (h , H)) = begin
  g          ∼⟨ (H ·ᵣ g) ⁻¹ ⟩
  h ∘ f ∘ g  ∼⟨ h ·ₗ G ⟩
  h ∎
  where
    open HomReasoning

is-equiv⇒has-inverse : is-equiv f → has-inverse f
is-equiv⇒has-inverse {f = f} p@((g , G) , (h , H)) = g , G , L
  where
    open HomReasoning
    L : (g ∘ f) ∼ id
    L = begin
          g ∘ f ∼⟨ is-equiv⇒equalSplits p ·ᵣ f ⟩
          h ∘ f ∼⟨  H ⟩
          id ∎

-- Corollary 9.2.8

equivalence-inverse-equivalence : (p : is-equiv f) →
                                  is-equiv (`sec p)
equivalence-inverse-equivalence {f = f} p@((g , G) , (h , H)) =
  has-inverse⇒is-equiv (f , L , G)
  where
    open HomReasoning
    L : g ∘ f ∼ id
    L = begin
      g ∘ f ∼⟨ is-equiv⇒equalSplits p ·ᵣ f ⟩
      h ∘ f ∼⟨ H ⟩
      id ∎

-- Example 9.2.9

open import Data.Empty

⊥-unit-+ : {A : Set ℓ} → (A + ⊥) ≃ A
⊥-unit-+ {A = A} = α , has-inverse⇒is-equiv (β , (G , H)) where
  α : A + ⊥ → A
  α = λ { (inj₁ x) → x }
  β : A → A + ⊥
  β = inj₁
  G : α ∘ β ∼ id
  G = λ x → refl
  H : β ∘ α ∼ id
  H = λ { (inj₁ x) → refl }


×-distrib-+ : {A B C : Set ℓ} → (A × (B + C)) ≃ ((A × B) + (A × C))
×-distrib-+ {A = A} {B} {C} = α , has-inverse⇒is-equiv (β , (G , H)) where
  α : A × (B + C) → (A × B) + (A × C)
  α (x , inj₁ y) = inj₁ (x , y)
  α (x , inj₂ y) = inj₂ (x , y)
  β : (A × B) + (A × C) → A × (B + C)
  β (inj₁ (x , y)) = (x , inj₁ y)
  β (inj₂ (x , y)) = (x , inj₂ y)
  G : α ∘ β ∼ id
  G = λ { (inj₁ x) → refl ; (inj₂ y) → refl}
  H : β ∘ α ∼ id
  H = λ { (fst , inj₁ x) → refl ; (fst , inj₂ y) → refl}

-- Example 9.2.10:
-- generalizing laws for cartesian products (_×_) to
-- arbitrary dependent products.

-- Σ[ x ∈ ⊥ ] (B x) is the dependent version of ⊥ × B ≃ ⊥
Σ-absorptionₗ : (Σ[ x ∈ ⊥ ] (𝐁 x)) ≃ ⊥
Σ-absorptionₗ {𝐁 = B} =
  to , has-inverse⇒is-equiv (from , (λ ()) , λ ())
  where
    to : Σ[ x ∈ ⊥ ] (B x) → ⊥
    to ()

    from : ⊥ → Σ[ x ∈ ⊥ ] (B x)
    from ()


-- Σ[ x ∈ ⊤ ] (B x) ≃ B tt is the dependent version of ⊤ × B ≃ B
Σ-unitₗ :  (Σ[ x ∈ ⊤ ] (𝐁 x)) ≃ 𝐁 tt
Σ-unitₗ  {𝐁 = B} = to , has-inverse⇒is-equiv (from , H , G)
  where
    -- N.b. I'm using pattern matching on x : ⊤, which isn't
    -- strictly the same as the induction principle for ⊤
    to : (Σ[ x ∈ ⊤ ] (B x)) → B tt
    to (tt , b) = b

    from : B tt → (Σ[ x ∈ ⊤ ] (B x))
    from b = (tt , b)

    H : to ∘ from ∼ id
    H = refl-∼

    G : from ∘ to ∼ id
    G (tt , b) = refl

--------------------------------------------------------------------
-- §9.3 Characterizing the identity types of Σ-types

_≡Σ_ : Σ A 𝐁 → Σ A 𝐁 → Set _
_≡Σ_ {A = A} {𝐁 = B} s t =
  Σ[ α ∈ (fst s ≡ fst t) ]
    tr B α (snd s) ≡ snd t

-- Lemma 9.3.2: _≡Σ_ is reflexive

refl-≡Σ : ∀ (p : Σ A 𝐁) → p ≡Σ p
refl-≡Σ p = refl , refl

sym-≡Σ : ∀ {p q : Σ A 𝐁} → (p ≡Σ q) → (q ≡Σ p)
sym-≡Σ (refl , refl) = refl , refl

-- Definition 9.3.3: pair-eq
-- Or: _≡Σ_ respects propositional equivalence

pair-eq : ∀ {s t : Σ A 𝐁} → s ≡ t → s ≡Σ t
pair-eq refl = refl-≡Σ _

-- Theorem 9.3.4: pair-eq is an equivalence
pairEqv : ∀ {s t : Σ A 𝐁} → is-equiv (pair-eq {s = s} {t = t})
pairEqv {s = s} {t} = has-inverse⇒is-equiv
  (eq-pair ,
    (λ p → eq-pair-section (fst p) (snd p)) ,
    eq-pair-retraction)
  where
    eq-pair : ∀ {s t : Σ A 𝐁} → s ≡Σ t → s ≡ t
    eq-pair {s = x , y} {t = x′ , y′} (refl , refl) = refl

    eq-pair-section : ∀ {s t : Σ A 𝐁} (α : (fst s ≡ fst t))
                        (β : tr _ α (snd s) ≡ snd t) →
                        pair-eq (eq-pair (α , β)) ≡ (α , β)
    eq-pair-section refl refl = refl

    eq-pair-retraction : ∀{s t : Σ A 𝐁}
                          (p : s ≡ t) →
                          eq-pair (pair-eq p) ≡ p
    eq-pair-retraction refl = refl


--------------------------------------------------------------------------------
-- -- ≃ is an eqv relation

has-inverse-comp : {f : B → C} {g : A → B} → 
                   has-inverse f → has-inverse g → has-inverse (f ∘ g)
has-inverse-comp {f = f} {g = g} 
  (f̅ , f∘f̅~id , f̅∘f~id) (g̅ , g∘g̅~id , g̅∘g~id) = 
  g̅ ∘ f̅ , 
  ((λ x →  ap f (g∘g̅~id (f̅ x)) ○ f∘f̅~id x) , 
  λ x → ap g̅ (f̅∘f~id (g x)) ○ g̅∘g~id x )

is-equiv-comp : {f : B → C} {g : A → B} → 
                is-equiv f → 
                is-equiv g → 
                is-equiv (f ∘ g)
is-equiv-comp {f = f} {g = g} equiv-f equiv-g =
  has-inverse⇒is-equiv (has-inverse-comp has-inverse-f has-inverse-g)
  where
    has-inverse-f : has-inverse f
    has-inverse-f = is-equiv⇒has-inverse equiv-f

    has-inverse-g : has-inverse g
    has-inverse-g = is-equiv⇒has-inverse equiv-g

trans-≃ : A ≃ B → B ≃ C → A ≃ C
trans-≃ e1 e2 = (fst e2 ∘ fst e1) , (is-equiv-comp (snd e2) (snd e1))

sym-≃ : A ≃ B → B ≃ A
sym-≃ (f , is-eq-f) with is-equiv⇒has-inverse is-eq-f
... | (f̅ , is-eq-f̅) =  f̅ , ((f , (is-eq-f̅ .snd)) , (f , (is-eq-f̅ .fst)))

refl-≃ : A ≃ A
refl-≃ = id , ((id , (λ x → refl)) , (id , λ x → refl))

--------------------------------------------------------------------------------
-- Equational reasoning over ≃ equivalence

module ≃-Reasoning {ℓ₁} where
  -- Usage:
  -- eq : A ≃ B
  -- eq = begin
  --   foo ≃⟨ ? ⟩
  --   ...
  --   ?   ≃⟨ ? ⟩
  --   bar ∎
  open import Relation.Binary.Reasoning.Syntax using (module ≃-syntax ; module begin-syntax ; module end-syntax)
  open import Relation.Binary.Reasoning.Base.Single (_≃_ {ℓ₁ = ℓ₁})
    refl-≃ 
    trans-≃ renaming (∼-go to ≃-go) public
  open ≃-syntax _IsRelatedTo_ _IsRelatedTo_ ≃-go sym-≃ public


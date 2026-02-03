{-# OPTIONS --without-K #-} 
module Chapters.`09.Reading where
  
open import Prelude 
open HomReasoning  

open import Relation.Binary.PropositionalEquality 
    using (trans-assoc ; trans-reflʳ ; trans-symˡ ; trans-symʳ)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C D : Set ℓ 
  𝐁 𝐂 𝐃 : A → Set ℓ 
  f g h i : (x : A) → 𝐁 x 

-- Example 9.1.3

neg-bool-id : not ∘ not ∼ id
neg-bool-id = λ { false → refl ; true → refl}

-- Proposition 9.1.6

assoc-htpy : (H : f ∼ g) → (K : g ∼ h) → (L : h ∼ i) → (H · K) · L ∼ H · (K · L)
assoc-htpy H K L = λ x → trans-assoc (H x)

left-unit-htpy : (H : f ∼ g) → refl-htpy f · H ∼ H
left-unit-htpy H = λ x → refl

right-unit-htpy : (H : f ∼ g) → H · refl-htpy g ∼ H
right-unit-htpy H = trans-reflʳ ∘ H

left-inv-htpy : (H : f ∼ g) → H ⁻¹ · H ∼ refl-htpy g
left-inv-htpy H = trans-symˡ ∘ H

right-inv-htpy : (H : f ∼ g) → H · H ⁻¹ ∼ refl-htpy f
right-inv-htpy H = trans-symʳ ∘ H 

-- Definition 9.1.7

whˡ : (h : B → C) → (H : f ∼ g) → (h ∘ f) ∼ (h ∘ g)
whˡ h H = λ x → cong h (H x)

infixl 25 whˡ
syntax whˡ h H = h ·ₗ H

whʳ : (H : g ∼ h) → (f : A → B) → (g ∘ f) ∼ (h ∘ f)
whʳ H f = λ x → H (f x)

infixl 25 whʳ
syntax whʳ H f = H ·ᵣ f

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

is-equiv⇒has-inverse : is-equiv f → has-inverse f
is-equiv⇒has-inverse {f = f} p@((g , G) , (h , H)) = g , G , L
  where 
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
    H = refl-htpy _ 

    G : from ∘ to ∼ id 
    G (tt , b) = refl 

-- 9.3 Characterizing the identity types of Σ-types 

_≡Σ_ : Σ A 𝐁 → Σ A 𝐁 → Set _ 
_≡Σ_ {A = A} {𝐁 = B} s t = 
  Σ[ α ∈ (fst s ≡ fst t) ]  
    tr B α (snd s) ≡ snd t 

-- Lemma 9.3.2: _≡Σ_ is reflexive

refl-≡Σ : ∀ (p : Σ A 𝐁) → p ≡Σ p 
refl-≡Σ p = refl , refl 

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




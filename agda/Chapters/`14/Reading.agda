module Chapters.`14.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises
open import Chapters.`12.Reading
open import Chapters.`13.Reading

open import Function

open is-contr
 
private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ 
    𝐁 : A → Set ℓ

--------------------------------------------------------------------------------
-- Ch. 14 Propositional Truncation

--------------------------------------------------------------------------------
-- Introduction.

-- AH> The introduction to Ch. 14 highlights an important subtlety:
--     often, when working *constructively*, we work with stronger information
--     than one does in mathematics. Rather than claim a set is finite,
--     we expect a *witness* to being finite---e.g., a bijection to a finite set.
--     As another example, a mathematician may claim that b ∈ B is in the image
--     of f. Or, more vagely, they might just claim that "f is a surjection"---
--     meaning each b ∈ B has an a ∈ A such that f(a) = b, without telling you
--     which particular a:

Surjective₀ : (f : A → B) → Set _
Surjective₀ {A = A} {B = B} f = ∀ (b : B) → Σ[ a ∈ A ](f a ≡ b)

-- Note that, if f is not injective, there might be many inhabitants of Surjective₀ f.
-- The mathematician may not care which a ∈ A we are picking, whereas we are forced
-- to care.

-- Recall from Ex. 10.8 that every type A with f : A → B is equivalent
-- to the total space of fibers over f.
Ex-10-8 : (f : A → B) → A ≃ (Σ[ b ∈ B ] (fib f b))
Ex-10-8 {A = A} {B = B} f = g , has-inverse⇒is-equiv (g⁻¹ , (λ { (b , a , refl) → refl }) , Refl) 
  where
    g : A → (Σ[ b ∈ B ] (fib f b))
    g a = f a , a , refl

    g⁻¹  : (Σ[ b ∈ B ] (fib f b)) → A 
    g⁻¹ (b , a , eq) = a 

-- Rijke writes "Something is clearly off here, because the type A is often not a subtype of the
-- type B, while we would expect the image of f to be a subtype of B."
-- To unpack this a bit: for arbitrary `f`, why should A be equivalent to the fibers of f?
-- A mathematician might write f⁻¹(B) to define the notion above: the set of a ∈ A that hit
-- B via f. This should only be equal to A if f is surjective.

-- Rijke further writes "Therefore we see that the type fib f b = Σ[ a ∈ A ] (f a ≡ b) 
-- does not quite capture the concept of b being in the image of f. The
-- difference is again due to the fact that fib f b is often not a proposition,
-- whereas we are looking to express the proposition that the preimage of f at b
-- is inhabited."
-- Again: fib f b tells us *a particular* a ∈ A s.t. f(a) = b, which is a
-- stronger notion than only knowing that there *exists* such an a.

--------------------------------------------------------------------------------
-- AH> A note---when we say something is a proposition, it's tempting to think
-- of it as being "either contractible or empty". An equivalent way of saying this
-- is "it's equivalent to ⊤ or to ⊥". But this isn't quite the case unless P
-- is decidable. 

⊤-or-⊥ : ∀ (P : Set ℓ) → is-prop P → Decidable P → is-contr P + is-empty P
⊤-or-⊥ P prp D with D 
... | inj₁ p =  inj₁ $ Irrelevant⇒contractibleIfInhabited (is-prop⇒Irrelevant prp) p
... | inj₂ q = inj₂ q

--------------------------------------------------------------------------------
-- Def 14.1.1. Let A be a type, and let f : A → P be a map into a proposition P.
-- We say that f is a *propositional truncation* of A if for every proposition Q, the
-- precomposition map 
--   — ∘ f : (P → Q) → (A → Q) 
-- is an equivalence.

is-prop-trunc : ∀ {ℓ} → (P : Set ℓ) → is-prop P → (f : A → P) → Setω
is-prop-trunc  P p f = ∀ {ℓ} (Q : Set ℓ) → is-prop Q → is-equiv (λ (h : P → Q) → h ∘ f)


--------------------------------------------------------------------------------
-- Remark 14.1.2: If f is a propositional truncation, then for all props Q, there exists
-- an extension h : P → Q s.t. the following commutes:
--   A
--   | \ 
-- f |  \ g
--   v   v
--   P -> Q
--     h

map-extension : ∀ (P : Set ℓ₁) → (prp : is-prop P) → (f : A → P) → 
                   is-prop-trunc P prp f → 
                   (Q : Set ℓ₂) → is-prop Q → 
                   (g : A → Q) → (Σ[ h ∈ (P → Q) ] (h ∘ f ≡ g))
map-extension P p f prp-t Q q g = is-equiv⇒is-contr-map (_∘ f) (prp-t Q q) g .center 


--------------------------------------------------------------------------------
-- Remark 14.1.3: is-prop-trunc P p f is implied by exhibiting a function with type
--  (A → Q) → (P → Q)
-- for arbitrary prop Q.

-- AH> This first property is proven in Ch. 12 as "propositionalEquivalence", but in fuller 
--     generality and for {P Q : Set}.
--     I'm going to rewrite it here rather than refactor it there.
prop-equivalence : ∀ {P : Set ℓ} {Q : Set ℓ₂} → 
                  is-prop P → is-prop Q → (f : P → Q) → (Q → P) → is-equiv f
prop-equivalence {P = P} {Q} p q f h = 
  has-inverse⇒is-equiv (h , ((λ x → q (f (h x)) x .center)) , λ x → p (h (f x)) x .center)
 -- has-inverse⇒is-equiv 
 --  (h , (λ x →  q (f (h x)) x .center), 
 --  λ x → p (h (f x)) x .center) 

-- Also observe that X → Q is a proposition for any type X and proposition Q.
prop-codomain : ∀ {Q : Set ℓ₂} → is-prop Q → (X : Set ℓ₁) → is-prop (X → Q) 
prop-codomain q X = Irrelevant⇒is-prop λ f g → (fun-ext _ _ (λ x → q (f x) (g x) .center)) 

-- We can inhabit is-prop-trunc P p f by instead inhabiting
--   (∀ {ℓ} → (Q : Set ℓ) → is-prop Q → (A → Q) → P → Q),
-- which is slightly less unpleasant.
is-prop-trunc′ : ∀ (P : Set ℓ₁) → (p : is-prop P) → (f : A → P) → 
                   (∀ {ℓ} → (Q : Set ℓ) → is-prop Q → (A → Q) → P → Q) → 
                   is-prop-trunc P p f
is-prop-trunc′ P p f H Q q = 
  prop-equivalence (prop-codomain q P) (prop-codomain q _) (_∘ f) (H Q q)   

--------------------------------------------------------------------------------
-- Proposition 14.1.4. Let A be a type, and consider two maps 
--   f : A → P and g : A → Q
-- into two propositions P and Q. If any two of the following three assertions hold,
-- so does the third:
--  (i) The map f is a propositional truncation of A
--  (ii) The map g is a propositional truncation of A
--  (iii) There is a (unique) equivalence P ≃ Q.

-- AH> Todo!              

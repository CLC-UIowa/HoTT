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
open _↔_
 
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

-- This first property is proven in Ch. 12 as "propositionalEquivalence", but in fuller 
-- generality as: 
--   propositionalEquivalence : {P : Set ℓ₁} {Q : Set ℓ₂} → is-prop P → is-prop Q → ((P ≃ Q) ↔ (P ↔ Q))
-- This definition tells us that P ≃ Q but not specifically that (f : P → Q) is an equivalence,
-- so I'll prove this ad hoc lemma instead. 
prop-equivalence : ∀ {P : Set ℓ} {Q : Set ℓ₂} → 
                  is-prop P → is-prop Q → (f : P → Q) → (Q → P) → is-equiv f
prop-equivalence {P = P} {Q} p q f h = 
  has-inverse⇒is-equiv (h , ((λ x → q (f (h x)) x .center)) , λ x → p (h (f x)) x .center)

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

-- We will need the following helper, which states that (P ≃ Q) is a prop if P and
-- Q are props.
≃-prop : {P : Set ℓ} {Q : Set ℓ} 
         (p : is-prop P) 
         (q : is-prop Q)  → 
         is-prop (P ≃ Q) 
≃-prop {P = P} {Q} p q = Irrelevant⇒is-prop irrel
  where 
    -- AH> This proof looks more involved than it really is. The first pain point
    --     is that we are equating dependent pairs, hence I use with-abstractions
    --     to pattern-match on equalities of type f ≡ g, σ₁ ≡ σ₂, and ρ₁ ≡ ρ₂. 
    --     (These identities hold because f, g, σᵢ, and ρᵢ are each propositions.)
    --     Next, we need to show the contractions contr₁ and contr₂ are equivalent,
    --     which follows from propositions also being sets. 
    irrel : Irrelevant (P ≃ Q) 
    irrel (f , ((σ₁ , sec₁) , (ρ₁ , retr₁))) (g , ((σ₂ , sec₂) , (ρ₂ , retr₂))) with 
        prop-codomain q _ f g .center
      | prop-codomain p _ σ₁ σ₂
      | prop-codomain p _ ρ₁ ρ₂
    ... | refl | (refl , contr₁) | (refl , contr₂) = 
      ap (f ,_) (ap₂ _,_ (ap (σ₁ ,_) 
        (fun-ext _ _ λ x → is-prop⇒is-set q _ _ (sec₁ x) (sec₂ x) .center)) 
        (ap (ρ₁ ,_) (fun-ext _ _ (λ x → is-prop⇒is-set p _ _ (retr₁ x) (retr₂ x) .center)))) 

module _ {P : Set ℓ} {Q : Set ℓ} 
        (p : is-prop P) 
        (q : is-prop Q) 
        (f : A → P)
        (g : A → Q) where 
  
  
  -- We express that P ≃ Q is a "unique" equivalence by stating that
  -- (P ≃ Q) is contractible.
  is-prop-trunc-→≃ : is-prop-trunc P p f → is-prop-trunc Q q g → 
                      is-contr (P ≃ Q)
  is-prop-trunc-→≃ p-trunc q-trunc = P≃Q , 𝒞 
    where
      -- We need to simply exhibit a pair of functions inhabiting P ↔ Q.
      -- In one direction, that f is a propositional truncation means:
      --  is-equiv (λ (h : P → Q) → h ∘ f)
      -- Where (λ (h : P → Q) → h ∘ f) : (P → Q) → (A → Q). That this function
      -- is a section means we have a function at the converse type:
      --   (A → Q) → (P → Q)
      -- and hence we may build a witness to (P → Q) from g : A → Q.
      -- Inhabiting the other direction, Q → P, is entirely dual.    
      P≃Q : P ≃ Q
      P≃Q = propositionalEquivalence p q .from (p-trunc Q  q .fst .fst g , q-trunc P p .fst .fst f) 

      -- This fact follows from P ≃ Q being a proposition if P and Q are propositions.
      𝒞 : ∀ (e : P ≃ Q) → P≃Q  ≡ e
      𝒞 e = ≃-prop p q P≃Q e .center 

  -- We'll split the other direction into two functions, because the type
  --   is-prop-trunc P p f : Setω
  -- and so cannot be bundled up with _×_ or _↔_. 
  -- The proof idea:
  -- Use the simpler is-prop-trunc′, which expects the "body" below. 
  -- Now our goal is to build a term with type Q′, given h : A → Q′ and x : Q.
  -- As f is a propositional truncation, we have a section at type:
  --   (A → Q′) → P → Q′
  -- and so we pass it h : A → Q′ and, leveraging the equivalence P ≃ Q,
  -- convert x : Q to type P, giving us back an inhabitant of Q′.
  ≃→is-prop-trunc₁ : is-contr (P ≃ Q) → is-prop-trunc P p f → is-prop-trunc Q q g
  ≃→is-prop-trunc₁ ((_ , ((σ , _) , _)) , _) prp-trnc-f = is-prop-trunc′ Q q g body 
    where 
      -- Using where abstraction just to spell out types.
      body : ∀ {ℓ} (Q′ : Set ℓ) → is-prop Q′ → (A → Q′) → (Q → Q′) 
      body Q′ prop-Q′ h x = —∘f-sec h (σ x)
        where 
          —∘f-sec : (A → Q′) → P → Q′
          —∘f-sec = prp-trnc-f Q′ prop-Q′ .fst .fst

  -- We repeat the dualized, but same, steps as above.
  ≃→is-prop-trunc₂ : is-contr (P ≃ Q) → is-prop-trunc Q q g → is-prop-trunc P p f
  ≃→is-prop-trunc₂ ((e , (_ , _) , _) , _) prp-trnc-g = is-prop-trunc′ P p f λ Q′ prop-Q′ h x → prp-trnc-g Q′ prop-Q′ .fst .fst h (e x) 

--------------------------------------------------------------------------------
-- § 14.2 Propositional truncations as higher inductive types 
-- 
-- Higher inductive types specify not just point constructors but "path constructors".
-- Agda has no base support for higher inductive types, and there is no consensus
-- as to how such could be added. Cubical agda is one implementation, which commits
-- to cubical type theory to realize Univalent Foundations, including HITs.
-- A more vanilla approach is to postulate the formation rules, constructors, induction
-- principle, and computation rule for each HIT. We then use Agda's REWRITE pragma
-- to force the computation rule to be computed definitionally.
-- 
-- We first view propositional truncation as a HIT, which requires no computational rule.

-- Type former, point & path constructor
postulate
  ∥_∥ : ∀ {ℓ} → Set ℓ → Set ℓ 
  η : A → ∥ A ∥
  α : ∀ (x y : ∥ A ∥) → x ≡ y

-- Lemma 14.2.1: 
-- It follows basically from definition that ∥ A ∥ is a prop.
∥_∥-prop : ∀ (A : Set ℓ) → is-prop (∥ A ∥)
∥_∥-prop A = Irrelevant⇒is-prop α

--------------------------------------------------------------------------------
{- On induction principles for HITs: a very long detour

I'm going to take us on a long detour because I am particular interested
in how we arrive at the induction principle for ∥_∥. In particular,
I am interested in how we extrapolate from "defining behavior on points"
to "defining behavior on paths".

The idea behind an induction principle / pattern matching on a type X is that, 
in order to describe an eliminator h : X → Y, it is sufficient to describe just how h behaves 
on the *generators* of X. For example, we know that all elements of type ℕ are freely generated by
either 0 : ℕ or S : ℕ → ℕ, and hence to define h : ℕ → Y, it is sufficient to 
define h as 
  h 0     = φ  
  h (S n) = ψ 
for φ : Y and ψ : Y.

Higher Inductive Types (HITs) allow us to define types using both *point* and *path* constructors. 
The induction principle for HITs extends the same structural idea: to define h : X → Y, 
we must define how it behaves on the point generators, and prove that it respects the path generators.
This is analogous to defining a group homomorphism: it is not sufficient to simply define
a mapping between elements, but also to show that the equational structure of X 
is respected in Y. 

What does that mean, to define a function on path generators?
Recall that h : X → Y acts as a functor from the groupoid X to the groupoid 
Y; it maps objects in X to objects in Y and, given x, y : X, 
maps a path u : x ≡ y to a path in Y, namely its action-on-paths:
  ap h u : h x ≡ h y.

At first, I wanted to argue that the presence of "non-trivial" path constructors
meant we must be careful in mapping the arrow (α x y) : x ≡ y in ∥ A ∥ to 
an arrow (h x ≡ h y) in Y. But this argument is flawed! ∥ A ∥ is a *set*, and
is not somehow generated by non trivial path constructors: -}

-- ∥ A ∥ is a set
∥_∥-set : ∀ (A : Set ℓ) → is-set (∥ A ∥)
∥_∥-set A = is-prop⇒is-set (∥_∥-prop A)

-- and so paths in ∥ A ∥ are not "generated" by α. Indeed, 
-- the only paths in ∥ A ∥ are trivial. It is therefore 
-- not the topological structure of ∥ A ∥ that shapes its induction principle.
only-trivial-paths : ∀ {x : ∥ A ∥} → α x x ≡ refl 
only-trivial-paths {x = x} =   ∥ _ ∥-set x x (α x x) refl .center 

--------------------------------------------------------------------------------
-- Nevertheless, let's see what happens when our induction principle does not address 
-- the paths in ∥ A ∥.

module _ where private
  open PathReasoning

  -- A sensible alternative? Instead of postulating ∥_∥ and η, let's define 
  -- ∥_∥ as an inductive type and postulate its quotient structure.
  data ∥_∥′ (A : Set ℓ) : Set ℓ where 
    η′ : A → ∥ A ∥′ 
  postulate
    α′ : ∀ (x y : ∥ A ∥′) → x ≡ y

  -- From the inductive definition of ∥_∥′, we can
  -- define an induction principle via pattern matching,
  -- and need only describe how the eliminator 
  -- behaves on points.
  ∥—∥′-ind : {Q : ∥ A ∥′ → Set ℓ} → 
             (f : (a : A) → Q (η′ a)) → 
            ((t : ∥ A ∥′) → Q t)
  ∥—∥′-ind f (η′ x) = f x

  -- But this lets us define a section on η:
  σ : ∥ A ∥′ → A 
  σ = ∥—∥′-ind id

  η′-sec : σ ∘ (η′ {A = A}) ∼ id
  η′-sec = Refl 

  -- Clearly, the induction principle (pattern matching) is too strong. 
  -- The naughty equation is:
  --   ap σ (α′ (η′ x) (η′ y)) : σ (η′ x) ≡ σ (η′ y)
  -- whose type reduces (definitionally) to
  --   ap σ (α′ (η′ x) (η′ y)) : x ≡ y
  -- In other words, A is a prop!
  all-prop : ∀ {A : Set ℓ} → is-prop A 
  all-prop = Irrelevant⇒is-prop (λ x y → begin 
    x        ≡⟨ refl ⟩ 
    σ (η′ x) ≡⟨ ap σ (α′ (η′ x) (η′ y)) ⟩ 
    σ (η′ y) ≡⟨ refl ⟩ 
    y ∎)
  
  -- This is obviously bad.
  bad : true ≡ false
  bad = all-prop {A = Bool} true false .center

--------------------------------------------------------------------------------
{- A recursion principle for ∥_∥ 

Before defining the induction principle, let's think more simply on how 
we fix things with a well-behaved recursion principle.

When defining a recursion principle, we see that an equation by pattern 
would define h on points according to:
  h (η x) = f x 
where f : A → B, with the expectation that h ∘ η ∼ f. The intuition: We
throw f : A → B in as an argument to the recursion principle principle,
and assert (in the return type) that the pattern holds.

  ∥—⊩rec :  (f : A → B) → 
             ? → 
            Σ[ h ∈ (∥ A ∥ → B) ] (h ∘ η ∼ f)

Likewise, we should expect that h maps paths in ∥ A ∥ according to:
  ap h (α x y) = v x y
where v : (x y : ∥ A ∥) → h x ≡ h y. However, we're in the middle 
of defining h! So we cannot "throw it in" as an argument to the induction 
principle.

We know, however, that if (x y : ∥ A ∥), then they were generated by 
some (a b : A) such that 
  x = η a and y = η b
it follows then that 
    ap h (α x y) 
  = ap h (α (η a) (η b)) : h (η a) ≡ h (η b) 
but we know that h ∘ η ∼ f, and so
    ap h (α (η a) (η b)) : f a ≡ f b 
and hence we can instead require an argument of the form:
  v : (x y : A) → f x ≡ f y
-} 

postulate 
  ∥—⊩rec :  (f : A → B) → 
            (v : (x y : A) → f x ≡ f y) → 
            Σ[ h ∈ (∥ A ∥ → B) ] (h ∘ η ∼ f)

-- Alternatively, the HoTT book simply requires that B be a prop.
-- Our definition can build the HoTT definition (but not the other way around.)
prop-def→ : (f : A → B) → (v : is-prop B) → Σ[ h ∈ (∥ A ∥ → B) ] (h ∘ η ∼ f)
prop-def→ f v = ∥—⊩rec f λ x y → v (f x) (f y) .center

-- 
module _ where private 
  -- Now the naughty destructor won't work unless A is a prop!
  σ : is-prop A → ∥ A ∥ → A 
  σ prop = ∥—⊩rec id (λ x y → prop x y .center) .fst


{- --------------------------------------------------------------------------------
Finally:
Def 14.2.2: The induction principle for propositional truncations. 

This definition can be thought of as a mix between our recursion principle 
and the HoTT text's. The type 
  tr Q (α x y) u ≡ v
is just asserting that, modulo type indices, the image of Q is a prop. -}
postulate
  ∥—∥-ind : {Q : ∥ A ∥ → Set ℓ} → 
            (f : (a : A) → Q (η a)) → 
            ((x y : ∥ A ∥) (u : Q x) (v : Q y) → tr Q (α x y) u ≡ v) → 
            Σ[ h ∈ ((t : ∥ A ∥) → Q t) ] (h ∘ η ∼ f)










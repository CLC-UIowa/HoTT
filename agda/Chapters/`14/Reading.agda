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

open import Data.Nat using (_≤_)

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

  -- N.b. Incongruent with HITs in general, Agda also
  -- recognizes internally that constructors are disjoint. Observe:
  oopsies : ⊥ 
  oopsies with bad 
  ... | () 

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

  ∥—∥-rec :  (f : A → B) → 
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

module ∥—∥-recursor where 
  postulate
    ∥—∥-rec :  (f : A → B) → 
              ((x y : A) → f x ≡ f y) → 
              (∥ A ∥ → B)
    -- This computational law has to be asserted 
    ∥—∥-rec-comp : ∀ (f : A → B) (v : (x y : A) → f x ≡ f y) →  ∥—∥-rec f v ∘ η ∼ f 

  -- Alternatively, the HoTT book simply requires that B be a prop.
  -- Our definition can build the HoTT definition (but not the other way around.)
  prop-def→ : (f : A → B) → (v : is-prop B) → (∥ A ∥ → B)
  prop-def→ f v = ∥—∥-rec f λ x y → v (f x) (f y) .center

  module _ where private 
    -- Now the naughty destructor won't work unless A is a prop!
    σ : is-prop A → ∥ A ∥ → A 
    σ prop = ∥—∥-rec id (λ x y → prop x y .center)


{- --------------------------------------------------------------------------------
Finally:
Def 14.2.2: The induction principle for propositional truncations. 

This definition can be thought of as a mix between our recursion principle 
and the HoTT text's. The type 
  tr Q (α x y) u ≡ v
is just asserting that, modulo type indices, the image of Q is a prop.

A more straightforward translation of our recursion principle would 
be:
  ((x y : A) → tr Q (α (η x) (η y)) (f x) ≡ f y)
but Rijke argues "h(x) and h(y) are not determined by our choice of f".
I don't think this is true---we know, in fact, that h ∘ η ∼ f.

 -}
postulate
  ∥—∥-ind : {Q : ∥ A ∥ → Set ℓ} → 
            (f : (a : A) → Q (η a)) → 
            ((x y : ∥ A ∥) (u : Q x) (v : Q y) → tr Q (α x y) u ≡ v) → 
            (t : ∥ A ∥) → Q t
           
-- Remark 14.2.3: the second requirement of the induction principle
-- is satisfied iff Q is a family of propositions. 
-- AH> Calling again in to question why Rijke chose this definition.
fam-props⇒condition : {Q : ∥ A ∥ → Set ℓ} → (∀ (x : ∥ A ∥) → is-prop (Q x)) → 
      (x y : ∥ A ∥) (u : Q x) (v : Q y) → tr Q (α x y) u ≡ v
fam-props⇒condition p x y u q with α x y 
... | refl = p x u q .center 

condition⇒fam-props : {Q : ∥ A ∥ → Set ℓ} → 
      ((x y : ∥ A ∥) (u : Q x) (v : Q y) → tr Q (α x y) u ≡ v) → 
      is-prop-fam Q 

condition⇒fam-props  {Q = Q} p x = Irrelevant⇒is-prop 
  (λ u v → tr (λ X → tr Q X u ≡ v) 
            only-trivial-paths 
            (p x x u v))

-- the computational rule isn't strictly necessary, as  both (h ∘ η) and f map 
-- into props. We'll rewrite by it anyway!
∥—∥-comp : {Q : ∥ A ∥ → Set ℓ} → 
            (f : (a : A) → Q (η a)) → 
            (υ : (x y : ∥ A ∥) (u : Q x) (v : Q y) → tr Q (α x y) u ≡ v) → 
            ∥—∥-ind f υ ∘ η ∼ f
∥—∥-comp f υ a = condition⇒fam-props υ (η a) (∥—∥-ind f υ (η a)) (f a) .center

{-# REWRITE ∥—∥-comp #-}

-- It's more convenient, often (always?), to use ∥—∥-ind using the equivalent 
-- induction principle:
∥—∥-ind′ : {Q : ∥ A ∥ → Set ℓ} → 
          (f : (a : A) → Q (η a)) → 
          is-prop-fam Q → 
          (t : ∥ A ∥) → Q t
∥—∥-ind′ f q = ∥—∥-ind  f (fam-props⇒condition q)

-- The computation rule for ∥—∥-ind′ holds definitionally
-- by consequence of rewriting by ∥—∥-comp.
∥—∥-comp′ : {Q : ∥ A ∥ → Set ℓ} → 
          (f : (a : A) → Q (η a)) → 
          (υ : is-prop-fam Q) → 
          ∥—∥-ind′ f υ ∘ η ∼ f
∥—∥-comp′ f υ = Refl           

-- AH> The Book HoTT recursor, for free.
∥—∥-rec :  (f : A → B) → 
           is-prop B → 
           (∥ A ∥ → B)
∥—∥-rec f v = 
  ∥—∥-ind′ f (const v)

-- Again, the computational rule is definitional.
∥—∥-rec-comp : (f : A → B) (v : is-prop B) → ∥—∥-rec f v ∘ η ∼ f 
∥—∥-rec-comp f v = Refl 


--------------------------------------------------------------------------------
-- The universal property 

-- Thm 14.2.4: The map η : A → ∥ A ∥ satisfies the universal property 
-- of propositional truncation, that is:
--   (— ∘ η)
-- is an equivalence.

-- Pf. It suffices to construct a map
--   (Q : Set) → is-prop Q → (A → Q) → (∥ A ∥ → Q) 
-- We can build the result type (∥ A ∥ → Q) using the induction 
-- principle for truncated types. Clearly, the point constructor is handled
-- by f : A → Q. We handle the path constructor by observing that, as Q 
-- is a proposition, then the type family (const Q) is a family of propositions.
-- Hence we use the helper fam-props⇒condition to inhabit the condition 
-- on the path constructor α. 
η-is-prop-trunc : is-prop-trunc ∥ A ∥ ∥ A ∥-prop η 
η-is-prop-trunc {A = A} = is-prop-trunc′ ∥ A ∥ ∥ A ∥-prop η 
  (λ Q q f a → ∥—∥-ind f (fam-props⇒condition {Q = λ _ → Q} (λ _ → q)) a) 

--------------------------------------------------------------------------------
-- Proposition 14.2.5: ∥—∥ is functorial, i.e., there is a map
--   ∥—∥* : (A → B) → (∥ A ∥ → ∥ B ∥) 


∥_∥* : (f : A → B) → (∥ A ∥ → ∥ B ∥)
∥_∥* {A = A} {B = B} f = ∥—∥-ind′ (η ∘ f) (λ _ → ∥ B ∥-prop)  

-- Rijke instead defines a ∥_∥* as a map-extension. These definitions are 
-- equivalent definitionally.
∥_∥*-map-extension : (f : A → B) → ∥ f ∥* ≡ map-extension _ (∥ A ∥-prop) _ η-is-prop-trunc (∥ B ∥) ∥ B ∥-prop (η ∘ f) .fst 
∥_∥*-map-extension = Refl 

-- functor identity holds simply because ∥ A ∥ is a prop. 
∥—∥-id : ∥ (λ (x : A) → x) ∥* ∼ id 
∥—∥-id {A = A} x = ∥ A ∥-prop (∥ (λ (x : A) → x) ∥* x) x .center 

-- functor composition, which again holds because ∥ C ∥ is a prop.
∥—∥-∘ : (f : A → B) (g : B → C) → ∥ (g ∘ f) ∥* ∼ ∥ g ∥* ∘ ∥ f ∥*
∥—∥-∘ {C = C} f g x = ∥ C ∥-prop  _ _ .center 


--------------------------------------------------------------------------------
-- AH> Taking this a step further, we can go ahead and show that propositional
-- truncation is a monad. (I omit monad laws.)

module ∥—∥-monad where 
-- Clearly, η is the unit
  return : A → ∥ A ∥ 
  return = η 

  -- We can escape the monad if we are indeed a prop
  escape : is-prop A → ∥ A ∥ → A 
  escape prp = ∥—∥-ind′ id (λ _ → prp) 

  -- mult is simple enough to define
  mult : ∥ (∥ A ∥) ∥ → ∥ A ∥ 
  mult {A = A} = escape (∥ A ∥-prop)

  -- mult in any monad can produce a bind.
  -- (Every monad gives rise to a Kleisli category.)
  _>>=_ : ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥ 
  m >>= f = mult (∥ f ∥*  m)

  -- Example do notation.
  module _ where private 
    foobar : ∥ A ∥ → ∥ A + ¬ A ∥ 
    foobar x = do 
      y ← x 
      return (inj₁ y) 
open ∥—∥-monad 

--------------------------------------------------------------------------------
-- § 14.3 Logic in type theory
{- 
AH> This much is crucial
    > However, when the existential quantifier is interpreted by Σ-types,
      then it is not possible to express certain concepts correctly, such 
      as finiteness of a type or being in the image of map, and therefore
      we will add a second interpretation of logic in type theory, where
      logical propositions are interpreted by type theoretic propositions,
      i.e., the types of truncation level -1.
    N.b., the types of truncation level -1 means "props". Further...
    > We have seen that the propositions are closed under cartesian products,
      implication, and dependent products indexed by arbitrary types. However,
      they are not closed under coproducts, and if P is a family of propositions
      over a type A, then it not necessarily the case that Σ[ x ∈ A ](P x) is 
      a proposition.
-} 
--------------------------------------------------------------------------------
-- Def 14.3.1: disjunction.

-- Given two propositions P and Q, we define their disjunction
--  P ∨ Q ≡ ∥ P + Q ∥ 

-- AH> I am going to be a little bit loose and wild here, and not 
-- define _∨_ as a partial type constructor. Otherwise it fucks
-- with our nice infix notation... We will just have to be 
-- careful to assert that P and Q are props!
_∨_ : (P : Set ℓ₁) (Q : Set ℓ₂) → Set _ 
P ∨ Q = ∥ P + Q ∥

module _ {P : Set ℓ₁} {Q : Set ℓ₂} (p : is-prop P) (q : is-prop Q) where 

  -- Prop 14.3.2: Given P ∨ Q, then:
  -- there exists 
  --   - i : P → P ∨ Q
  --   - j : Q → P ∨ Q
  -- such that the universal property of disjunction (branching) is satisfied
  -- for any proposition R:
  --   (p ∨ Q → R) ↔ ((P → R) × (Q → R))
  left : P → P ∨ Q 
  left = η ∘ inj₁ 

  right : Q → P ∨ Q 
  right = η ∘ inj₂ 

  -- The last part of the proof is easy to describe on paper,
  -- which witnesses that (P ≃ Q) ↔ (P ↔ Q). Unfolding definitions 
  -- is a bit tricky, and is more amenable to mechanization directly.

  -- Begin by defining the elimination principle (universal property)
  -- of coproducts.
  ∨-elim : ∀ (R : Set ℓ₃) → is-prop R → 
              (P → R) → (Q → R) → 
              (P ∨ Q → R) 
  ∨-elim R r f g = ∥—∥-ind′ [ f , g ] (const r) 

  -- The proof is now straightforward, modulo some plumbing
  ∨-univ : ∀ (R : Set ℓ₃) → is-prop R → 
              (P ∨ Q → R) ↔ ((P → R) × (Q → R))
  ∨-univ R r .to f = (f ∘ left) , (f ∘ right)
  ∨-univ R r .from = uncurry (∨-elim R r)               

--------------------------------------------------------------------------------
-- Def 14.3.3: existential quantification
-- ... is defined, for family P of propositions over A, as
--   ∃[ x ∈ A ](P x) := ∥ Σ[ x ∈ A ] (P x) ∥
-- AH> Again, I am going to define this syntax without the stipulation 
--     that P be a family of props, simply to preserve nice notation.

infix 2 ∃-syntax

∃-syntax : (A : Set ℓ₁) → (A → Set ℓ₂) → Set _
∃-syntax A P = ∥ Σ[ x ∈ A ] (P x) ∥ 

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B

-- Prop 14.3.4: For family P of props over A, the quantification ∃[ x ∈ A ](P x)
-- comes equipped with a dependent function with type
--   (a : A) → (P a → ∃[ x ∈ A ] (P x))
-- and, further, for any prop Q,
--   ((∃[ x ∈ A] (P x)) → Q) ↔ ((x : A) → P x → Q)

-- AH> I omit the requirement that P be a family of propositions:
--     it should be present to correctly use ∃ notation,
--     but it isn't required for the proof.
module _ {A : Set ℓ₁} {P : A → Set ℓ₂} where 
  _,,_ : (a : A) → P a → ∃[ x ∈ A ] (P x) 
  a ,, Pa = η (a , Pa)

  -- AH> We state clearly the elimination principle
  ∃-elim : ∀ (Q : Set ℓ₃) → is-prop Q →
             (Σ A P → Q) → 
             ∃[ x ∈ A ] (P x) → Q  
  ∃-elim Q prop-Q f = ∥—∥-ind′ f (const prop-Q) 

  -- Again, the universal property is the smart constructor for ∃
  -- and its smart eliminator.
  ∃-univ : ∀ (Q : Set ℓ₃) → is-prop Q → 
           ((∃[ x ∈ A ] (P x)) → Q) ↔ ((x : A) → P x → Q)
  ∃-univ Q prop-Q .to f x Px = f (x ,, Px)
  ∃-univ Q prop-Q .from f = ∃-elim Q prop-Q (uncurry f) 

--------------------------------------------------------------------------------
-- A syntax for the other connectives

-- Truth: 
-- ⊤ = 1

-- Falsity: 
-- ⊥ = 0 

-- implication
_⇒_ : (P : Set ℓ₁) (Q : Set ℓ₂) → Set _ 
P ⇒ Q = P → Q 

-- conjunction 
_∧_ : (P : Set ℓ₁) (Q : Set ℓ₂) → Set _ 
P ∧ Q = P × Q 

-- disjunction 
-- (see above)

-- bi-implication
_⇔_ : (P : Set ℓ₁) (Q : Set ℓ₂) → Set _ 
P ⇔ Q = P ↔ Q 

-- Existentials 
-- (above)

-- Universals
infix 2 ∀-syntax
∀-syntax : (A : Set ℓ₁) → (A → Set ℓ₂) → Set _
∀-syntax A P = ∀ (x : A) → P x 
syntax ∀-syntax A (λ x → P) = ∀[ x ∈ A ] P

--------------------------------------------------------------------------------
-- AH> *Applications of logic in type theory*!

-- AH> To give a flavor of what Rijke means by "... being in the image of a map",
--     we borrow for Def 4.6.1 of the HoTT book to define surjectivity.
--     Note that this says "the fiber is inhabited", without specifying which fiber.
Surjective : (f : A → B) → Set _ 
Surjective {B = B} f = (b : B) → ∥ fib f b ∥ 

-- AH> Here is the logical axiom of choice, from the HoTT book.
-- From Book HoTT:
-- > In particular, note that the propositional truncation appears twice.
--   The truncation in the domain means we assume that for every x there 
--   exists *some* (a : A x) such that P x a, but taht these values
--   are not chosen or specified in any known way. The truncation in the codomain
--   means that we conclude there exists some function g, but this function
--   is not determined or specified in any known way.
-- 
-- AH> N.b., this axiom *must* be postulated. (It is, indeed, an axiom.)
--     Book HoTT insists, though, that X, A, and P are sets (or set families).
--     Why, I'm not sure of.  
AOC : (X : Set ℓ₁) → is-set X → 
      (A : X → Set ℓ₂) → is-set-fam A → 
      (P : (x : X) → A x → Set ℓ₃) → ((x : X) → is-set-fam (P x)) →  
      Set _ 
AOC X _ A _ P _  = 
  (∀[ x ∈ X ] (∃[ a ∈ A x ] P x a)) ⇒ 
    (∃[ g ∈ ((x : X) → A x) ] (∀[ x ∈ X ] P x (g x))) 

--------------------------------------------------------------------------------
-- § 14.4 Mapping propositional truncations into sets
-- 
-- The problem: we only know how to eliminate ∥ A ∥ to P provided P is a prop!
-- What do we do when defining a map into X s.t. X is not a set?

-- Rijke writes:
-- > One strategy is to find a type family P over X such that Σ X P is a proposition.
--   In that case, we may use the universal property of the propositional truncation
--   to obtain a map ∥ A ∥ → Σ X P from a map A → Σ X P, and then we simply
--   compose with the projection map.
-- 
-- AH> Another way put this is that we can view Σ X P as a "subset" of X,
--     where P determines which x ∈ X are in the subset. Hence we restrict
--     ourselves to just a propositional subset of X. 

module _ (X : Set ℓ₁) (P : X → Set ℓ₂) 
         (f : A → Σ X P)
         (prp : is-prop (Σ X P)) where private 

  -- This is the idea!
  map : ∥ A ∥ → X 
  map = fst ∘ toSubset 
    where 
      toSubset : ∥ A ∥ → Σ X P 
      toSubset = ∥—∥-ind′ f λ _ → prp 

--------------------------------------------------------------------------------
-- Example 14.4.1
-- Recall that a subtype P of ℕ is a predicate P for which,
-- for all x : ℕ, we have is-prop (P x). if P x is also
-- decidable for all x : ℕ, then there exists a function
-- with type:
--   ∃[ n ∈ ℕ ] (P x) → Σ[ x ∈ ℕ ] (P x).

lower-bound-irrelevant : (P : ℕ → Set ℓ) → (x : ℕ) → Irrelevant (is-lower-bound P x)
lower-bound-irrelevant P x b₁ b₂ = fun-ext _ _ (λ y → fun-ext _ _ (λ py → ≤-irrelevant (b₁ y py) (b₂ y py))) 

-- Theorem 8.3.2: The well ordering principle
-- AH> (which I did not implement!)
--     N.b. have to define this on the curried (x : ℕ) → P x → ...
--     because we can't recurse over dependent tuples.
well-ordering : {P : ℕ → Set ℓ} (sub : P ⊆ ℕ) (dec : (x : ℕ) → Decidable (P x)) → 
                (x : ℕ) → P x → Σ[ x ∈ ℕ ](P x) × is-lower-bound P x 
well-ordering sub dec zero p = 0 , p , λ _ _  → z≤n
well-ordering {P = P} sub dec (suc x) p with dec 0 
... | inj₁ p₀ = 0 , p₀ , λ _ _ → z≤n 
... | inj₂ p₁ with well-ordering {P = P ∘ suc}  (sub ∘ suc)  (dec ∘ suc) x p 
... | n , q , b = suc n , q , λ { zero pm → (⊥-elim ∘ p₁) pm
                                ; (suc m) pm → s≤s (b m pm) }

module _ {P : ℕ → Set ℓ} (sub : P ⊆ ℕ) (dec : (x : ℕ) → Decidable (P x)) where 
  
  -- The trick is to find a propositional subset of ℕ, such as this one:
  -- (The lower bounds of P).
  prop-subset : is-prop (Σ[ x ∈ ℕ ](P x) × is-lower-bound P x) 
  prop-subset = Irrelevant⇒is-prop irr 
    where 
      irr : Irrelevant (Σ[ x ∈ ℕ ] (P x) × is-lower-bound P x) 
      irr (x , p₁ , b₁) (y , p₂ , b₂) with ≤-antisym (b₁ y p₂) (b₂ x p₁) 
      ... | refl = ap (x ,_) (ap₂ _,_ (sub  x  p₁ p₂ .center) (lower-bound-irrelevant P x b₁ b₂)) 

  -- Because the codomain is a prop, we can induct over 
  --   ∃[ n ∈ ℕ ] (P n) := ∥ Σ[ x ∈ ℕ ] (P x) ∥ 
  pick₀  : ∃[ n ∈ ℕ ] (P n) → (Σ[ x ∈ ℕ ](P x) × is-lower-bound P x) 
  pick₀ = ∥—∥-ind′ (uncurry $ well-ordering sub dec) (const prop-subset)

  -- The last step is to chop off the bits we don't care about.
  -- N.b. that the codomain of pick₀ is nested to the right:
  --   (x , (p , b)) : Σ[ x ∈ ℕ ](P x) × is-lower-bound P x
  -- so we associate to the left to get
  --   ((x , p) , b) : (Σ[ x ∈ ℕ ](P x)) × is-lower-bound P x
  -- and can thereafter take its (left) projection, e.g.,
  --   (x , p) : (Σ[ x ∈ ℕ ](P x))
  pick : ∃[ n ∈ ℕ ] (P n) → Σ[ x ∈ ℕ ](P x)
  pick = fst ∘ assocˡ ∘ pick₀ 

  -- Let's pause to establish what it is we've really done:
  -- Given only the knowledge of *some* element in P ⊆ ℕ,
  -- we can pick a precise witness (n , p) ∈ P.  

--------------------------------------------------------------------------------
-- Remark 14.4.2: We say that the type A satisfies the
-- **principle of global choice** if there is a function ∥ A ∥ → A.

global-choice : (A : Set ℓ) → Set _ 
global-choice A = ∥ A ∥ → A

-- Another (trivial) example:
gc-∥_∥ : (A : Set ℓ) → global-choice (∥ A ∥) 
gc-∥ A ∥ = mult

-- Any proposition has a global choice 
prop-choice : is-prop A → global-choice A 
prop-choice prp = ∥—∥-ind′ id (λ _ → prp) 

-- AH> I think it's erroneous to write that: 
--   > the function we constructed in Ex. 14.4.1 for 
--   > decidable subtypes of ℕ is a rare case in which
--   > it is possible to obtain a function ∥ A ∥ → A.
-- simply because any constant function is a global choice.
-- (it might be better to assert ¬ (is-constant f).
const-choice : (a : A) → global-choice A 
const-choice = const  

--------------------------------------------------------------------------------
-- Maps into sets
-- 
-- AH> Here we start to circle back to the the induction principle I originally
-- proposed for propositional truncation! 
-- That is, ∥—∥-ind f is well-defined if f is **weakly constant**:
-- Def 14.4.3:
-- A map f : A → B is **weakly constant** if
--   f x ≡ f y
-- for all x, y : A.
weakly-constant : (f : A → B) → Set _
weakly-constant f = ∀ x y → f x ≡ f y 

-- a map f : A → B is constant if its homotopic to a constant function.
is-constant : (f : A → B) → Set _
is-constant {B = B} f = Σ[ b ∈ B ] (const b ∼ f)

-- Remark 14.4.4: A type A is contractible iff the identity map on A is constant;
-- A type A is a proposition iff the identity map on A is weakly constant.
constant-contr : ∀ {A : Set ℓ} → is-constant (λ (x : A) → x)  ↔ is-contr A 
constant-contr .to (a , C) = a , C 
constant-contr .from (a , C) = a , C

weakly-constant-prop : ∀ {A : Set ℓ} → weakly-constant (λ (x : A) → x) ↔ is-prop A 
weakly-constant-prop .to = Irrelevant⇒is-prop
weakly-constant-prop .from p x y = p x y .center

-- Lemma 14.4.5. If 
--   g ∘ η ∼ f 
-- then f is a weakly constant. 
weakly-constant-factors : ∀ (f : A → B) (g : ∥ A ∥ → B) → 
                            g ∘ η ∼ f → weakly-constant f 
weakly-constant-factors f g H x y = begin 
  f x ≡⟨ H x ⁻¹ ⟩ 
  (g ∘ η) x ≡⟨ ap g (α (η x) (η y)) ⟩ 
  (g ∘ η) y ≡⟨ H y ⟩ 
  f y ∎ 
  where 
    open PathReasoning

-- AH> N.b. that, as ∥—∥-ind f υ ∘ η ∼ f,
--     we have f weakly constant. But this is obvious!
--     Because υ asserts that B is a family of props.
∥—∥-weakly-constant : (f : A → B) (υ : is-prop B) → weakly-constant f 
∥—∥-weakly-constant f υ = 
  weakly-constant-factors f (∥—∥-ind′ f (λ _ → υ)) Refl 

--------------------------------------------------------------------------------
-- Thm. 14.4.6 (Kraus) let A be a type and let B be a set. Then the map
--   (∥ A ∥ → B) → Σ[ f ∈ A → B ] ((x y : A) → f x ≡ f y)
-- given g ↦ (g ∘ η , λ x y. ap g (α x y)) is an equivalence.
-- AH> N.b., error in def'n above. Corrected below and in Errata.md.

module _ {A : Set ℓ₁}  {B : Set ℓ₂} (Bₛ : is-set B) where 

  kraus : (∥ A ∥ → B) → Σ[ f ∈ (A → B) ] (weakly-constant f) 
  kraus g = (g ∘ η , λ x y → ap g (α (η x) (η y)))

  module _ ((f , eq) : Σ[ f ∈ (A → B) ] (weakly-constant f)) where 
    open PathReasoning 

    -- The strategy is to construct an inverse to krause as follows:
    --   krause⁻¹ (f , eq) = fst ∘ h
    -- with h : ∥ A ∥ → Σ[ b ∈ B ] (∥ fib f b ∥).
    -- The trick is, as described above, to:
    -- 1. Prove that p : is-prop (Σ[ b ∈ B ] (∥ fib f b ∥))
    -- 2. Construct g : A → Σ[ b ∈ B ] (∥ fib f b ∥)
    -- 3. This is sufficient to construct 
    --      h : ∥ A ∥ → Σ[ b ∈ B ] (∥ fib f b ∥) 
    --    using induction. (The image is a prop!)
    -- From there, fst ∘ h : ∥ A ∥ → B.    

    -- Step #1 
    -- ... is the trickiest. We are given b₁ and b₂, and their fibers.
    -- The crux of this proof relies on **B being a set**, which means
    -- the type family Q = const (b₁ ≡ b₂) is a prop! So we can
    -- do induction on fib₁ and fib₂. 

    f⁻¹[B]-fixed-image : ((b₁ , fib₁) (b₂ , fib₂) : (Σ[ b ∈ B ] (∥ fib f b ∥))) → b₁ ≡ b₂
    f⁻¹[B]-fixed-image (b₁ , fib₁) (b₂ , fib₂) = escape (Bₛ  b₁ b₂) (do 
        (a₁ , p₁) ← fib₁ 
        (a₂ , p₂) ← fib₂
        return (begin 
            b₁   ≡⟨ p₁ ⁻¹ ⟩ 
            f a₁ ≡⟨ eq a₁ a₂ ⟩ 
            f a₂ ≡⟨ p₂ ⟩ 
            b₂ ∎))

    -- The type is otherwise trivially irrelevant.
    f⁻¹[B]-Irrelevant : Irrelevant (Σ[ b ∈ B ] (∥ fib f b ∥))
    f⁻¹[B]-Irrelevant (b₁ , fib₁) (b₂ , fib₂) with f⁻¹[B]-fixed-image (b₁ , fib₁) (b₂ , fib₂)
    ... | refl = ap (b₁ ,_) (α fib₁ fib₂)

    -- Step #2 
    -- The handler for the point constructor
    g : A → Σ[ b ∈ B ] (∥ fib f b ∥)
    g x = (f x) , (η (x , refl)) 

    -- Step #3
    h : ∥ A ∥ → Σ[ b ∈ B ] (∥ fib f b ∥)
    h = ∥—∥-ind′ g (λ _ → Irrelevant⇒is-prop f⁻¹[B]-Irrelevant) 

    -- lastly...
    kraus⁻¹ : (∥ A ∥ → B)
    kraus⁻¹ = fst ∘ h 

  -- Now, observe that 
  --     krause (krause⁻¹ (f , eq)) 
  --   ≡ krause (fst ∘ h)
  --   ≡ (fst ∘ h ∘ η , λ x y → ap (fst ∘ h) (α (η x) (η y)))
  --   ≡ (f , λ x y → ap f (α (η x) (η y)))
  -- Because B is a set, we have 
  --     ap f (α (η x) (η y)) ≡ eq 
  -- and so:
  --   krause (krause⁻¹ (f , eq))  ≡ (f , eq)
  kraus-inv₁ : ∀ (weak-f : Σ[ f ∈ (A → B) ] (weakly-constant f)) → 
                kraus (kraus⁻¹ weak-f) ≡ weak-f 
  kraus-inv₁ (f , wk) =  
    ap (f ,_) 
      (fun-ext _ _ 
        (λ x → fun-ext _ _ (λ y → Bₛ (f x) (f y) (ap (kraus⁻¹ (f , wk)) (α (η x) (η y))) (wk x y) .center)))

  -- The other direction relies on the observation that
  -- maps of the form (g h : ∥ A ∥ → B), equipped with homotopies f ∼ g ∘ η and f ∼ h ∘ η,
  -- are necessarily the same. This is a universal property of the induction principle:
  -- recall that ∥—∥-ind f _ ∼ f ∘ η. Another way of looking at it:
  -- if we defined g and h by pattern matching, as so:
  --   g (η x) = f x 
  -- and 
  --   h (η x) = f x 
  -- then g ∼ h, as η is the only generator of ∥ A ∥.
  unique-extensions : (f : A → B) (g h : ∥ A ∥ → B) (G : g ∘ η ∼ f) (H : h ∘ η ∼ f) → g ∼ h 
  unique-extensions f g h G H = ∥—∥-ind′ {Q = λ x → g x ≡ h x} (λ a → G a ○ H a ⁻¹) (λ a → Bₛ (g a) (h a))
   
  -- In particular, letting h : ∥ A ∥ → B be arbitrary and choosing
  -- f = h ∘ η, g = kraus⁻¹ (kraus h), and h = h, we have 
  --   - G : kraus⁻¹ (kraus h) ∘ η ∼ h ∘ η 
  --   - H : h ∘ η ∼ h ∘ η 
  -- And so kraus⁻¹ (kraus h) ∼ h. 
  -- N.b. that G holds definitionally because of the computational law for ∥—∥-ind. 
  kraus-inv₂ : (h : ∥ A ∥ → B) → kraus⁻¹ (kraus h) ∼ h
  kraus-inv₂ h = unique-extensions (h ∘ η) (kraus⁻¹ (kraus h)) h Refl Refl

  -- Finally...
  kraus-equiv : is-equiv kraus 
  kraus-equiv = has-inverse⇒is-equiv (kraus⁻¹ , kraus-inv₁ , λ g → fun-ext _ _ (kraus-inv₂ g))

--------------------------------------------------------------------------------
-- AH> I'll die on this hill: there's nothing wrong with the (more accurate!)
--     recursor ∥—∥-rec. It's more general! We can replicate the Kraus theorem
--     to recover the ∥—∥-rec recursor given the Book HoTT definition, provided
--     B is a set. 
--     
module Stubborn {A : Set ℓ₁} {B : Set ℓ₂} (Bₛ : is-set B) (f : A → B) 
                (rec : ∀ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → 
                  is-prop B → Σ[ h ∈ (∥ A ∥ → B) ] (h ∘ η ∼ f)) where private 
                    
  prop-def← : (v : weakly-constant f) → Σ[ h ∈ (∥ A ∥ → B) ] (h ∘ η ∼ f)
  prop-def← v = fst ∘ h₀ , 
    (begin 
      fst ∘ (h₀ ∘ η)       ∼⟨ ap fst ∘ h₁ ⟩  
      fst ∘ (g Bₛ (f , v)) ∼⟨ (λ x → v x x) ⟩ 
      f ∎) 
    where 
      open HomReasoning
      fibers-irrelevant₁  : ((b₁ , fib₁) (b₂ , fib₂) : (Σ[ b ∈ B ] (∥ fib f b ∥))) → b₁ ≡ b₂
      fibers-irrelevant₁  (b₁ , fib₁) (b₂ , fib₂) = 
        rec {A = fib f b₁} {B = b₁ ≡ b₂} 
        (λ { (a₁ , eq₁) → rec {A = fib f b₂} {B = b₁ ≡ b₂} 
        (λ { (a₂ , eq₂) → eq₁ ⁻¹ ○ (v  a₁ a₂ ○ eq₂) }) (Bₛ b₁ b₂) .fst fib₂ }) 
        (Bₛ b₁ b₂) .fst fib₁ 

      fibers-irrelevant : Irrelevant (Σ[ b ∈ B ] (∥ fib f b ∥))
      fibers-irrelevant (b₁ , fib₁) (b₂ , fib₂) with fibers-irrelevant₁ (b₁ , fib₁) (b₂ , fib₂)
      ... | refl = ap (b₂ ,_) (α fib₁ fib₂) 

      h′  : Σ[ h ∈ (∥ A ∥ → Σ[ b ∈ B ] (∥ fib f b ∥)) ] (h ∘ η ∼ g Bₛ (f , v)) 
      h′ = rec {B = Σ[ b ∈ B ] (∥ fib f b ∥)} (g Bₛ (f , v)) (Irrelevant⇒is-prop fibers-irrelevant) 
      open Σ h′ renaming (proj₁ to h₀ ; proj₂ to h₁)
      
module Chapters.`12.Reading where

open import Prelude
open import Chapters.`01-08.Reading hiding (tr)
open import Chapters.`01-08.Exercises
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises


--------------------------------------------------------------------
-- Chapter 12: Propositions, sets and the higher truncation levels

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set
    𝐁 : A → Set

--------------------------------------------------------------------
-- § 12.1 Propositions

-- Def 12.1.1
-- A type A is a proposition if its identity types are contractible i.e

is-prop : Set → Set
is-prop A = ∀ (x y : A) → is-contr (x ≡ y)

-- given a universe 𝓤, define Prop[𝓤] to be the type of all small propositions
-- AI> I can't make this work
-- Prop[_] : Set → Set
-- Prop[ 𝓤 ] = Σ[ x ∈ 𝓤 ] is-prop x

-- Example 12.1.2
-- Any contractible type is a proposition by Exercise 10.1
-- In particular the unit type is a proposition, so is the empty type
is-prop-∅ : is-prop ∅
is-prop-∅ = λ x y → 10-1.ex-10-1 x y ((ex-falso x) , (ex-falso y))

is-prop-𝟙 : is-prop 𝟙
is-prop-𝟙 = λ {𝟙.⋆ 𝟙.⋆ → 10-1.ex-10-1 𝟙.⋆ 𝟙.⋆ (⋆ , (λ { 𝟙.⋆ → refl })) }

-- Proposition 12.1.3
-- Let A be a type, The following are equivalent
-- (i) Type A is a proposition
-- (ii) Any two terms of type A can be identified, i.e. there is a dependent function of type
--           is-prop' A := Π_{x y : A} x ≡ y
-- (iii) The type A is contractible as soon as it is inhabited, i.e., there is a function of type
--           A → is-contr A
-- (iv) the map const_⋆ : A → 𝟙 is an embedding

is-prop' : Set ℓ → Set ℓ
is-prop' A = ∀ (x y : A) → x ≡ y

module 12•1•3 {A : Set} where
-- The proof proceeds by showing (i) → (ii) → (iii) → (iv) → i

  i→ii : is-prop A → is-prop' A
  i→ii pa = λ x y → is-contr.center (pa x y)

  ii→iii : is-prop' A → (A → is-contr A)
  ii→iii pa = λ x → x , pa x

  lem : {X Y : Set} → {f : X → Y} → (X → is-emb f) → is-emb f
  lem = λ x → {!!}

  iii→iv : (A → is-contr A) → is-emb {A = A} (const 𝟙.⋆)
  iii→iv f = thm•11•4•2 (const 𝟙.⋆ , 10-3.const-tt-is-equiv {A = A} {!!})

  iv→i : is-emb {A = A} (const 𝟙.⋆) → is-prop A
  iv→i (Embed ap-equiv) = λ x y → (ap-equiv x y .proj₁ .proj₁ refl) , (λ e → {!ap-equiv x y .fst .snd!})


-- Proposition 12.1.4
-- A map f : P → Q between to propositions P and Q is an equivalence
-- if and only if there is a map g : Q → P
prop•12•1•4 : {P Q : Set} → is-prop P → is-prop Q → ((P ≃ Q) ↔ (P ↔ Q))
prop•12•1•4 {P = P} {Q = Q} prop-p prop-q =
        (λ e → e .proj₁ , e .snd .proj₁ .proj₁)
        , λ { (f , g) → f ,
               has-inverse⇒is-equiv (g , (λ x → is-contr.center (prop-q (f (g x)) (id x))) ,
                                         (λ x → is-contr.center (prop-p (g (f x)) (id x))) ) }


--------------------------------------------------------------------
-- § 12.2 Subtypes

-- There is some correspondence between proposition on types and subsets in set theory

-- Definition 12.2.1
-- A type family B over A is said to be a subtype of A if for each x : A, B x is a proposition
-- When B is a subtype of A, we also say that B x is a _property_ of x : A
is-subtype : {A : Set} → (A → Set) → Set
is-subtype {A = A} 𝐁 = ∀ (x : A) → is-prop (𝐁 x)

-- Lemma 12.2.2
-- Let A B by types, let e : A ≃ B then we have
-- is-prop A ↔ is-prop B
lem•12•2•2 : (A ≃ B) → is-prop A ↔ is-prop B
lem•12•2•2 {A = A} {B = B} e = fwd , bwk  where
  fwd : is-prop A → is-prop B
  fwd prop-A = λ x y → {!!}

  bwk : is-prop B → is-prop A
  bwk prop-B x y = {!!} where
    lem : is-contr-map (Paths.ap (fst e))
    lem = thm•10•4•6 (Paths.ap {x = x} {y = y} (e .fst)) (is-emb.ap-equiv (thm•11•4•2 e) x y)

-- Theorem 12.2.3
-- Consider a map f : A → B. The following are equivalent
-- (i) map f is an embedding
-- (ii) the fiber fib f b is a proposition for each b : B
module 12•2•3 {f : A → B} where
  i→ii : is-emb f → ((b : B) → is-prop (fib f b))
  i→ii (Embed p) b = {!!}

  ii→i : ((b : B) → is-prop (fib f b)) → is-emb f
  ii→i = {!!}


-- Corollary 12.2.4: Consider a family B of types over A. The following are equivalent
-- (i) The map pr₁ : Σ_{x : A} B x → A is an embedding
-- (ii) The type B x is a proposition for each x : A


--------------------------------------------------------------------
-- § 12.3 Sets



--------------------------------------------------------------------
-- § 12.4 General truncation levels

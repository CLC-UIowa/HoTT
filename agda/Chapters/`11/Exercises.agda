module Chapters.`11.Exercises where

open import Prelude
open import Chapters.`01-08.Reading
open import Chapters.`01-08.Exercises
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading


module 11•1a where
  -- show that the map ∅ → A is an embedding for any type A
  ex : ∅ ↪[ A ]
  ex = {!!}


module 11•1b where
  -- show that inl : A → A + B and inr : B → A + B are embeddings
  -- for any two types A and B

  ex1 : is-emb {A = A} {B = A ⊎ B} inl
  ex1 = {!!}

  ex2 : is-emb {A = B} {B = A ⊎ B} inr
  ex2 = {!!}


module 11•1c where
  -- show that inl : A → A + B is an equivalence iff B is empty
  -- show that inr : B → A + B is an equivalence iff A is empty

  ex1 : is-equiv {A = A} {B = A ⊎ B} inl ↔ (B → ∅)
  ex1 = {!!}

  ex2 : is-equiv {A = B} {B = A ⊎ B} inr ↔ (A → ∅)
  ex2 = {!!}


module 11•2 where
  -- consider an equivalence e : A ≃ B.
  -- Construct and equivalence
  -- p ↦ p̃ : (e(x) = y) ≃ x = e⁻¹(y)
  -- for every x : A and y : B, such that, the triangle (see text)
  -- commutes for every p : e (x) = y
  --


module 11•3 {A B : Set ℓ} {f g : A → B} where
  -- show that (f ∼ g) → (is-emb f ↔ is-emb g)
  -- for any f, g : A → B

  ex : (f ∼ g) → is-emb f ↔ is-emb g
  ex = {!!}

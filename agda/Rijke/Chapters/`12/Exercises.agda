module Chapters.`12.Exercises where

open import Prelude
open import Chapters.`01-08.Exercises
open import Chapters.`01-08.Reading using (Eqℕ; toEqℕ; is-decidable; _⊎_; inr; inl; has-decidable-equality; ex-falso)
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises
open import Chapters.`12.Reading


-- 12.1
-- Show that Bool is a set by applying Thm 12.3.4


-- 12.2
-- partially ordered set is defined to be a type A equipped with
-- the relation - ≤ - : A → (A → Prop_𝓊)
-- it is reflexive, transitive and antisymmetric.
-- Show that the underlying type of any poset is a set

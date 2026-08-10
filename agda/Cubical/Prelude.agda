{-# OPTIONS --cubical #-} 
module Cubical.Prelude where 

open import Agda.Primitive public

--------------------------------------------------------------------------------
-- Standard lib imports; we're careful to not import  _≡_ 

open import Data.Bool using (true ; false ; Bool ; not) public
open import Data.Product
    renaming (proj₁ to fst ; proj₂ to snd)
    using (_×_ ; Σ ; Σ-syntax ; _,_ ; <_,_> ; curry ; uncurry ; map₂ ; assocˡ ; assocʳ) public
open import Data.Sum
    using (inj₁ ; inj₂ ; [_,_])
    renaming (_⊎_ to _+_) public
open import Data.Unit using (⊤ ; tt) public
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ₚ ; tt to ttₚ) public
open import Data.Empty using (⊥ ; ⊥-elim) public
open import Data.Empty.Polymorphic renaming (⊥ to ⊥ₚ ; ⊥-elim to ⊥ₚ-elim) public
open import Data.Fin
  using (Fin ; fromℕ)
  renaming (zero to fzero ; suc to fsuc) public
open import Data.Nat using (ℕ ; suc ; zero ; _≤_ ; z≤n ; s≤s) public
open import Function hiding (_↔_ ; _↪_ ; Surjective ; _⇔_) public
open import Data.String using (String)

--------------------------------------------------------------------------------
-- # The identity type 

module Identity where 
  open import Relation.Binary using (IsEquivalence)
  open import Relation.Binary.PropositionalEquality
      using (_≡_ ; trans ; sym ; refl ; module ≡-Reasoning ; cong) public 
  open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
  open import Relation.Nullary using (¬_) public  

--------------------------------------------------------------------------------
-- # Cubical Agda 
--   - https://github.com/agda/cubical
--   - https://agda.readthedocs.io/en/latest/language/cubical.html

-- 
-- Other Resources:
-- - 1lab (paths and transport):
--   - https://amelia.how/posts/cubical-type-theory.html
--   - https://1lab.dev/1Lab.Path.html
-- - Cyril Cohen, Thierry Coquand, Simon Huber, and Andres Mörtberg. 
--   Cubical Type Theory: a constructive interpretation of the univalence axiom.
--   - https://arxiv.org/pdf/1611.02108 
-- - Thierry Coquand, Simon Huber, Anders Mörtberg. On Higher Inductive Types in Cubical Type Theory.
--   - https://arxiv.org/abs/1802.01170


module Cubical where 
  open import Cubical.Foundations.Prelude public 


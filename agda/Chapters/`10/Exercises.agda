module Chapters.`10.Exercises where 

open import Prelude 
open import Chapters.`09.Reading
open import Chapters.`10.Reading

-- open HomReasoning

-------------------------------------------------------------------------------
-- #10.1 Show that if A is contractible, then for any x, y : A the identity
-- type x ≡ y is also contractible. 

module 10-1 where 
  private
    variable
      ℓ : Level      

-------------------------------------------------------------------------------
-- #10.2 Suppose that A is a retract of B. Show that
--   is-contr(B) → is-Contr(A)

module 10-2 where 
  private
    variable
      ℓ : Level    

-------------------------------------------------------------------------------
-- #10.3 

module 10-3 where 
  private
    variable
      ℓ : Level  

  -------------------------------------------------------------------------------
  -- (a) Show that for any type A, the map const_* : A → 1 is an equivalence
  --     iff A is contractible. 

  -------------------------------------------------------------------------------
  -- (b) Apply Exercise 9.4 to show that for any map f : A → B, if any two of the
  -- three assertions 
  --   (i) A is contractible
  --   (ii) B is contractible
  --   (iii) f is an equivalence 
  -- hold, then so does the third. 

-------------------------------------------------------------------------------
-- #10.4 Show that Finₖ is not contractible for all k ≠ 1. 

module 10-4 where 
  private
    variable
      ℓ : Level  
      
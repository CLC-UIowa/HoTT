module Exercises.Ch9 where 

open import Agda.Primitive
open import Data.Bool
open import Data.Product
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum
open import Function hiding (_↔_)
open import Data.Unit 
open import Relation.Binary.PropositionalEquality

open import Part2
open Chapter9

-------------------------------------------------------------------------------
-- #9.1 
-- ...

-------------------------------------------------------------------------------
-- #9.2 
-- ...

-------------------------------------------------------------------------------
-- #9.3:

module 9-3 where 
  private
    variable
      ℓ : Level 
      A B : Set ℓ 
  
  open _↔_ public
  open HomReasoning

  -- --------------------------------------------------------------------------
  -- (a) Consider two functions f, g : A → B and a homotopy H : f ∼ g. Then
  --     is-equiv(f) ↔ is-equiv(g).
  -- AH> I prove this directly over the definition of is-equiv f (that f has
  --     both a section and retraction). Could have just-as-well used
  --     is-equiv⇒has-inverse and has-inverse⇒is-equiv to reduce the cases,
  --     but I suspect this would not be *that* much more concise.
  
  
  is-equiv↔ : (f g : A → B) (H : f ∼ g) → is-equiv f ↔ is-equiv g
  is-equiv↔ f g H .to ((r , f∘r∼id) , (l , l∘f∼id)) .fst = 
    r , (begin 
      g ∘ r ∼⟨ H ⁻¹ ·ᵣ r ⟩ 
      f ∘ r ∼⟨ f∘r∼id    ⟩ 
      id ∎)
  is-equiv↔ f g H .to ((r , f∘r∼id) , (l , l∘f∼id)) .snd = 
    l , (begin 
      l ∘ g ∼⟨ l ·ₗ H ⁻¹ ⟩ 
      l ∘ f ∼⟨ l∘f∼id    ⟩ 
      id ∎)
  is-equiv↔ f g H .from ((r , g∘r∼id) , (l , l∘g∼id)) .fst = 
    r , (begin 
      f ∘ r ∼⟨ H ·ᵣ r ⟩ 
      g ∘ r ∼⟨ g∘r∼id ⟩ 
      id ∎)
  is-equiv↔ f g H .from ((r , g∘r∼id) , (l , l∘g∼id)) .snd = 
    l , (begin 
      l ∘ f ∼⟨ l ·ₗ H ⟩ 
      l ∘ g ∼⟨ l∘g∼id ⟩ 
      id ∎)

  -- --------------------------------------------------------------------------
  -- (b) Show that for any two homotopic equivalences e₁ , e₂ : A ≃ B, their
  --     inverses are also homotopic.

  inverses-homotopic : ∀ (e₁ e₂ : A ≃ B) → {!e₁!} 
  inverses-homotopic = {!!} 
  
  



-------------------------------------------------------------------------------
-- #9.4 
-- ...

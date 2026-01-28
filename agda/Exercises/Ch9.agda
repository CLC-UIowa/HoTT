module Exercises.Ch9 where 

open import Agda.Primitive
open import Data.Bool
open import Data.Product
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.Sum
open import Function hiding (_↔_)
open import Data.Unit 
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Data.Empty
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
  --     AH> recall (1) that the inverse of an equivalence e is its section
  --         f : B → A
  --         and (2) we mean by "are also homotopic" that the sections
  --         of e₁ and e₂ are homotopically equivalent under _∼_.

  inverses-homotopic : ∀ (e₁ e₂ : A ≃ B) → `inv e₁ ∼ `inv e₂ 
  inverses-homotopic (f , (f⁻¹ , f∘f⁻¹∼id) , retr-f) (g , (g⁻¹ , g∘g⁻¹∼id) , retr-g) = {!!}

  -- Actually, this statement is not true. Consider the two distinct
  -- identifications of bools.
  𝔹⁻¹ : Bool ≃ Bool
  𝔹⁻¹ = not , ((not , neg-bool-id) , (not , neg-bool-id))
  𝔹 : Bool ≃ Bool 
  𝔹 = id , (id , refl-htpy _) , (id , refl-htpy _)

  what? : ¬ (`inv 𝔹 ∼ `inv 𝔹⁻¹)
  what? f with f true
  ... | () 

  -- I believe the author may have meant that 
  -- e₁ and e₂ are equivalences built from (resp.) f and g such that
  -- H : f ∼ g, then the sections of their equivalences are homotopic:
  sections-homotopic : (f g : A → B) (H : f ∼ g) (eq-f : is-equiv f) (eq-g : is-equiv g) → 
                        `sec eq-f ∼ `sec eq-g
  sections-homotopic f g H eqv-f@((f⁻¹ , f∘f⁻¹∼id) , (h , h∘f∼id)) ((g⁻¹ , g∘g⁻¹∼id) , retr-g) 
    with is-equiv⇒equalSplits eqv-f 
  ... | G =
    begin
      f⁻¹          ∼⟨ f⁻¹ ·ₗ refl-htpy id  ⟩ 
      f⁻¹ ∘ id     ∼⟨ f⁻¹ ·ₗ g∘g⁻¹∼id ⁻¹  ⟩ 
      f⁻¹ ∘ g ∘ g⁻¹ ∼⟨ f⁻¹ ·ₗ H ⁻¹ ·ᵣ g⁻¹ ⟩ 
      f⁻¹ ∘ f ∘ g⁻¹ ∼⟨  G ·ᵣ f ·ᵣ g⁻¹ ⟩ 
      h ∘ f ∘ g⁻¹   ∼⟨  h∘f∼id ·ᵣ g⁻¹ ⟩ 
      id ∘ g⁻¹      ∼⟨ refl-htpy _ ⟩ 
      g⁻¹ ∎ 
  
  
  



-------------------------------------------------------------------------------
-- #9.4 
-- ...

module Exercises.Ch9 where 

open import Agda.Primitive
open import Data.Bool
open import Data.Nat
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
module 9-2 where
  private
    variable
      ℓ : Level
  open _↔_ public
  open HomReasoning

  -- I'm stupid
  true-neq-false : ¬ (true ≡ false)
  true-neq-false = λ () -- okey dokey

  -- I'm stupid
  false-neq-true : ¬ (false ≡ true)
  false-neq-true = λ ()

  -- I'm stupid
  bool-neq-neg : (b : Bool) → ¬(not b ≡ b)
  bool-neq-neg false = λ ()
  bool-neq-neg true = λ ()

  const-bool-not-equiv : (b : Bool) → ¬(is-equiv (λ (x : Bool) → b))
  const-bool-not-equiv false = λ x → true-neq-false (sym ((proj₂ ∘ proj₁) x true ))
  const-bool-not-equiv true = λ x → true-neq-false ((proj₂ ∘ proj₁) x false)

  bool-not-hom-unit : ¬(Bool ≃ ⊤)
  bool-not-hom-unit h =
    let
      fh = proj₂ h
      retraction = (proj₁ ∘ proj₂) fh
      retraction-h = (proj₂ ∘ proj₂) fh 
      b = retraction tt
    in
      bool-neq-neg b (sym (retraction-h (not b)))

--  ℕ-not-equiv-Fin : (k : ℕ) → ¬(ℕ ≃ Fin k)
--  ℕ-not-equiv-Fin = ?

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
  -- 
  -- AH> I prove this directly over the definition of is-equiv f (that f has
  --     both a section and retraction). Could have just-as-well used
  --     is-equiv⇒has-inverse and has-inverse⇒is-equiv, but you would
  --     still have 4 cases to prove, so I don't think it saves work.
  
  
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
  -- 
  -- AH> recall (1) that the inverse of an equivalence e : A ≃ B is its section
  --       f : B → A,
  --     and (2) we mean by "are also homotopic" that the sections
  --     of e₁ and e₂ are homotopically equivalent under _∼_.

  inverses-homotopic : ∀ (e₁ e₂ : A ≃ B) → `inv e₁ ∼ `inv e₂ 
  inverses-homotopic (f , (f⁻¹ , f∘f⁻¹∼id) , retr-f) (g , (g⁻¹ , g∘g⁻¹∼id) , retr-g) = {!!}

  -- Actually, this statement is not true. Consider the two distinct
  -- identifications of bools.
  𝔹⁻¹ : Bool ≃ Bool
  𝔹⁻¹ = not , ((not , neg-bool-id) , (not , neg-bool-id))
  𝔹 : Bool ≃ Bool 
  𝔹 = id , (id , refl-htpy _) , (id , refl-htpy _)

  counter-example : ¬ (`inv 𝔹 ∼ `inv 𝔹⁻¹)
  counter-example f with f true
  ... | () 

  -- I believe the author may have meant that if e₁ and e₂
  -- are equivalences built from (resp.) f and g such that
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


module 9-4 where 
  private
    variable
      ℓ : Level 
      A B C X : Set ℓ 
  
  open _↔_ public
  open HomReasoning

{- ----------------------------------------------------------------------------
  Consider a commuting triangle
                  h
               A ---> B
              f \   / g   
                 v  v      
                  C  
  with H : f ∼ g ∘ h.
  (a) Suppose that the map h has a section s : B → A. 
      (i) Show that the triangle
                  s
               A <--- B
              f \   / g
                 v  v      
                  C     
          commutes (that is, g ∼ f ∘ s), and 
      (ii) that f has a section iff g has a section.
-} 
  module 9-4a 
    (f : A → C) 
    (h : A → B) 
    (g : B → C)
    (H : f ∼ g ∘ h)
    (σ : section h) where 
 
    -- equivalent to let (s , S) = σ in ...
    open Σ σ renaming (proj₁ to  s ; proj₂ to S)

    -- (i) The triangle commutes.
    I : g  ∼ f ∘ s 
    I = begin 
      g         ∼⟨ refl-htpy _ ⟩ 
      g ∘ id    ∼⟨ g ·ₗ S ⁻¹ ⟩ 
      g ∘ h ∘ s ∼⟨ H ⁻¹ ·ᵣ s ⟩ 
      f ∘ s ∎ 
    
    -- (ii) f has a section iff g has a section.
    f-section↔g-section : section f ↔ section g 
    f-section↔g-section .to (f⁻¹ , F) .fst = h ∘ f⁻¹ 
    f-section↔g-section .to (f⁻¹ , F) .snd = begin 
      g ∘ h ∘ f⁻¹ ∼⟨ H ⁻¹ ·ᵣ f⁻¹ ⟩ 
      f ∘ f⁻¹    ∼⟨ F ⟩ 
      id ∎ 
    f-section↔g-section .from (g⁻¹ , G) .fst = s ∘ g⁻¹ 
    f-section↔g-section .from (g⁻¹ , G) .snd = begin 
      f ∘ s ∘ g⁻¹ ∼⟨ I ⁻¹  ·ᵣ g⁻¹ ⟩ 
      g ∘ g⁻¹    ∼⟨ G ⟩ 
      id ∎ 

{- ----------------------------------------------------------------------------
  (b) Suppose that the map g has a retraction r : X → B. 
    (i)  Show that the triangle
           h ∼ r ∘ f 
         commutes, and 
    (ii) that f has a retraction iff h has a retraction.
-}   

  module 9-4b 
    (f : A → C) 
    (h : A → B) 
    (g : B → C)
    (H : f ∼ g ∘ h)
    (ρ : retraction g) where 

    open Σ ρ renaming (proj₁ to  r ; proj₂ to R)
    -- (i) The triangle commutes.
    I : h ∼ r ∘ f
    I = begin 
      h         ∼⟨ refl-htpy _ ⟩ 
      id ∘ h    ∼⟨ R ⁻¹ ·ᵣ h ⟩ 
      r ∘ g ∘ h   ∼⟨ r ·ₗ H ⁻¹ ⟩ 
      r ∘ f ∎ 
    
    -- (ii) f has a retraction iff h has a retraction.
    f-retraction↔h-retraction : retraction f ↔ retraction h
    f-retraction↔h-retraction .to (f⁻¹ , F) .fst = f⁻¹ ∘ g 
    f-retraction↔h-retraction .to (f⁻¹ , F) .snd = begin 
      f⁻¹ ∘ g ∘ h  ∼⟨  f⁻¹ ·ₗ H ⁻¹  ⟩ 
      f⁻¹ ∘ f    ∼⟨ F ⟩ 
      id ∎ 
    f-retraction↔h-retraction .from (h⁻¹ , H) .fst = h⁻¹ ∘ r 
    f-retraction↔h-retraction .from (h⁻¹ , H) .snd = begin 
      h⁻¹ ∘ r ∘ f ∼⟨ h⁻¹ ·ₗ I ⁻¹ ⟩ 
      h⁻¹ ∘ h   ∼⟨ H ⟩ 
      id ∎ 

{- ----------------------------------------------------------------------------
  (c) (The 3-for-2 property for equivalences.) 
    (i) Show that if any two of the functions
          f, g, h 
        are equivalences, then so is the third. 
    (ii) Conclude that any section and any retraction of an equivalence is
         again an equivalence. 
-}   

  module 9-4c 
    (f : A → C) 
    (h : A → B) 
    (g : B → C)
    (H : f ∼ g ∘ h) where 

    -- (i) ---------------------------------------------------------------------
    -- show that if any two f , g , h are equivalences, then so is the third.

    fg-equiv : is-equiv f → is-equiv g → is-equiv h 
    fg-equiv ((f⁻¹ , F) , retr-f) (sec-g , (r , G)) .fst = f⁻¹ ∘ g , 
      (begin 
        h ∘ f⁻¹ ∘ g    ∼⟨ I ·ᵣ f⁻¹ ·ᵣ g ⟩ 
        r ∘ f ∘ f⁻¹ ∘ g ∼⟨ r ·ₗ F ·ᵣ g ⟩ 
        r ∘ g ∼⟨ G ⟩ 
        id ∎)
      where 
        open 9-4b f h g H (r , G) 
    fg-equiv (sec-f , retr-f) (sec-g , retr-g) .snd = f-retraction↔h-retraction .to retr-f 
      where open 9-4b f h g H retr-g 

    fh-equiv : is-equiv f → is-equiv h → is-equiv g 
    fh-equiv (sec-f , retr-f) (sec-h , retr-h) .fst = f-section↔g-section .to sec-f
      where 
        open 9-4a f h g H sec-h 
    fh-equiv (sec-f , (f⁻¹ , F)) ((h⁻¹ , H′), retr-h) .snd = h ∘ f⁻¹ , 
      (begin 
        h ∘ f⁻¹ ∘ g       ∼⟨ h ·ₗ (f⁻¹ ·ₗ I) ⟩ 
        h ∘ f⁻¹ ∘ f ∘ h⁻¹ ∼⟨ h ·ₗ F ·ᵣ h⁻¹ ⟩ 
        h ∘ h⁻¹           ∼⟨ H′ ⟩ 
        id ∎)
      where 
        open 9-4a f h g H (h⁻¹ , H′)

    gh-equiv : is-equiv g → is-equiv h → is-equiv f 
    gh-equiv (sec-g , retr-g) (sec-h , retr-h) = 
      f-section↔g-section .from sec-g , f-retraction↔h-retraction .from retr-h 
      where 
        open 9-4a f h g H sec-h hiding (I) 
        open 9-4b f h g H retr-g hiding (I)

  -- (ii) --------------------------------------------------------------------
  -- Conclude that any section and any retraction of an equivalence is
  -- again an equivalence. 
  module 9-4c-ii (f : A → B) where 

    equivSections : (e : is-equiv f) → is-equiv (`sec e)
    equivSections e@((s , S) , (r , R)) = 
      (f , is-equiv⇒equalSplits e ·ᵣ f · R) , 
      f , S 

    equivRetractions : (e : is-equiv f) → is-equiv (`retr e) 
    equivRetractions e@((s , S) , (r , R)) = 
      (f , R) , 
      f , f ·ₗ (is-equiv⇒equalSplits e) ⁻¹ · S 



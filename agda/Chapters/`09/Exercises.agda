module Chapters.`09.Exercises where

open import Prelude hiding ([_,_] ; ind≡)
open import Chapters.`09.Reading 

-------------------------------------------------------------------------------
--- #9.1

module 9-1 where

  ind≡ : {ℓ ℓ′ : Level}
         {A : Set ℓ}
         (a : A) →                        -- 1st
         (P : (x : A) → a ≡ x → Set ℓ′) → -- 2nd
         P a refl →                       -- 3rd
         (x : A) →                        -- 4th
         (p : a ≡ x) →                    -- 5th
         P x p
  ind≡ _ _ p _ refl = p

  inv : {ℓ : Level} → {A : Set ℓ} → (x y : A) → x ≡ y → y ≡ x
  inv = λ x y p → ind≡ x (λ y x≡y → y ≡ x) refl y p

  inv-is-equiv : (A : Set) → (x y : A) → is-equiv (inv x y)
  inv-is-equiv _ x y = ((inv y x , λ p → helper x y p) , inv y x , λ p → helper y x p)
    where
    -- Note: We write "equals" in double quotes because we don't have the
    -- wherewithal to show that two functions are ≡
    --
    -- ind≡(y) is our way to say "if a property P holds for y : A, then P also
    -- holds for any x equivalent to y"
    --
    -- Suppose we want to prove inv(x, y) ∘ inv(y, x) "equals" id
    --
    -- Let P(z) be the property that inv(z, y) ∘ inv(y, z) "equals" id
    --
    -- It's easy to prove P(y), which is concretely
    -- inv(y, y) ∘ inv(y, y) "equals" id
    --
    -- We use ind≡(y) to prove P(x) when we have a proof p that shows y ≡ x
    helper : {ℓ : Level} → {A : Set ℓ} → (x y : A) → (p : y ≡ x) → inv x y (inv y x p) ≡ id p
    helper x y p = let principle = (ind≡ y)
                       motive y' p' = (inv y' y (inv y y' p') ≡ id p')
                       base-case = refl
                       what-equal = x
                       how-equal = p
                   in  principle motive base-case what-equal how-equal

    concat : {A : Set} → (x y z : A) → x ≡ y → y ≡ z → x ≡ z
    concat = λ x y z p → ind≡ x (λ y x≡y → y ≡ z → x ≡ z) id y p

    concat-has-section : {A : Set} → (x y z : A) → (p : x ≡ y) → section (concat x y z p)
    concat-has-section x y z p =
      concat y x z (inv x y p) ,
      λ (q : x ≡ z) →
        let principle = (ind≡ x)
            -- The goal is easier to prove, i.e. refl, when x and y are the same.
            motive x' p' = (concat x x' z p' (concat x' x z (inv x x' p') q) ≡ id q)
            base-case = refl
            what-equal = y
            how-equal = p
        in  principle motive base-case what-equal how-equal

    concat-has-retraction : {A : Set} → (x y z : A) → (p : x ≡ y) → retraction (concat x y z p)
    concat-has-retraction x y z p =
      concat y x z (inv x y p) ,
      λ (q : y ≡ z) → let principle = (ind≡ y)
                          -- The outer goal is easier to prove when y and z are the same.
                          motive y' q' = concat y x y' (inv x y p) (concat x y y' p q') ≡ id q'
                          inner-principle = (ind≡ x)
                          -- The inner goal (outer goal's base case) is easier to prove when x and y are the same.
                          inner-motive = (λ x' p' → concat x' x x' (inv x x' p') (concat x x' x' p' refl) ≡ id refl)
                          inner-base-case = refl
                          inner-what-equal = y
                          inner-how-equal = p
                          base-case = inner-principle inner-motive inner-base-case inner-what-equal inner-how-equal
                          what-equal = z
                          how-equal = q
                      in  principle motive base-case what-equal how-equal

    concat-is-equiv : {A : Set} → (x y z : A) → (p : x ≡ y) → is-equiv (concat x y z p)
    concat-is-equiv x y z p = concat-has-section x y z p , concat-has-retraction x y z p

    concat' : {A : Set} → (x y z : A) → (q : y ≡ z) → (p : x ≡ y) → (x ≡ z)
    concat' x y z q p =  concat x y z p q

    concat'-has-section0 : (A : Set) → (x y z : A) → (q : z ≡ y) → section (concat' x y z (inv z y q))
    concat'-has-section0 A x y z q = (concat' x z y q) , λ (p : x ≡ z) → ind≡ z ((λ z' q' → concat' x z' z (inv z z' q') (concat' x z z' q' p) ≡ id p)) (ind≡ x (λ x' p' → concat' x x' x' (inv x' x' refl) (concat' x x' x' refl p') ≡ id p') refl z p) y q

    {-
    -- Fix a type A.
    -- Fix terms x, y, z of type A.
    -- Fix a proof q that y ≡ z.
    -- We want to prove:
    --
    --     section ((concat' x y z) q)
    --
    -- We will prove the goal using transport with the type (y ≡ z) and motive (λ (q' : y ≡ z) → section ((concat' x y z) q'))
    -- We have already proved the goal when the motive is instantiated with (inv z y) ((inv y z) q).
    -- We have also proved that ((inv z y) ((inv y z) q) ≡ q).
    -- That's really all we need.
    -}
    concat'-has-section : (A : Set) → (x y z : A) → (q : y ≡ z) → section (concat' x y z q)
    concat'-has-section A x y z q = tr {_} {y ≡ z} (section ∘ (concat' x y z)) (helper z y q) (concat'-has-section0 A x y z ((inv y z) q))

    {-
    -- Fix a type A.
    -- Fix terms x, y and z : A.
    -- Fix q, a proof that y ≡ z.
    -- Recall that (concat' x y z) : (y ≡ z) → (x ≡ y) → (x ≡ z).
    -- We want to show that ((concat' x y z) q) has a retraction.
    -- This is to say that we want to create a function h : (x ≡ z) → (x ≡ y) such that:
    --
    --     ∀ p : (x ≡ y),
    --       h $ concat' x y z q p ≡ id p
    --
    -- Going off the type of h we can guess that it might be:
    --
    --     λ r : (x ≡ z),
    --       (concat x z y) r (inv y z q)
    --
    -- We need to prove that h is really a retraction:
    --
    --     (concat x z y) ((concat' x y z) q p) (inv y z q) ≡ id p
    --
    -- Will the goal typecheck if z is replaced with a fresh variable z', while q is replaced with a fresh variable q' : y ≡ z' ?
    --
    --     e0 = (concat' x y z) q' p : x ≡ z'
    --     e1 = inv y z' q' : z' ≡ y
    --     (concat x z y) e0 e1 : x ≡ y
    --
    -- Yes!  The goal will typecheck.  Induction will simplify the aforementioned goal to:
    --
    --     (concat x y y) ((concat' x y y) refl p) (inv y y refl) ≡ id p
    --
    -- The new goal necessitates another induction.  Will it typecheck if y is replaced with a fresh variable y', while p is replaced with a fresh variable p' : x ≡ y'?
    --
    --     e0 = (concat' x y' y') refl p' : x ≡ y'
    --     e1 = inv y' y' refl : y' ≡ y'
    --     (concat x y' y') e0 e1 : x ≡ y'
    --
    -- Yes, the goal will typecheck.  Moreover the resulting subgoal is trivial:
    --
    --     (concat x x x) ((concat' x x x) refl refl) (inv x x refl) ≡ id refl
    -}
    concat'-has-retraction : (A : Set) → (x y z : A) → (q : y ≡ z) → retraction (concat' x y z q)
    concat'-has-retraction A x y z q =
      (λ (r : x ≡ z) → (concat x z y) r (inv y z $ q)) ,
      λ (p : x ≡ y) →
        let lhs = y
            motive = λ z' q' → (concat x z' y) ((concat' x y z') q' p) (inv y z' q') ≡ id p
            base = concat'-has-retraction_base p
            rhs = z
            lhs≡rhs = q
        in  ind≡ lhs motive base rhs lhs≡rhs
      where
      concat'-has-retraction_base : (p : x ≡ y) → (concat x y y) ((concat' x y y) refl p) (inv y y refl) ≡ id p
      concat'-has-retraction_base p =
        let lhs = x
            motive = λ x' p' → (concat x x' x') ((concat' x x' x') refl p') (inv x' x' refl) ≡ id p'
            base = refl
            rhs = y
            lhs≡rhs = p
        in  ind≡ lhs motive base rhs lhs≡rhs

    concat'-is-equiv : (A : Set) → (x y z : A) → (q : y ≡ z) → is-equiv (concat' x y z q)
    concat'-is-equiv A x y z q = concat'-has-section A x y z q , concat'-has-retraction A x y z q

    transport-has-section0 : (ℓ : Level) → (A : Set ℓ) → (B : A → Set ℓ) → (x y : A) → (p : y ≡ x) → section (tr {ℓ} {A} B (inv y x p))
    transport-has-section0 ℓ A B x y p =
      (λ (q : B y) → tr {ℓ} {A} B p q) ,
      λ (q : B y) → let principle = (ind≡ y)
                        motive = (λ x' p' → tr {ℓ} {A} B (inv y x' p') (tr {ℓ} {A} B p' q) ≡ id q)
                        base-case = refl
                        what-equal = x
                        how-equal = p
                    in  principle motive base-case what-equal how-equal

    transport-has-section : (ℓ : Level) → (A : Set ℓ) → (B : A → Set ℓ) → (x y : A) → (p : x ≡ y) → section (tr {ℓ} {A} B p)
    transport-has-section ℓ A B x y p =
      let type_ = (x ≡ y)
          motive = (λ (p' : x ≡ y) → section (tr {ℓ} {A} B p'))
          show-for = (inv y x (inv x y p))
          what-equal = p
          how-equal = helper y x p
          proof_ = (transport-has-section0 ℓ A B x y (inv x y p))
      in  tr {ℓ} {type_} motive how-equal proof_

    transport-has-retraction : (ℓ : Level) → (A : Set ℓ) → (B : A → Set ℓ) → (x y : A) → (p : x ≡ y) → retraction (tr {ℓ} {A} B p)
    transport-has-retraction ℓ A B x y p =
      (λ (q : B y) → tr {ℓ} {A} B (inv x y p) q) ,
      λ (r : B x) →
        let principle = (ind≡ {ℓ} {ℓ} x)
            motive = (λ y' p' → tr {ℓ} {A} B (inv x y' p') (tr {ℓ} {A} B p' r) ≡ id r)
            base-case = refl
            what-equal = y
            how-equal = p
        in  principle motive base-case what-equal how-equal

    transport-is-equiv : (ℓ : Level) → (A : Set ℓ) → (B : A → Set ℓ) → (x y : A) → (p : x ≡ y) → is-equiv (tr {ℓ} {A} B p)
    transport-is-equiv ℓ A B x y p = (transport-has-section ℓ A B x y p) , transport-has-retraction ℓ A B x y p

-------------------------------------------------------------------------------
-- #9.2 
-- ...
module 9-2 where
  true-neq-false : ¬ (true ≡ false)
  true-neq-false = λ () -- okey dokey

  bool-neq-neg : (b : Bool) → ¬(not b ≡ b)
  bool-neq-neg false = λ ()
  bool-neq-neg true = λ ()

  const-bool-not-equiv : (b : Bool) → ¬(is-equiv (λ (x : Bool) → b))
  const-bool-not-equiv false = λ x → true-neq-false (sym ((snd ∘ fst) x true ))
  const-bool-not-equiv true = λ x → true-neq-false ((snd ∘ fst) x false)

  bool-not-equiv-unit : ¬(Bool ≃ ⊤)
  bool-not-equiv-unit h =
    let
      fh = snd h
      retraction = (fst ∘ snd) fh
      retraction-h = (snd ∘ snd) fh 
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
  inverses-homotopic (f , (f⁻¹ , f∘f⁻¹∼id) , retr-f) (g , (g⁻¹ , g∘g⁻¹∼id) , retr-g) = ⊥-elim wrong!
    where 
      postulate 
        wrong! : ⊥

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

-------------------------------------------------------------------------------
-- #9.5
module 9-5 where 
  private
    variable
      ℓ ℓ₁ ℓ₂ ℓ₃ : Level 
  open HomReasoning

  -- --------------------------------------------------------------------
  -- (a) Let A and B be types, and let C be a family over x : A, y : B.
  --     Construct an equivalence 
  --       Σ_{x : A} Σ_{y : B} C(x , y) ≃ Σ_{y : B} Σ_{x : A} C(x , y)

  {-
  -- We want an *equivalence* between Σ_{x : A} Σ_{y : B} C(x , y) and
  -- Σ_{y : B} Σ_{x : A} C(x , y).
  --
  -- This just means that we want a function `eqv` from the former type to the
  -- latter type such that `eqv` has both a section (a right inverse)
  -- `eqv-lt-inv` as well as a retraction `eqv-rt-inv` (a left inverse)
  --
  -- We'll proceed with the proof in a bottom-up manner.
  -- First we'll define `eqv`.
  -- Then we'll show that `eqv` has a section.
  -- Once we're through with that we'll show that `eqv` has a retraction.
  -- Finally we'll assemble the pieces to show that `eqv` is an equivalence
  -- between the given types.
  -}

  {-
  -- If we forget about the implicit type arguments, `eqv` just maps (x, (y, z))
  -- to (y, (x, z)).
  -}

  eqv : {A B : Set} →
        {C : A → B → Set} →
        (Σ[ x ∈ A ] (Σ[ y ∈ B ] (C x y))) →
        (Σ[ y ∈ B ] (Σ[ x ∈ A ] (C x y)))
  eqv x = (fst $ snd x) , (fst x , (snd $ snd x))

  {-
  -- Our intuition might tell us `eqv` ought to be its own left inverse and
  -- right inverse.  If it does, we should trust it.  Let's provide an explicit
  -- proof that `eqv` is an involution.
  -}

  eqv-is-involution : {A B : Set} → {C : A → B → Set} →
                        (y : Σ[ y ∈ B ] (Σ[ x ∈ A ] (C x y))) →
                        (eqv (eqv y)) ≡ y
  eqv-is-involution y = refl

  {-
  -- We can easily show that `eqv` its own section and retraction.  Since `eqv`
  -- has a section as well as a retraction, it must be an equivalence between
  -- the given types.
  -}

  9-5-a-goal : {A B : Set} →
               {C : A → B → Set} →
               (Σ[ x ∈ A ] (Σ[ y ∈ B ] (C x y))) ≃
               (Σ[ y ∈ B ] (Σ[ x ∈ A ] (C x y)))
  9-5-a-goal = let eqv-has-section = eqv , eqv-is-involution
                   eqv-has-retraction = eqv , eqv-is-involution
               in  eqv , (eqv-has-section , eqv-has-retraction)

  -- --------------------------------------------------------------------
  -- (b) Let A be a type and let B and C be type families over A.
  --     Construct an equivalence 
  --     (Σ_{u : Σ_{x : A} B(x)} C(pr₁(u))) ≃ (Σ_{v : Σ_{x : A} C(x)} B(pr₁(v)))

  {-
  -- This time, let S be the type Σ[ u ∈ Σ[ x ∈ A ] (B x) ] (C (fst u)).
  -- S appears to hold some x : A, a proof of (B x), and a proof of (C x).
  --
  -- Let T be the type Σ[ u ∈ Σ[ x ∈ A ] (C x) ] (B (fst u)).
  -- T also appears to hold some x : A, a proof of (C x), and a proof of (B x).
  --
  -- In a sense every element of S is a rearrangement of the components of some
  -- element of T and vice-versa.
  -}

  eqv-b : {A : Set} → {B C : A → Set} →
          Σ[ u ∈ Σ[ x ∈ A ] (B x) ] (C (fst u)) →
          Σ[ u ∈ Σ[ x ∈ A ] (C x) ] (B (fst u))
  eqv-b z = (fst (fst z) , snd z) , snd (fst z)

  {-
  -- At this point it's clear that `eqv_b` is an involution.  It follows that
  -- `eqv_b` is its own section as well as its own retraction.  Consequently it
  -- is almost trivial to show that `eqv_b` is an equivalence between S and T.
  -}

  eqv-b-is-involution : {A : Set} → {B C : A → Set} →
                        (z : Σ[ u ∈ Σ[ x ∈ A ] (B x) ] (C (fst u))) →
                        (eqv-b (eqv-b z)) ≡ z
  eqv-b-is-involution z = refl

  9-5-b-goal : {A : Set} → {B C : A → Set} →
               ((Σ[ u ∈ Σ[ x ∈ A ] (B x) ] (C (fst u))) ≃
               (Σ[ u ∈ Σ[ x ∈ A ] (C x) ] (B (fst u))))
  9-5-b-goal = let eqv-b-has-section = eqv-b , eqv-b-is-involution
                   eqv-b-has-retraction = eqv-b , eqv-b-is-involution
               in  eqv-b , (eqv-b-has-section , eqv-b-has-retraction)

-------------------------------------------------------------------------------
-- #9.6
{- 
Recall from remark 4.4.2 that coproducts have a *functorial action*, i.e.,
that for every f : A → A′ and every g : B → B′ we have a map
  f + g : (A + B) → (A′ + B′) 
-} 

module 9-6 where 
  private
    variable
      ℓ : Level 
      A A′ A′′ B B′ B′′ C C′ D D′ X Y Z : Set ℓ 
  open HomReasoning
  
  -- --------------------------------------------------------------------
  -- (a - 1) Let's set up the bifunctorial action of coproducts.
  -- 
  -- Technically we're showing that any category 𝒞 that admits coproducts
  -- (denoted by _+_) has a bifunctor _⊕_ : 𝒞 × 𝒞 → 𝒞 defined by:
  --   - A ⊕ B = A + B
  --   - f ⊕ g = [inj₁ ∘ f, inj₂ ∘ g]
  -- where inj₁ and inj₂ are canonical injections and [f, g] : A + B → C is 
  -- the unique morphism that makes the coproduct diagram commute.

  [_,_] : (f : A → C) (g : B → C) → A + B → C 
  [ f , g ] (inj₁ a) = f a 
  [ f , g ] (inj₂ b) = g b

  -- Computational laws for [_,_] stated as homotopies
  []-reduce₁ : ∀ {f : A → C} {g : B → C} → [ f , g ] ∘ inj₁ ∼ f 
  []-reduce₁ = refl-htpy _ 

  []-reduce₂ : ∀ {f : A → C} {g : B → C} → [ f , g ] ∘ inj₂ ∼ g
  []-reduce₂ = refl-htpy _ 

  -- [ g , h ] is unique up to homotopy
  []-unique : ∀ {f : A + B → C} {g : A → C} {h : B → C} → 
              g ∼ f ∘ inj₁ → h ∼ f ∘ inj₂ → [ g , h ] ∼ f 
  []-unique {f = f} {g} {h} f∘inj₁ f∘inj₂ (inj₁ a) = f∘inj₁ a
  []-unique {f = f} {g} {h} f∘inj₁ f∘inj₂ (inj₂ b) = f∘inj₂ b 

  -- η-rule for coproducts
  []-η : ∀ {f : A + B → C} → [ f ∘ inj₁ , f ∘ inj₂ ] ∼ f 
  []-η {f = f} = []-unique (refl-htpy (f ∘ inj₁)) (refl-htpy (f ∘ inj₂)) 
  
  []-η-id : [ inj₁ {A = A} , inj₂ {B = B} ] ∼ id 
  []-η-id {A = A} {B = B} = []-η {f = id}

  -- congruence over [_,_]
  ∼[_,_]∼ : ∀ {f g : A → C} {h k : B → C} → f ∼ g → h ∼ k → 
               [ f , h ] ∼ [ g , k ] 
  ∼[_,_]∼ F H = []-unique F H                 
  
  -- distributivity 
  []-distrib : ∀ (h : C → D) (f : A → C) (g : B → C) → 
                  h ∘ [ f , g ] ∼ [ h ∘ f , h ∘ g ] 
  []-distrib _ _ _ = ([]-unique (refl-htpy _) (refl-htpy _)) ⁻¹ 

  -- f ⊕ g is the unique arrow from (A + B) to (C + D)
  -- s.t. inj₁ ∘ f ∼ (f ⊕ g) ∘ inj₁  and inj₂ ∘ g ∼ (f ⊕ g) ∘ inj₂.
  _⊕_ : (f : A → C) (g : B → D) → (A + B) → (C + D) 
  (f ⊕ g) = [ inj₁ ∘ f , inj₂ ∘ g ]

  -- --------------------------------------------------------------------
  -- (a) Show that id_A + id_B ∼ id_{A + B}
  -- (Or: The coproduct bifunctor preserves identities.)

  ⊕-id : id {A = A} ⊕ id {A = B} ∼ id 
  ⊕-id = begin 
    (id ⊕ id) ∼⟨ refl-htpy _ ⟩
    [ inj₁ , inj₂ ] ∼⟨ []-η-id ⟩
    id ∎ 

  -- --------------------------------------------------------------------
  -- (b) Show that for any two pairs of composable functions
  --        f      g              h       k     
  --     A ---> B ---> C  and  X ---> Y ---> Z
  -- there is a homotopy (g ∘ f) + (k ∘ h) ∼ (g + k) ∘ (f + h).
  -- (We can compose componentwise.)

  ∘+-distribute : ∀ {f : A → B} {g : B → C} {h : X → Y} {k : Y → Z} → 
                  (g ⊕ k) ∘ (f ⊕ h) ∼ (g ∘ f) ⊕ (k ∘ h)
  ∘+-distribute {f = f} {g} {h} {k} = begin 
    (g ⊕ k) ∘ (f ⊕ h)                         ∼⟨ refl-htpy _ ⟩ 
    (g ⊕ k) ∘ [ inj₁ ∘ f , inj₂ ∘ h ]             ∼⟨ []-distrib (g ⊕ k) (inj₁ ∘ f) (inj₂ ∘ h) ⟩ 
    [ (g ⊕ k) ∘ inj₁ ∘ f , (g ⊕ k) ∘ inj₂ ∘ h ]   ∼⟨ refl-htpy _ ⟩ 
    [ ([ inj₁ ∘ g , inj₂ ∘ k ] ∘ inj₁) ∘ f , 
      ([ inj₁ ∘ g , inj₂ ∘ k ] ∘ inj₂) ∘ h ]         ∼⟨ ∼[ []-reduce₁ {g = inj₂ ∘ k}  , []-reduce₂ {f = inj₁ ∘ g} ]∼ ⟩ 
    [ inj₁ ∘ g ∘ f ,  inj₂ ∘ k ∘ h ]               ∼⟨ refl-htpy _ ⟩ 
     (g ∘ f) ⊕ (k ∘ h) ∎


  -- --------------------------------------------------------------------
  -- (c) Show that if H : f ∼ f′ and K : g ∼ g′, then there is a homotopy
  --     H + K : (f + g) ∼ (f′ + g′).
  -- (Congruence over _⊕_.)

  -- Follows simply from congruence over [_,_]
  ∼⟨_⊕_⟩∼ : ∀ {f f′ : A → C} {g g′ : B → D} → f ∼ f′ → g ∼ g′ → 
               f ⊕ g ∼ f′ ⊕ g′ 
  ∼⟨ H ⊕ K ⟩∼ = ∼[ inj₁ ·ₗ H , inj₂ ·ₗ K ]∼ 

  -- --------------------------------------------------------------------
  -- (d) Show that if both f and g are equivalences, then so is f ⊕ g.

  module _ (f : A → C) (g : B → D) (f-eqv : is-equiv f) (g-eqv : is-equiv g) where 

    ⊕-section : section (f ⊕ g) 
    ⊕-section  = 
      f⁻¹ ⊕ g⁻¹ , (begin
          (f ⊕ g) ∘ (f⁻¹ ⊕ g⁻¹) ∼⟨ ∘+-distribute ⟩ 
          (f ∘ f⁻¹) ⊕ (g ∘ g⁻¹) ∼⟨ ∼⟨ sec-f ⊕ sec-g ⟩∼ ⟩ 
          id ⊕ id               ∼⟨ ⊕-id ⟩ 
          id ∎)
      where 
        open Σ (f-eqv .fst) renaming (proj₁ to f⁻¹ ; proj₂ to sec-f)
        open Σ (g-eqv .fst) renaming (proj₁ to g⁻¹ ; proj₂ to sec-g)

    ⊕-retr : retraction (f ⊕ g) 
    ⊕-retr = f⁻¹ ⊕ g⁻¹ , (begin 
      (f⁻¹ ⊕ g⁻¹) ∘ (f ⊕ g)  ∼⟨ ∘+-distribute ⟩ 
      (f⁻¹ ∘ f) ⊕ (g⁻¹ ∘ g)  ∼⟨ ∼⟨ retr-f ⊕ retr-g ⟩∼ ⟩ 
      id ⊕ id                ∼⟨ ⊕-id ⟩ 
      id ∎)
      where 
        open Σ (f-eqv .snd) renaming (proj₁ to f⁻¹ ; proj₂ to retr-f)
        open Σ (g-eqv .snd) renaming (proj₁ to g⁻¹ ; proj₂ to retr-g)      

    ⊕-equiv : is-equiv (f ⊕ g)
    ⊕-equiv = ⊕-section , ⊕-retr

-------------------------------------------------------------------------------
-- #9.7

module 9-7 where 
  private
    variable
      ℓ : Level 
      A A′ A′′ B B′ B′′ : Set ℓ       
  open HomReasoning
  open 9-1
  open Paths

  -- --------------------------------------------------------------------
  -- (a) Construct for any two maps f : A → A′ and g : B → B′, a map
  --     f × g : A × B → A′ × B′ 
  -- (I've added _⊗_ as the recommended syntax for this definition. -Alex)

  _⊗_ : (f : A → A′) (g : B → B′) → A × B → A′ × B′ 
  (f ⊗ g) (a , b) = (f a , g b) 
  
  -- --------------------------------------------------------------------
  -- (b) Show that id_A × id_B ∼ id_{A × B}
  id-funprod : id ⊗ id ∼ id
  id-funprod = λ x → refl

  -- --------------------------------------------------------------------
  -- (c) Show that for any two pairs of composable functions
  --        f       f′               g       g′     
  --     A ---> A′ ---> A′′  and  B ---> B′ ---> B′′ 
  -- there is a homotopy (f′ ∘ f) × (g′ ∘ g) ∼ (f′ × g′) ∘ (f × g)
  comp-dist : (f : A → A′) (f′ : A′ → A′′) (g : B → B′) (g′ : B′ → B′′) →  (f′ ∘ f) ⊗ (g′ ∘ g) ∼ (f′ ⊗ g′) ∘ (f ⊗ g)
  comp-dist f f′ g g′ = λ x → refl

  -- --------------------------------------------------------------------
  -- (d) Show that if H : f ∼ f′ and K : g ∼ g′, then there is a homotopy
  --     H + K : (f × g) ∼ (f′ × g′) 
  pair-eqₗ : {a a′ : A} {b : B} (eq : a ≡ a′) → (a , b) ≡ (a′ , b)
  pair-eqₗ eq = refl

  pair-eqᵣ : {a : A} {b b′ : B} (eq : b ≡ b′) → (a , b) ≡ (a , b′)
  pair-eqᵣ eq = refl


  hom-funprodₗ : {f f′ : A → A′} {g : B → B′} (H : f ∼ f′) → (f ⊗ g) ∼ (f′ ⊗ g)
  hom-funprodₗ H = λ (a , _) → pair-eqₗ (H a)

  hom-funprod : {f : A → A′} {g g′ : B → B′} (H : g ∼ g′) → (f ⊗ g) ∼ (f ⊗ g′)
  hom-funprod K = λ (_ , b) → pair-eqᵣ (K b)

  hom-dist : (f f′ : A → A′) (g g′ : B → B′) (H : f ∼ f′) (K : g ∼ g′) → (f ⊗ g) ∼ (f′ ⊗ g′)
  hom-dist f f′ g g′ H K = 
    begin
      (f ⊗ g) ∼⟨ hom-funprodₗ H ⟩
      (f′ ⊗ g) ∼⟨ hom-funprod K ⟩
      (f′ ⊗ g′) ∎

  -- --------------------------------------------------------------------
  -- (e) Show that for any two maps f : A → A′ and g : B → B′, the following
  --     are equivalent:
  --     (i) The map f × g is an equivalence 
  --     (ii) There are functions
  --          - α : B → is-equiv f 
  --          - β : A → is-equiv g 
  funprod-fst : (f : A → A′) (g : B → B′) (x : A × B) → fst ((f ⊗ g) x) ≡ f (fst x)
  funprod-fst _ _ = λ x → refl

  funprod-snd : (f : A → A′) (g : B → B′) (x : A × B) → snd ((f ⊗ g) x) ≡ g (snd x)
  funprod-snd _ _ = λ x → refl

  is-equiv-equiv : (f : A → A′) (g : B → B′) → (is-equiv (f ⊗ g)) ↔ ((B → is-equiv f) × (A → is-equiv g))
  is-equiv-equiv f g ._↔_.to = λ equiv →
    let 
      sec = `sec equiv
      sec-h = equiv |> fst |> snd

      retr = `retr equiv
      retr-h = equiv |> snd |> snd

      -- β
      β-sec-fun b = λ a′ → (a′ , g b) |> sec |> fst 
      β-sec-rw a′ b = funprod-fst f g (sec (a′ , g b)) |> sym
      β-sec-rw2 a′ b = ap fst (sec-h (a′ , g b))
      β-sec-proof b = λ a′ → (β-sec-rw a′ b) ○ (β-sec-rw2 a′ b) ○ refl
      β-sec b = (β-sec-fun b , β-sec-proof b)

      β-retr-fun b = λ a′ → (a′ , g b) |> retr |> fst 
      β-retr-rw a b = ap fst (retr-h (a , b))
      β-retr-proof b = λ a → β-retr-rw a b ○ refl
      β-retr b = (β-retr-fun b , β-retr-proof b)

      β b = β-sec b , β-retr b

      -- α
      α-sec-fun a = λ b′ → (f a , b′) |> sec |> snd 
      α-sec-rw a b′ = funprod-snd f g (sec (f a , b′)) |> sym
      α-sec-rw2 a b′ = ap snd (sec-h (f a , b′))
      α-sec-proof a = λ b′ → α-sec-rw a b′ ○ α-sec-rw2 a b′
      α-sec a = (α-sec-fun a , α-sec-proof a)

      α-retr-fun a = λ b′ → (f a , b′) |> retr |> snd 
      α-retr-rw a b = ap snd (retr-h (a , b))
      α-retr-proof a = λ b → α-retr-rw a b ○ refl
      α-retr a = (α-retr-fun a , α-retr-proof a)

      α a = α-sec a , α-retr a
    in
      (β , α)
  -- I'm tapping out
  is-equiv-equiv f g ._↔_.from = λ x → {!   !}
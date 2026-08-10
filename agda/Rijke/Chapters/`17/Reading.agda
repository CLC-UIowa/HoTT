module Chapters.`17.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises
open import Chapters.`12.Reading
open import Chapters.`13.Reading
open import Chapters.`14.Reading
open import Chapters.`15.Reading

 
private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ι ι₁ ι₂ ι₃ : Level
    A B C : Set ℓ 
    𝐁 : A → Set ℓ

open Chapters.`10.Exercises ; open 10-5
open is-contr    

--------------------------------------------------------------------------------
-- We will need a handful of lemmas about type equivalence. 
--------------------------------------------------------------------------------
-- Congruence properties of _≃_ 
-- 1. Congruence w.r.t. Σ 
-- 2. Congruence w.r.t. _≃_ 

-- Postulated because lazy
postulate 
  -- Likewise, _≃_ is congruent over _≃_. 
  -- Not certain if this is proven elsewhere.
  cong-≃ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ι₁} {Y : Set ι₂} → 
                 A ≃ X → 
                 B ≃ Y → 
                 (A ≃ B) ≃ (X ≃ Y)   

  -- I'll need this too 
  ≃-distrib-+ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {X : Set ι₁} {Y : Set ι₂} → 
                  (A ≃ X) → (B ≃ Y) → (A + B) ≃ (X + Y)                                 

--------------------------------------------------------------------------------
-- Contractibility is closed under _×_ and _≃_ 

-- contractability and propositionality are closed under _×_ 
×-is-contr : is-contr A → is-contr B → is-contr (A × B)
×-is-contr = ×-k-type -𝟚T 

×-is-prop : is-prop A → is-prop B → is-prop (A × B) 
×-is-prop = ×-k-type (succT -𝟚T) 

--------------------------------------------------------------------------------
--   Now's as good a time as any to prove the following

↔-≃-× : (A ↔ B) ≃ ((A → B) × (B → A))
↔-≃-× = (λ { (f , g) → (f , g) })  , has-inverse⇒is-equiv ((λ (f , g) → (f , g)) , Refl , Refl) 

--------------------------------------------------------------------------------
-- The next main result is that (is-equiv f) is a prop. This is both pleasant
-- and *necessary*. 
-- - It's pleasant because it means we can equate (p₁ p₂ : A ≃ B) 
--   based solely on the first component.
-- - It's necessary because, with univalence, we want only one 
--   inhabitant of equivalence per isomorphism. For example, we have only two
--   inhabitants of (Bool ≡ Bool) because there are exactly two distinct
--   equivalences:
--   - equiv-eq (id , pf₁) : Bool ≡ Bool 
--   - equiv-eq (not , pf₂) : Bool ≡ BOol
--   because (is-equiv not) is a prop, we don't have extra identifications
--   floating around.

module _ (f : A → B) where 
  open ≃-Reasoning
--------------------------------------------------------------------------------
--   
  -- We will prove that, if f is an equivalence, then
  -- the sections/retractions of f are contractible. 
  -- The trick is to observe that the type (fib (f ∘_) id) is *almost*
  -- exactly what we need.
  --     is-contr (fib (f ∘_) id)
  --   ≡ is-contr (Σ[ g ∈ B → A ] (f ∘ g ≡ id))
  -- Unfortunately, fibers are w.r.t. equality and sections are w.r.t. homotopy:
  --   is-contr (section f) 
  -- ≡ is-contr (Σ[ g ∈ B → A ] (f ∘ g ∼ id))
  -- Fortunately, by functional extensionality, we have: 
  --   f ∘ g ≡ id ≃ f ∘ g ∼ id 
  fib-≃-section : fib (f ∘_) id ≃ section f 
  fib-≃-section = 
    fib (f ∘_) id                  ≃⟨ refl-≃ ⟩ 
    Σ[ g ∈ (B → A) ] (f ∘ g ≡ id) ≃⟨ ≃-distrib-Σ refl-≃ (λ g → eq-≃-htpy (f ∘ g) id) ⟩ 
    Σ[ g ∈ (B → A) ] (f ∘ g ∼ id) ≃⟨ refl-≃ ⟩
    section f ∎ 

  -- likewise, the fibers of precomposition are equivalent to retractions
  fib-≃-retraction : fib (_∘ f) id ≃ retraction f 
  fib-≃-retraction = 
    fib (_∘ f) id                 ≃⟨ refl-≃ ⟩ 
    Σ[ g ∈ (B → A) ] (g ∘ f ≡ id) ≃⟨ ≃-distrib-Σ refl-≃ (λ g → eq-≃-htpy (g ∘ f) id) ⟩ 
    Σ[ g ∈ (B → A) ] (g ∘ f ∼ id) ≃⟨ refl-≃ ⟩
    retraction f ∎ 

  -- Observe that f is an equivalence iff (f ∘_) is an equivalence.
  -- Since (f ∘_) is an equivalence, its fibers are contractible. Notably,
  -- we have 
  --   is-contr (fib (f ∘_) id)
  -- which we show above is equivalent to
  --  is-contr (section f). 
  section-is-contr : is-equiv f → is-contr (section f)
  section-is-contr eqv = ≃-is-contr fib-≃-section contr-fibers
    where 
      contr-fibers : is-contr (fib (f ∘_) id) 
      contr-fibers = is-equiv⇒is-contr-map (f ∘_) (post-composition-equiv f ._↔_.from eqv B) id


  retraction-is-contr : is-equiv f → is-contr (retraction f)
  retraction-is-contr eqv = ≃-is-contr fib-≃-retraction contr-fibers
    where 
      contr-fibers : is-contr (fib (_∘ f) id) 
      contr-fibers = is-equiv⇒is-contr-map (_∘ f) (is-equiv⇒Hom-equiv f eqv) id

  -- Being an equivalence is a prop.
  is-prop-is-equiv : is-prop (is-equiv f)
  is-prop-is-equiv = 
    (const⋆-embedding⇒is-prop ∘
      contractibleIfInhabited→const⋆-embedding {A = is-equiv f})
      ifInhabited 
    where
      ifInhabited : is-equiv f → is-contr (is-equiv f)
      ifInhabited eqv = ×-is-contr (section-is-contr eqv) (retraction-is-contr eqv) 

-- It immediately follows that is-equiv is a subtype of (A → B)
is-equiv-subtype : is-equiv ⊆ (A → B) 
is-equiv-subtype = is-prop-is-equiv

≃-subtype : (is-equiv ∘ fst) ⊆ (A ≃ B)
≃-subtype = is-prop-is-equiv ∘ fst 

-- Because (is-equiv f) is a prop, it's sufficient to compare
-- just the maps of given equivalences.
eq-≃ : {e₁ e₂ : A ≃ B} → (fst e₁ ≡ fst e₂) → e₁ ≡ e₂ 
eq-≃ {e₁ = e₁} {e₂}  = fst-inj is-equiv-subtype

-- sym-≃ is involutive
sym-≃-involutive : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → sym-≃ ∘ (sym-≃ {A = A} {B = B}) ∼ id
sym-≃-involutive x = eq-≃ refl 

-- Which is needed to show the following 
sym-≃² : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → (A ≃ B) ≃ (B ≃ A) 
sym-≃² = sym-≃ , has-inverse⇒is-equiv (sym-≃ , sym-≃-involutive , sym-≃-involutive) 


--------------------------------------------------------------------------------
-- Ch. 17 The Univalence Axiom
  
--------------------------------------------------------------------------------
-- §17.1 Equivalent forms of the Univalence Axiom 
-- AH> I will first characterize each equivalent form. That they are equivalent
--     follows form the fundamental theorem of identity types.

module _ {ℓ} where
  
  private
    𝒰 = Set ℓ 
    𝒰₁ = Set (lsuc ℓ)

  equiv-eq : ∀ {A B : 𝒰} → A ≡ B → A ≃ B
  equiv-eq refl = refl-≃

  -- Formulation (i): 𝒰 is univalent if equiv-eq is an equivalence.
  Univalence : 𝒰₁
  Univalence = ∀ {A B : 𝒰} → is-equiv (equiv-eq {A = A} {B})

  -- Formulation (ii)
  EquivContractible : 𝒰₁
  EquivContractible = (A : 𝒰) → is-contr (Σ[ B ∈ 𝒰 ] (A ≃ B))

  -- Formulation (iii)
  module _ (A : 𝒰) (P : (X : 𝒰) → A ≃ X → Set ℓ₃) where
    equiv-eval : ((X : 𝒰) (e : A ≃ X) → P X e) → 
                 P A refl-≃  
    equiv-eval f = f A refl-≃

    EquivInduction : Set (lsuc ℓ ⊔ ℓ₃)
    EquivInduction = section equiv-eval

  -- That these three are equivalent follows from the fundamental theorem of identity types
  module _ {A : 𝒰} (pf : IdFundProof {𝐁 = A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B})) where
    univalence-forms : IdFund {A = 𝒰} {A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B}) 
    univalence-forms = fund-thm-id A refl-≃ (λ B → equiv-eq {A = A} {B}) pf 


--------------------------------------------------------------------------------
-- Axiom 17.1.2: The univalence axiom

module _ {ℓ} where
  private
    𝒰 = Set ℓ 
    𝒰₁ = Set (lsuc ℓ)


  postulate 
    -- AH> We are postulating that all universes
    --     (Set ℓ), for any ℓ, are *univalent*.
    univalence : Univalence {ℓ} 

  -- The juicy bit
  eq-equiv : ∀ {A B : 𝒰} → A ≃ B → A ≡ B
  eq-equiv = `sec univalence  


  -- When we want to explicitly specify the equivalence
  univ : ∀ (A B : 𝒰) → (A ≡ B) ≃ (A ≃ B) 
  univ A B = (equiv-eq , univalence)

  -- A proof we can use to derive the rest of the equivalent forms
  univ-proof : ∀ {A : 𝒰} → IdFundProof {𝐁 = A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B})
  univ-proof = familyEquivalence λ _ → univalence
  
  -- The other forms
  univ-forms : IdFund {A = 𝒰} {A ≃_} A refl-≃ (λ B → equiv-eq {A = A} {B}) 
  univ-forms = univalence-forms univ-proof

  -- The total space is contractible
  equiv-contractible : EquivContractible {ℓ}
  equiv-contractible A = univ-forms .space-contractible 

  -- We have an identity system
  module _ where private 
    -- AH> Here is how we can derive EquivInduction from the fundamental theorem
    --     of identity types...
    --     However, the identity system code in Ch. 11 is not sufficiently general in its levels;
    --     in particular, we want the type family P to eliminate into an arbitrary universe (Set ι).
    --     (See below that we're forced to let P eliminate into 𝒰₁).
    --     I tried to fix the code in Chapter 11 to permit an arbitrary level for the motive P,
    --     but that's causing my Agda to hang. (??) 
    equiv-induction : (A : 𝒰) (P : (X : 𝒰) → A ≃ X → 𝒰₁) → EquivInduction A P
    equiv-induction A P = univ-forms .id-system P  
  
  -- AH> Instead, I'm going to postulate EquivInduction at arbitrary motive level.
  --     I don't see any harm in this---equiv-induction, defined above,
  --     fundamentally relies on the postulation of Univalence made above.
  postulate 
    equiv-induction : ∀ {ι} → (A : 𝒰) (P : (X : 𝒰) → A ≃ X → Set ι) → EquivInduction A P
  {- 
  
  -- But here's a rough sketch of how you'd prove it using univalence.
  equiv-induction A P = eval-equiv , {!   !} 
    where 
      eval-equiv : P A refl-≃ → (X : 𝒰) → (e : A ≃ X) → P X e 
      eval-equiv p X e with eq-equiv e 
      ... | refl = tr (P X) pf e 
        where 
          pf : e ≡ refl-≃ 
          pf = {! is-contr⇒is-prop _ (equiv-contractible X) (X , e) (X , refl-≃) .center   !} 
  -} 

--------------------------------------------------------------------------------
-- Def 17.1.3: A type X is said to be 𝒰-small if it comes equipped with an element of type:
--   is-small 𝒰 A := Σ[ X ∈ 𝒰 ] (A ≃ X).

module _ {ℓ} where
  private
    𝒰 = Set ℓ
  -- A type is 𝒰 small if it is equivalent to a 𝒰-type.
  is-small : Set ι → Set _
  is-small A = ⟨ X ∈ 𝒰 ∣ A ≃ X ⟩

  -- Similarly, a map f : A → B is said to be 𝒰-small
  -- if all of its fibers are 𝒰-small.
  is-small-map : ∀ {A : Set ι₁} {B : Set ι₂} → 
                   (f : A → B) → Set _
  is-small-map {B = B} f = ∀ (b : B) → is-small (fib f b)

  -- AH> N.b. We have to be very careful with universes.
  -- The relation 
  --   _≃_ : Set ℓ₁ → Set ℓ₂ → Set _
  -- relates different universes; the relation 
  --   _≡_ : {A : Set ℓ} → A → A → Set 
  -- homogeneously relates types in the same universe.
  -- Let me demonstrate. Below, we have
  -- - A : Set ι 
  -- - X : Set ℓ
  -- - eq : A ≃ X 
  -- but (eq-equiv eq) is ill-formed, as
  -- the type A ≡ X is ill-formed.
  -- bad : ∀ (A : Set ι) → ((X , _) : is-small A) → Set {! cong-≃ !}
  -- bad A (X , eq) = {!eq-equiv eq !}

  --------------------------------------------------------------------------------
  -- Example 17.1.4
  -- AH> Here Rijke claims some examples, which we'll prove.

  -- (1) Any type in 𝒰 is 𝒰-small.
  all-𝒰 : (A : 𝒰) → is-small A
  all-𝒰 A = A , refl-≃
  
  -- (ii) Any contractible type is 𝒰-small with respect to any universe 𝒰
  -- the idea: every contractible type is isomorphic to the unit type 
  -- (at any universe level). We've proven this fact for ⊤ at level lzero elsewhere;
  -- I'll reprove it here.
  ⊤-≃-contr : ∀ (A : Set ι) → is-contr A → A ≃ (⊤ₚ {ℓ})
  ⊤-≃-contr A (c , C) = 
    (const ttₚ , 
    has-inverse⇒is-equiv (const c , (λ { ttₚ → refl } ) , C))  

  -- Proof of (ii)
  contractible-small : ∀ (A : Set ι) → is-contr A → is-small A
  contractible-small A C = ⊤ₚ , ⊤-≃-contr A C 

  -- Stating the dual, for use elsewhere.
  ⊥-≃-is-empty : ∀ (A : Set ι) → (A → ⊥ₚ {ℓ}) → A ≃ (⊥ₚ {ℓ})
  ⊥-≃-is-empty A ¬A = ¬A , has-inverse⇒is-equiv 
    (¬A⁻¹ , (λ ()) , λ x → ⊥ₚ-elim {Whatever = λ _ → ¬A⁻¹ (¬A x) ≡ x} (¬A x) )
    where 
      ¬A⁻¹ : ⊥ₚ {ℓ} → A 
      ¬A⁻¹ () 

  -- Any empty type is 𝒰-small 
  is-empty-small : ∀ (A : Set ι) → (A → ⊥ₚ) → is-small A
  is-empty-small A ¬A = ⊥ₚ , ⊥-≃-is-empty A ¬A 

  -- (iii) For any family P of 𝒰-small types over a 𝒰-small type A, the dependent
  --       product (x : A) → B x is 𝒰-small.
  family-small : ∀ {ι₁ ι₂} → 
                   (A : Set ι₁) →
                   is-small A → 
                   (P : A → Set ι₂) → 
                   -- P is a family of 𝒰 small types
                   ((x : A) → is-small (P x)) → 
                   is-small ((x : A) → P x)
  family-small A (X , (f , eq)) P sm-P with is-equiv⇒has-inverse eq
  ... | f⁻¹ , f∘f⁻¹ , f⁻¹∘f = 
      -- I can't be bothered to prove these inverses.
      Y , (g , has-inverse⇒is-equiv (g⁻¹ , {!!} , {!!}))
      where
        Y : 𝒰 
        Y = (x : X) → sm-P (f⁻¹ x) .fst
        g : ((x : A) → P x) → Y
        g h x = sm-P (f⁻¹ x) .snd .fst (h (f⁻¹ x))

        g⁻¹ : Y → ((x : A) → P x)
        g⁻¹ h a = `inv (sm-P a .snd) (tr (fst ∘ sm-P) (f⁻¹∘f a) (h (f a)) ) 
        
  -- AH> I can't be bothered with the rest of the examples.

  --------------------------------------------------------------------------------
  -- Proposition 17.1.5: For any univalent universe 𝒰 and any type A, the type
  -- is-small 𝒰 A is a proposition.

  -- AH> I would be shocked if this isn't proven somewhere, but I can't find it.
  is-contr-≃ : ∀ (A : Set ι₁) (B : Set ι₂) → A ≃ B → is-contr A → is-contr B
  is-contr-≃ A B (f , eq) (c , C) with is-equiv⇒has-inverse eq 
  ... | f⁻¹ , f∘f⁻¹ , f⁻¹∘f  = (f c) , λ b → begin
      f c       ≡⟨ ap f (C (f⁻¹ b)) ⟩ 
      f (f⁻¹ b) ≡⟨ f∘f⁻¹ b ⟩ 
      b ∎ 
    where
      open PathReasoning

                                
  is-small-prop : ∀ (A : Set ι) → is-prop (is-small A)
  is-small-prop A = contractibleIfInhabited⇒is-prop ifInhabited
    where
      ifInhabited : is-small A → is-contr (is-small A)
      ifInhabited (X , e) = 
        is-contr-≃ 
          (is-small X) 
          (is-small A) 
          (≃-distrib-Σ refl-≃ (λ Y → cong-≃ (sym-≃ e) refl-≃)) 
          is-contr-is-small-X
        where
          is-contr-is-small-X : is-contr (is-small X)
          is-contr-is-small-X = equiv-contractible X 

  --------------------------------------------------------------------------------
  -- Corollary 17.1.6: Consider a univalent universe 𝒰 and univalent universe 𝒱 
  -- containing all types in 𝒰. Then the universe inclusion i : 𝒰 → 𝒱 is an embedding.
  -- 
  -- AH> I don't know of a good way to formalize that 𝒾 : 𝒰 → 𝒱 is an inclusion.
  --     Ch. 6 assumes a cumulative hierarchy of universes:
  --       X : 𝒰 ⊢ 𝒯(X) : 𝒰' 
  --     i.e, that if X : Set ℓ then X : Set (lsuc ℓ). 
  --     We don't have cumulativity to play with, really. (Enabling it causes Agda to loop.)
  --     We can fuck with intensional cumulativity---that is, an inclusion operator
  --       𝒾 : Set ℓ → Set (lsuc ℓ)
  --     where lift : A → 𝒾 A is an equivalence.

  module 𝒱-inclusion₁ where 
    data 𝒾 (A : Set ℓ) : Set (lsuc ℓ) where 
      lift : (x : A) → 𝒾 A 
    
    unlift : 𝒾 A → A 
    unlift (lift x) = x 

    𝒾so : ∀ {ℓ} → is-equiv (lift {ℓ})
    𝒾so = has-inverse⇒is-equiv (unlift , (λ { (lift x) → refl }) , Refl)

    module _ where 
      𝒱 = Set (lsuc ℓ) 
      
      -- "Since 𝒱 is assumed to be univalent, it follows that 
      --   fib 𝒾 A ≃ is-small A". Observe that
      --     fib 𝒾 A 
      --   ≡ Σ[ X ∈ 𝒰 ] (𝒾 X ≡ A) 
      -- and 
      --     is-small A 
      --   ≡ Σ[ X ∈ 𝒰 ] (A ≃ X) 
      -- The proof is that, by ≃-distrib-Σ, we need only prove second
      -- components are equivalent. Then:
      --   (𝒾 X ≡ A) 
      --   {by univalence}
      -- ≃ (𝒾 X ≃ A)
      --    {as 𝒾 X ≃ X}
      -- ≃ (X ≃ A) 
      --    {by symmetry}
      -- ≃ (A ≃ X)

      fib≃is-small : (A : 𝒱) → fib 𝒾 A ≃ is-small A
      fib≃is-small A = ≃-distrib-Σ refl-≃ s
        where
          𝒾-eqv : (X : 𝒰) → X ≃ 𝒾 X
          𝒾-eqv X = (lift , 𝒾so)       

          s : (X : 𝒰) → (𝒾 X ≡ A) ≃ (A ≃ X)
          s X = 
            (𝒾 X ≡ A) ≃⟨ univ (𝒾 X) A ⟩ 
            (𝒾 X ≃ A) ≃⟨ cong-≃ (sym-≃ (𝒾-eqv X)) refl-≃ ⟩ 
            (X ≃ A)   ≃⟨ sym-≃² ⟩
            (A ≃ X) ∎
            where 
              open ≃-Reasoning
      
      --  Equivalent types are the same k-types; since (is-small A) is a prop (proven above),
      -- we know that fib 𝒾 A is a prop.
      𝒾-prop-fibers : (A : 𝒱) → is-prop (fib 𝒾 A) 
      𝒾-prop-fibers A = ≃-is-prop (sym-≃ (fib≃is-small A)) (is-small-prop A) 
      
      -- Having propositional fibers is equivalent to being an embedding,
      -- completing the proof.
      𝒾-emb : is-emb 𝒾 
      𝒾-emb = prop-fibers⇒is-emb 𝒾 𝒾-prop-fibers  

  --------------------------------------------------------------------------------
  -- The only aspect of "intensional cumulativity" we really needed was
  -- that 𝒾 X ≃ X, so let's just generalize that. 

  module 𝒱-inclusion₂ 
    {ι} 
    (𝒾 : 𝒰 → Set ι) 
    (𝒾-eqv : (X : 𝒰) → X ≃ 𝒾 X) where 

    𝒱 = Set ι

    fib≃is-small : (A : 𝒱) → fib 𝒾 A ≃ is-small A
    fib≃is-small A = ≃-distrib-Σ refl-≃ (λ X → 
       (𝒾 X ≡ A)    ≃⟨ univ (𝒾 X) A ⟩ 
       (𝒾 X ≃ A) ≃⟨ cong-≃ (sym-≃ (𝒾-eqv X)) refl-≃ ⟩ 
       (X ≃ A)   ≃⟨ sym-≃² ⟩
       (A ≃ X) ∎)
      where   
        open ≃-Reasoning
    
    --  Equivalent types are the same k-types; since (is-small A) is a prop (proven above),
    -- we know that fib 𝒾 A is a prop.
    𝒾-prop-fibers : (A : 𝒱) → is-prop (fib 𝒾 A) 
    𝒾-prop-fibers A = ≃-is-prop (sym-≃ (fib≃is-small A)) (is-small-prop A) 
    
    -- Having propositional fibers is equivalent to being an embedding,
    -- completing the proof.
    𝒾-emb : is-emb 𝒾 
    𝒾-emb = prop-fibers⇒is-emb 𝒾 𝒾-prop-fibers  

  --------------------------------------------------------------------------------
  -- § 17.2 Propositional Extensionality

  --------------------------------------------------------------------------------
  -- Proposition 17.2.1: Let P be a family of propositions over 𝒰. Then
  -- the family of maps
  --   equiv-eq : A ≡ B → pr₁ A ≃ pr₁ B 
  -- where A , B : Σ[ X ∈ 𝒰 ] (P X) given by equiv-eq refl = refl-≃ is an equivalence.
  -- 

  module _ (P : 𝒰 → Set ℓ) 
           (prop-P : P ⊆ 𝒰) where

    equiv-eq′ : {A B : ⟨ X ∈ 𝒰 ∣ (P X) ⟩}  → A ≡ B → fst A ≃ fst B 
    equiv-eq′ = equiv-eq ∘ ap fst   

    -- AH> Rijke defines equiv-eq′(refl) := refl-≃.
    --     Either def'n will do! But defining it as above 
    --     makes the proof more straightforward.
    _ : ∀ {A  : ⟨ X ∈ 𝒰 ∣ (P X) ⟩} → 
          equiv-eq′ {A = A} refl ≡ refl-≃ 
    _ = refl 

    eq′-equiv : {A  B : ⟨ X ∈ 𝒰 ∣ (P X) ⟩} → fst A ≃ fst B → A ≡ B 
    eq′-equiv = fst-inj prop-P ∘ eq-equiv 
    
    fst-≃ : {A  B : ⟨ X ∈ 𝒰 ∣ (P X) ⟩} → is-equiv (equiv-eq′ {A = A} {B})
    fst-≃ {A = A} {B} = univalence ∘ₑ (fst-emb prop-P A B)

--------------------------------------------------------------------------------
-- Theorem 17.2.3 (Propositional Extensionality): 
-- the canonical map
--   iff-eq : P ≡ Q → (P ↔ Q) 
-- is an equivalence.

  module _ (P Q : 𝒰) 
           (prop-P : is-prop P) 
           (prop-Q : is-prop Q)  where 
    open _↔_
    open ≃-Reasoning

    `eq-iff : P ≡ Q → P ↔ Q 
    `eq-iff refl = (id , id) 

    -- We chain together (P ≡ Q) ≃ (P ≃ Q) ≃ (P ↔ Q).
    -- The first step is simply univalence.
    eqv-iff : (P ≃ Q) ≃ (P ↔ Q) 
    eqv-iff =  propositionalEquivalence 
                (≃-prop prop-P prop-Q) 
                (≃-is-prop 
                  (sym-≃ ↔-≃-×) 
                  (×-is-prop 
                    (prop-codomain prop-Q P) 
                    (prop-codomain prop-P Q))) .from 
                (propositionalEquivalence prop-P prop-Q)

    eq-iff : (P ≡ Q) ≃ (P ↔ Q)
    eq-iff = 
      P ≡ Q   ≃⟨ univ P Q ⟩ 
      (P ≃ Q) ≃⟨ eqv-iff ⟩ 
      (P ↔ Q) ∎ 
    
    iff→≡ : P ↔ Q → P ≡ Q 
    iff→≡ = `inv eq-iff

    -- AH> Just asserting that the chain produced by eq-iff has 
    --     the same computational content as the simpler def'n.
    δ-iff-eq : ` eq-iff ∼ `eq-iff
    δ-iff-eq refl = refl 
  --------------------------------------------------------------------------------
  -- Corollary 17.2.4:
  -- The type of decidable propositions in 𝒰 is equivalent to Bool.

  module _ where 
    open ≃-Reasoning 
    DProp : Set _ 
    DProp = ⟨ P ∈ Prop[ ℓ ] ∣ Decidable (P .fst) ⟩ 

    -- AH> Just to be clear about what DProp is
    DecidableProp : Set _
    DecidableProp = Σ[ P ∈ 𝒰 ] (is-prop P × Decidable P) 

    _ : DProp ≃ DecidableProp
    _ = (λ { ((P , prop) , dec) → (P , prop , dec) }) , 
      (has-inverse⇒is-equiv 
        ((λ { (P , prop , dec) → ((P , prop) , dec) })  , 
        Refl , 
        Refl)) 
    

    -- AH> An observation I made a while ago.
    --     We aren't going to use it...
    decProp⇒contr-or-empty : ((P , _) : DecidableProp) → (is-contr P + is-empty P)
    decProp⇒contr-or-empty = λ { (P , is-prop , is-dec) → ⊤-or-⊥ P is-prop is-dec } 

    -- The proof structure is as follows:
    -- 1. Prove that 
               
    --        DProp
    --        ⟨ P ∈ Prop[ ℓ ] ∣ Decidable (P .fst) ⟩
    --        ⟨ P ∈ Prop[ ℓ ] ∣ (P .fst) + ¬ (P .fst) ⟩
    --      ≃ ⟨ P ∈ Prop[ ℓ ] ∣ (P .fst) ⟩ + ⟨ Q ∈ Prop[ ℓ ] ∣ ¬ Q .fst ⟩
    -- 2. Prove that 
    --      ⟨ P ∈ Prop[ ℓ ] ∣ (P .fst) ⟩ and ⟨ Q ∈ Prop[ ℓ ] ∣ ¬ Q .fst ⟩ 
    --    are contractible. 
    -- 3. Since they're contractible, they're each equivalent to ⊤. 
    -- 4. Because _≃_ is congruent over _+_, we have 
    --      DProp ≃ ⊤ + ⊤ 
    -- 5. By Rijke's definition, this is Bool! By ours, we have to also
    --    prove that
    --      Bool ≃ ⊤ + ⊤ 

    -- (2) Prove contractibility
    P-contr : is-contr (⟨ P ∈ Prop[ ℓ ] ∣ (P .fst) ⟩) 
    P-contr = 
      ((⊤ₚ , is-prop-⊤ₚ) , ttₚ) , 
      (λ { ((X , prop-X) , x) → fst-inj 
        snd 
        (fst-inj 
          (λ _ → is-prop²) 
          (eq-equiv (sym-≃ (⊤-≃-contr X (is-prop⇒contractibleIfInhabited prop-X x))))) }) 
    
    ¬Q-contr : is-contr ⟨ Q ∈ Prop[ ℓ ] ∣ ¬ Q .fst ⟩
    ¬Q-contr = 
      ((⊥ₚ , is-prop-⊥ₚ) , λ ()) ,
      (λ { ((X , prop-X) , ¬X) → 
        fst-inj 
          (λ { (Y , prop-Y) → ¬P-prop Y }) 
          (fst-inj 
            (λ _ → is-prop²) 
            (eq-equiv (sym-≃ (⊥-≃-is-empty X (⊥-elim ∘ ¬X))))) })

    -- (4) Prove Bool ≃ ⊤ₚ {ℓ₁} + ⊤ₚ {ℓ₂}
    Bool≃⊤+⊤ : Bool ≃ (⊤ₚ {ℓ₁} + ⊤ₚ {ℓ₂})
    Bool≃⊤+⊤ = (λ { true → inj₁ ttₚ ; false → inj₂ ttₚ }) , 
      has-inverse⇒is-equiv 
        ((λ { (inj₁ x) → true  ; (inj₂ y) → false }) , 
        (λ { (inj₁ ttₚ) → refl
            ; (inj₂ ttₚ) → refl }) , 
        λ { false → refl
          ; true → refl })

    -- Finally, chain together the above. The first step is postulated in Ch. 9. 
    DProp≃Bool : DProp ≃ Bool 
    DProp≃Bool = 
      DProp                                                         ≃⟨ Σ-distrib-+ {A = Prop[ ℓ ]} {fst} {¬_ ∘ fst} ⟩ 
      ((⟨ P ∈ Prop[ ℓ ] ∣ (P .fst) ⟩ + ⟨ Q ∈ Prop[ ℓ ] ∣ ¬ Q .fst ⟩)) ≃⟨ ≃-distrib-+ (⊤-≃-contr _ P-contr) ((⊤-≃-contr _ ¬Q-contr)) ⟩ 
      (⊤ₚ {ℓ} + ⊤ₚ {ℓ})                                              ≃⟨ sym-≃ Bool≃⊤+⊤ ⟩ 
      Bool ∎  

  --------------------------------------------------------------------------------
  -- § 17.3 Univalence implies function extensionality 
  
  --------------------------------------------------------------------------------
  -- Lemma 17.3.1 : For any equivalence e : X ≃ Y in a univalent universe 𝒰,
  -- and any type A, the post-composition map:
  --   e ∘ — : (A → X) → (A → Y)
  -- is an equivalence. 
  
  -- AH> N.b. this is postulated in Ch. 13, and is the solution to Ex 13.12 (d).
  --     We prove it again here, because (1) it's postulated!, and (2) were we
  --     to prove it there, we would use function extensionality. So we'll avoid
  --     circularity.

  -- This proof is very subtle.
  -- The idea behind equiv-induction is that, provided a motive:
  --   P : (Y : 𝒰) → X ≃ Y → Set ι 
  -- if we can prove P X refl≃, then we know P Y e holds. 
  -- Here, we let:
  --   P Y e = is-equiv ((` e) ∘_)
  -- So now we have
  --  P X refl-≃ = is-equiv (` refl-≃) ∘_) 
  -- But (` refl≃) = id, so we must prove:
  --  is-equiv (id ∘_)
  -- where
  --  (id ∘ _) : (A → X) → (A → X)
  -- But we have
  --   id : (A → X) → A → X 
  -- and 
  --   (id ∘ _) ≡ id 
  -- so we must prove (is-equiv id), which we have already  done:
  --   is-equiv-id : ∀ {A} → is-equiv id
  -- Hence we have proven P x refl≃, and so: 
  --  P y e = is-equiv ((` e) ∘_) 
  -- holds.  
  f∘—-equivalence : {X Y : 𝒰} → (f : X → Y) (e : is-equiv f) → 
                          (A : Set ι) → is-equiv (λ (g : A → X) → f ∘ g) 
  f∘—-equivalence {X = X} {Y} f e A  = 
    equiv-induction X (λ Y e → is-equiv (_∘_ {A = A} (` e))) .fst is-equiv-id Y (f , e) 

  -- Defining the dual here because it's simple enough
  —∘f-equivalence : {X Y : 𝒰} → (f : X → Y) (e : is-equiv f) → 
                    (A : Set ι) → is-equiv (λ (g : Y → A) → g ∘ f) 
  —∘f-equivalence {X = X} {Y} f e A = equiv-induction X (λ Y e → is-equiv (λ (g : Y → A) → g ∘ (` e))) .fst is-equiv-id Y (f , e)    

  --------------------------------------------------------------------------------
  -- Thm 17.3.2 For any universe 𝒰, the univalence axiom on 𝒰 implies function 
  -- extensionality on 𝒰.

  -- We prove that univalence implies weak function extensionality, which implies function
  -- extensionality. 
  -- AH> N.b. the statement of weak function extensionality is: 
  --     ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → 
  --     ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  --   which holds ℓ₁ and A arbitrary. This statement is also true if we fix ℓ₁,
  --   but we will need to reprove it as such. In other words, weak function / strong function
  --   extensionality (as proven and postulated) are over f : A → B with A, B 
  --   from possibly different universes, but univalence is posited over a single universe
  --   𝒰. This subtlety is not a problem with cumulativity, which we work without.
  weak⇒strong-𝒰 : WeakFunctionExtensionality ℓ ℓ →
                (∀ {A : 𝒰} {B : A → 𝒰} → FunctionExtensionality {A = A} {𝐁 = B})
  weak⇒strong-𝒰 wk {A = A} {B} f = id-fund .family-equivalence
    where 
      id-fund    : IdFund f refl-∼ (htpy-eq f)
      id-fund-pf : IdFundProof f refl-∼ (htpy-eq f)

      id-fund    = fund-thm-id f refl-∼ (htpy-eq f) id-fund-pf
      id-fund-pf = spaceContractible
        (contr-codomain⇒contr-domain i 
        (wk {A = A} 
            {B = λ x → Σ-syntax (B x) λ b → f x ≡ b} 
            (λ x → (f x , refl) , λ { (_ , refl) → refl })) eqv-i)
        where 
          i : (Σ[ g ∈ ((x : A) → B x) ] (f ∼ g)) → 
              ((x : A) → Σ[ b ∈ (B x) ] (f x ≡ b))
          i (g , H) = < g , H > 

          r : ((x : A) → Σ[ b ∈ (B x) ] (f x ≡ b)) → 
              (Σ[ g ∈ ((x : A) → B x) ] (f ∼ g)) 
          r p = (fst ∘ p) , (snd ∘ p) 

          eqv-i : is-equiv i 
          eqv-i = has-inverse⇒is-equiv (r , refl-∼ , refl-∼)  
  
  
  
  wkExt : WeakFunctionExtensionality ℓ ℓ
  wkExt {A = A} {B = B} f = retract-is-contractible i (r , H) (pr₁-fibers id)
    where 
      open import Chapters.`10.Exercises
      open 10-7 using (module 10-7b) ; open 10-7b
      open 10-2

      -- Exercise 10.7b tells us that pr₁ is an equiv
      -- precisely because ((x : A) → B x) is contractible.
      pr₁ : Σ[ x ∈ A ] (B x) → A 
      pr₁ = fst 
  
      pr₁-equiv : is-equiv pr₁ 
      pr₁-equiv = ii⇒i f 
    
      pr₁∘—-equiv : is-equiv (pr₁ ∘_)
      pr₁∘—-equiv = f∘—-equivalence pr₁ pr₁-equiv A   
      
      pr₁-fibers : is-contr-map (pr₁ ∘_)
      pr₁-fibers = is-equiv⇒is-contr-map (pr₁ ∘_) pr₁∘—-equiv 

      -- We'll show that (( x : A) → B x) is a retract of fib (pr₁ ∘_) id
      -- by exhibiting H : r ∘ i ∼ id.
      -- Exercise 10.2 tells us that exhibiting a retract of a contractible
      -- type entails the retract is contractible. Namely,
      -- as (fib (pr₁ ∘_) id) is contractible, and 
      --   i : ((x : A) → B x) → fib (pr₁ ∘_) id 
      -- is a retraction, then ((x : A) → B x) is contractible.
      i : ((x : A) → B x) → fib (pr₁ ∘_) id 
      i f = (λ x → (x , f x)) , refl 

      r : fib (pr₁ ∘_) id → ((x : A) → B x)
      r (h , p) x =  tr B (htpy-eq _ _ p x) (snd (h x)) 

      H : r ∘ i ∼ id 
      H g = refl 
      
    
    -- Function extensionality now follows for universe 𝒰.
  Ext : ∀ {A : 𝒰} {B : A → 𝒰} → FunctionExtensionality {A = A} {𝐁 = B} 
  Ext = weak⇒strong-𝒰 wkExt

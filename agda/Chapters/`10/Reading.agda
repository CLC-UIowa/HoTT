module Chapters.`10.Reading where 

open import Prelude 
open import Chapters.`09.Reading

open HomReasoning
--------------------------------------------------------------------
-- Chapter 10: Contractible types and contractible maps

private
  variable 
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level 
    A B D X Y Z : Set ℓ
    𝐁 𝐂 𝐃 : A → Set ℓ 
    f g h i : (x : A) → 𝐁 x      


--------------------------------------------------------------------
-- §10.1: Contractible types

-- A type A is **contractible** if it has, in effect, exactly one
-- inhabitant. In type theory we can't straightforwardly describe
-- the size of a type, so we instead assert that there exists
-- an inhabitant equal to all other inhabitants.

record is-contr (A : Set ℓ) : Set ℓ where 
  constructor _,_ 
  field 
    center : A 
    contraction : ∀ (x : A) → center ≡ x

  -- Remark 10.1.2: the contraction C is a homotopy
  -- from the constant function to the identity.
  const∼id : const center ∼ id 
  const∼id = contraction

-- (AH: I would like to transition away from dependent pairs and towards
-- records. See: no funny business involved.) 
noFunnyBusiness : ∀ (A : Set ℓ) → is-contr A ≃ (Σ[ c ∈ A ](∀ (x : A) → c ≡ x))
noFunnyBusiness A .fst (c , cntr) = c , cntr
noFunnyBusiness A .snd .fst = (λ { (c , cntr) → c , cntr }) , (λ _ → refl)
noFunnyBusiness A .snd .snd = (λ { (c , cntr) → c , cntr }) , (λ _ → refl)

-- Example 10.1.3: The unity type is contractible

-- (the simplest proof, which relies on Agda's ηβ-normalization)
⊤-contr₁ : is-contr ⊤ 
⊤-contr₁ = tt , refl-htpy _

-- Rijke's proof, which pattern matches on x : ⊤
⊤-contr₂ : is-contr ⊤ 
⊤-contr₂ = tt , λ { tt → refl }  

-- Theorem 10.1.4: for any a : A, the type Σ_{x : A} (a ≡ x) is contractible.
-- If I'm not mistaken, this is asserting that, given a point a : A, 
-- it has exactly one path to x for all other x : A? Or, 
-- all paths from a to x contract to refl. 
thm-10∙1∙4 : ∀ (a : A) → is-contr (Σ[ x ∈ A ] (a ≡ x))
thm-10∙1∙4 {A = A} a = (a , refl) , C 
  where 
    -- using ind≡ just to be meticulous
    C : (p : Σ[ x ∈ A ] (a ≡ x)) → (a , refl) ≡ p
    C (x , eq) = ind≡ a (λ y a≡y → (a , refl) ≡ (y , a≡y)) refl x eq 

--------------------------------------------------------------------
-- §10.2: Contractible types

-- Definition 10.2.1: Let a : A. We say that A satisfies
-- **singleton induction** if for every family B over A,
-- the map:
--   ev-pt : (∀ (x : A) → 𝐁 x) → 𝐁 a 
--   ev-pt f = f a  
-- has a section. In other words, if A satisfies singleton 
-- induction, we have a function and a homotopy:
--   - ind-singₐ : 𝐁 a → ∀ (x : A) → B x 
--   - comp-singₐ : ev-pt ∘ ind-singₐ ∼ id 

record SingletonInduction {ℓ} (A : Set ℓ) : Setω where 
  constructor _,_
  field 
    𝐚 : A 

  ev-pt : ∀ {ℓ} {B : A → Set ℓ} → (∀ (x : A) → B x) → B 𝐚 
  ev-pt f = f 𝐚

  field 
    ind-sing : ∀ {ℓ} {B : A → Set ℓ} → 
                 section (ev-pt {B = B})

-- Example 10.2.2: The unit type satisfies singleton induction

⊤-SI : SingletonInduction ⊤ 
⊤-SI = tt , (λ btt tt → btt) , (refl-htpy id)

-- Theorem 10.2.3: The type A is contractible iff it satisfies
-- singleton induction.

module Contr⇒SI {ℓ} {A : Set ℓ} (cntr : is-contr A) where 
  open SingletonInduction 
  open is-contr cntr renaming (center to a ; contraction to C) 

  -- "WLOG, we may assume that C comes equipped with an 
  -- identification p : C(a) ≡ refl." If it does not,
  -- we can construct a new contraction C′ s.t.
  -- C′(a) ≡ refl:
  C′ : (x : A) → a ≡ x 
  C′ x = (! (C a)) ○ C x 

  p : C′ a ≡ refl
  p = left-inv (C a) 

  SI : SingletonInduction A 
  SI = {!   !} 
  
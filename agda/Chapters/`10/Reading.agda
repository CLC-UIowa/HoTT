module Chapters.`10.Reading where 

open import Prelude 
open import Chapters.`09.Reading

-- open HomReasoning
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

-- Example 10.1.3: The unit type is contractible

-- Rijke's proof, which pattern matches on x : ⊤
⊤-contr : is-contr ⊤ 
⊤-contr = tt , λ { tt → refl }  

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
-- §10.2: Singleton Induction

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
  constructor SingInd
  field 
    `a : A 

  -- ev-pt is the converse of an induction principle for A
  ev-pt : ∀ {ℓ} {B : A → Set ℓ} → (∀ (x : A) → B x) → B `a 
  ev-pt f = f `a

  field 
    ind-sing : ∀ {ℓ} {B : A → Set ℓ} → B `a → (∀ (x : A) → B x)
    comp-sing : ∀ {ℓ} {B : A → Set ℓ} → ev-pt {ℓ} {B} ∘ ind-sing ∼ id 

-- Example 10.2.2: The unit type satisfies singleton induction

-- Induction principle for unit type
ind⊤ : ∀ {ℓ} {B : ⊤ → Set ℓ} → B tt → (∀ (x : ⊤) → B x)
ind⊤ btt tt = btt

⊤-SI : SingletonInduction ⊤ 
⊤-SI = SingInd tt ind⊤ (refl-htpy _)
  
    

-- Theorem 10.2.3: The type A is contractible iff it satisfies
-- singleton induction.

module Contr⇒SI {ℓ} {A : Set ℓ} (cntr : is-contr A) where 
  open SingletonInduction 
  open is-contr cntr renaming (center to a ; contraction to C) 
  open PathReasoning

  -- "WLOG, we may assume that C comes equipped with an 
  -- identification p : C(a) ≡ refl." If it does not,
  -- we can construct a new contraction C′ s.t.
  -- C′(a) ≡ refl:
  C′ : (x : A) → a ≡ x 
  C′ x = (! (C a)) ○ C x 

  p : C′ a ≡ refl
  p = left-inv (C a) 

  -- Pfft 
  SI : SingletonInduction A 
  SI .`a = a
  SI .ind-sing {B = B} b x = tr B (C′ x) b
  SI .comp-sing {B = B} x = begin 
    tr B (C′ a) x ≡⟨ ap (λ o → tr B o x) p ⟩ 
    tr B refl x ≡⟨ refl ⟩ 
    x ∎ 

-- -- The other direction
module SI⇒Contr {ℓ} {A : Set ℓ} (SI : SingletonInduction A) where 
  open SingletonInduction
  Contr : is-contr A
  Contr = SI .`a ,  SI .ind-sing {B = λ x → SI .`a ≡ x} refl 

--------------------------------------------------------------------
-- §10.3: Contractible maps 

-- Def. 10.3.1: fibers

fib : (f : A → B) → (b : B) → Set _ 
fib {A = A} f b = Σ[ a ∈ A ] (f a ≡ b)

-- Def. 10.3.2

-- Eq-fib (f : A → B) 

-- Prop 10.3.3: The canonical map 
--   ((x, p) ≡ (x′ , p′)) → Eq-fib f ((x, p), (x′ , p′))
-- induced by the reflexivity of Eq-fib f is an equivalence for any
-- (x, p), (x′, p′) : fib f y.

-- Def 10.3.4: contractible maps 
-- AH> This is how the HOTT book defines is-equiv, actually. 
is-contr-map : (f : A → B) → Set _ 
is-contr-map {B = B} f = ∀ (b : B) → is-contr (fib f b) 

-- Thm 10.3.5: Any contractible map is an equivalence

--------------------------------------------------------------------
-- §10.4: Contractible maps 

-- Def 10.4.1: coherently invertible 

record is-coh-invertible (f : A → B) : Set _ where 

-- Prop 10.4.2: Any coherently invertible map has contractible fibers

coh-invertible⇒is-contr-map : ∀ (f : A → B) → is-coh-invertible f → is-contr-map f 
coh-invertible⇒is-contr-map f coh = {!   !} 

-- Def. 10.4.3: natural squares of homotopies

-- Def. 10.4.4: ... 

-- Lem 10.4.5: has-inverse f → is-coh-invertible f.

-- Thm 10.4.6: Any equivalence is a contractible map. 

-- Cor 10.4.7: for any a : A, the type Σ_{x : A} (a ≡ x) is contractible
-- AH> We already proved this in thm-10∙1∙4. 



  

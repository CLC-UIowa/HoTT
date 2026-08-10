{-# OPTIONS --prop #-} 
module Chapters.`18.WithProp where 

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises
open import Chapters.`12.Reading
open import Chapters.`13.Reading
open import Chapters.`14.Reading hiding (_⇔_)
open import Chapters.`15.Reading
open import Chapters.`17.Reading

 
private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ι ι₁ ι₂ ι₃ : Level
    A B C : Set ℓ 
    𝐁 : A → Set ℓ

--------------------------------------------------------------------------------
-- Agda's PROP 

-- Prop-is-prop : (A : Prop) → (x y : A) → x ≡ y
-- Prop-is-prop A = ? 

module PropTools where 
  infixr 5 _⇔_
  record _⇔_ (A : Prop ℓ₁) (B : Prop ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    field
      to : A → B
      from : B → A

  postulate 
    prop-ext : (P Q : Prop ℓ) → (P ⇔ Q) ≃ (P ≡ Q)
  
  iff→eq : {P Q : Prop ℓ} → (P ⇔ Q) → (P ≡ Q)
  iff→eq = ` prop-ext _ _ 

  -- Dependent products that live in prop
  data ∃-Prop {A : Set ℓ} (B : A → Prop ℓ) : Set ℓ where
    _,_ : (x : A) → B x → ∃-Prop B   

--------------------------------------------------------------------------------
-- Ch 18: Set quotients

--------------------------------------------------------------------------------
-- § 18.1 Equivalence relations and the replacement axiom

--------------------------------------------------------------------------------
-- Def 18.1.1: Equivalence relations on A.
-- 
-- AH> This encoding is sufficiently nested that things get a bit unpleasant to work with.
-- 1. The return type Prop[ ℓ ] is a pain. Now we must write, e.g., if (P : A → Prop[ ℓ ]),
--    that we have (P x .fst) instead of just P x. 
--    - This bleeds into notation... We can't write that _≈_ : A → A → Prop[ ℓ ]. 
--      We write (x ≈ y) .fst.
--    - An alternative might be to define fields:
--        R : A → A → 𝒰
--        prop-valued : ∀ (x y : A) → is-prop (R x y)
--    - Or we can use Agda's built-in prop. Let's try that. 

module WithProp {ℓ} where 
  open PropTools 
  𝒰 = Set ℓ 

  infixr 4 _∈_
  _∈_ : (x : A) (P : A → Prop) → Prop
  x ∈ P = P x 
  
  record Eq-Rel (A : Set ι) : Set (lsuc ℓ ⊔ ι) where 
    infixr 5 _≈_    
    field
      _≈_ : A → A → Prop

    field 
      ρ : (x : A) → x ≈ x
      σ : (x y : A) → x ≈ y → y ≈ x
      τ : (x y z : A) → x ≈ y → y ≈ z → x ≈ z

  -- --------------------------------------------------------------------------------
  -- Def 18.1.2: Equivalence classes     

  module _ (A : 𝒰) (rel : Eq-Rel A) where 
    open Eq-Rel rel 
      
    -- An equivalence class is a subtype P, where 
    -- There exists an element x ∈ A s.t. for all (y : A)
    -- - P y iff R x y.
    -- If you unwind the definition into set theoretic analogues, we have
    -- a subset P ⊆ A s.t. 
    --  - There exists a canonical representative x ∈ P, and
    --  - For all y ∈ A, y ∈ P iff R x y
    -- which is precisely an equivalence class: a partition on A 
    -- closed under R.
    is-equivalence-class : (P : A → Prop) → Set _ 
    is-equivalence-class P = ∃[ x ∈ A ] ∀[ y ∈ A ] ((y ∈ P) ⇔ (x ≈ y)) 

    -- This will become precisely the right infix notation as soon as 
    -- we exit the scope of this module. I.e., we will have
    --   _/_ : (A : 𝒰) → Eq-Rel A → Set _
    _/_ : Set _ 
    _/_ = Σ[ P ∈ (A → Prop) ] (is-equivalence-class P)

  -- -- The equivalence class induced by x
  [_] : (x : A) → (R : Eq-Rel A) → (A → Prop)
  [ x ] rel = _≈_ x 
    where open Eq-Rel rel 

  -- q is the canonical map from (x : A) into its equivalence class.
  -- Notably, this involves actually proving that ([ x ] R) *is*
  -- is an equivalence class
  q : {A : 𝒰} → (R : Eq-Rel A) → A → A / R 
  q {A = A} rel x = [ x ] rel , η (x , (λ y → (λ p → p) , λ p → p))

  open ∥—∥-recursor renaming (∥—∥-rec to ∥—∥-rec′) 
  -- In the other direction, if we have an equivalence class P, then
  -- there exists y ∈ P such that [ y ] rel = P.
  ⌊_⌋  : ∀ {A : 𝒰} {R : Eq-Rel A} → ((P , eq-P) : A / R) → Σ[ x ∈ A ]([ x ] R ≡ P)
  ⌊_⌋ {A = A} {R = rel} (P , eq-P) = ∥—∥-rec′ 
      body 
      -- Need to show that we're eliminating into a proposition...
      -- This doesn't seem right. Would need to prove that x ≡ y,
      -- which isn't true---x and y belong to the same equivalence class. 
      -- They aren't propositionally equal. 
      (λ { (x , r₁) (y , r₂) → {! iff→eq (r₁ y)  !} }) 
      eq-P
      where
        open Eq-Rel rel
        isProp : Irrelevant (Σ[ x ∈ A ] ([ x ] rel ≡ P))
        isProp (x , e₁) (y , e₂) = {! e₁  !} 

        body : (Σ[ x ∈ A ] ∀[ y ∈ A ] ((y ∈ P) ⇔ (x ≈ y))) → Σ[ x ∈ A ] ([ x ] rel ≡ P)
        body (x , r) = x , fun-ext _ _ λ y → iff→eq (r y) ⁻¹
      

--------------------------------------------------------------------------------
-- Proposition 18.1.3: Let R be an eqv relation, with x : A and equivalence class P.
-- Then the canonical map:
--   ([ x ] R ≡ P) → P x 
-- is an equivalence.

  module _ (A : 𝒰) 
           (rel : Eq-Rel A) 
           (x : A) 
           (P : A → Prop) 
           (eq-P : is-equivalence-class A rel P) where 
    open Eq-Rel rel 
    
    -- I'll take this to be the canonical map
    m : ([ x ] rel ≡ P) → P x
    m refl = ρ x

    -- We will prove that the total space is contractible
    -- and then use the fundamental thm of identity types for the first property.
    -- The type Σ[ P ∈ (A / rel) ] (x ∈ P .fst)
    -- says "there exists an equivalence class P of which x is a member."
    -- Contractibility states "there is just one equivalence class of which x is a member."
    tot-contr : is-contr (∃-Prop {A = A / rel} {! λ Q → x ∈ Q .fst  !})
    -- tot-contr = ((q rel x) , (ρ x)) , Contr
    --   where
    --     -- Because (λ Q → x ∈ Q .fst) is a subtype of A / rel,
    --     -- to equate (x y : (Σ[ P ∈ (A / rel) ] (x ∈ P .fst))), 
    --     -- it's sufficient to equate simply their first components.
    --     ∈-subtype : (λ Q → x ∈ Q .fst) ⊆ (A / rel)
    --     ∈-subtype (Q , eq-Q) = Q x .snd

    --     -- Note also that 
    --     --   A / rel =  Σ[ P ∈ (A → Prop[ ℓ ]) ] (is-equivalence-class P)
    --     -- where (is-equivalence-class P) is a prop! 
    --     -- So to equate (x y : A / rel), it suffices to equate just 
    --     -- their first components.
    --     A/R-subtype : is-equivalence-class A rel ⊆ (A → Prop[ ℓ ])
    --     A/R-subtype = λ _ → ∥ _ ∥-prop 

    --     Contr : (Q : Σ[ Q ∈ (A / rel) ] (x ∈ Q .fst)) → (q rel x , ρ x) ≡ Q 
    --     Contr ((Q , eq-Q) , x∈Q) =
    --       fst-inj ∈-subtype (fst-inj A/R-subtype 
    --       (∥—∥-ind′ (λ { (a′ , f) → {!q rel a′  !} }) 
    --       (λ _ → is-prop⇒is-set (prop-codomain {!!} A) (_≈_ x) Q ) eq-Q))

--   --------------------------------------------------------------------------------
--   -- AH> If we want, we can show an equivalence (below) of A // R ≅ A / R 
--   --     for R an equivalence relation.


--   -- Contrast with:
--   {- 
--   data _//_ (A : 𝒰) (R : A → A → Prop[ ℓ ]) : Set ℓ where 
--     q′ : A → A // R 
--     β : (a b : A) → a ≈ b → q′ a ≡ q′ b 
--     set-trunc : is-set (A // R)
--   -}   

--   infixr 5 _//_
--   postulate 
--     _//_ : 𝒰 → (R : A → A → Prop[ ℓ ]) → Set ℓ 
--     q′ : ∀ {A : 𝒰} {R : A → A → Prop[ ℓ ]} → A → (A // R) 
--     β : ∀ {A : 𝒰} {R : A → A → Prop[ ℓ ]} → (a b : A) → R a b .fst → q′ {A} {R} a ≡ q′ b
--     set-trunc : ∀ {A : 𝒰} {R : A → A → Prop[ ℓ ]} → is-set (A // R)
  

--   module _ (A : 𝒰) (rel : Eq-Rel A) where 
--     open Eq-Rel rel 
--     postulate 
--       —∘q : ((A // R) → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → a ≈ b → f a ≡ f b))

--     samesies :   (A // R) ≃ (A / rel) 
--     samesies = f , {!   !} 
--       where 
--         help : ∀ (a b c : A) → R a b .fst → R a c .fst ≡ R b c .fst 
--         help a b c r  = `inv (eq-iff (R a c .fst) (R b c .fst) (R a c . snd) (R b c .snd)) help₀ 
--           where 
--             help₀ : (a ≈ c) ↔ (b ≈ c)
--             help₀ ._↔_.to r₂ = τ _ _ _ (σ a b r) r₂
--             help₀ ._↔_.from r₂ = τ _ _ _ r r₂ 
--         f : A // R → A / rel 
--         f = `inv (—∘q {B = A / rel}) ((q {A} rel) , (λ a b r → fst-inj (λ _ → ∥ _ ∥-prop) (fun-ext _ _ λ x → fst-inj (λ _ → is-prop²) (help a b x r))))             

      


        

        

    

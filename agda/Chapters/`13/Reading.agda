module Chapters.`13.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading
open import Chapters.`11.Exercises
open import Chapters.`12.Reading

open import Function
--------------------------------------------------------------------------------
-- 13.1 Equivalent forms of function extensionality

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Set ℓ 
    𝐁 : A → Set ℓ

----------------------------------------
-- Proposition 13.1.1

-- We've three equivalent characterizations of the function extensionality principle.
-- AH> N.b. Rijke chooses to treat f as a module parameter, which is equivalent. I
--     prefer letting f and g both be components of the definition.
module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {𝐁 : A → Set ℓ₂} where

  htpy-eq : (f : (x : A) → 𝐁 x) (g : (x : A) → 𝐁 x) → f ≡ g → f ∼ g 
  htpy-eq f g refl = refl-∼ 
 
  -- ------------------------------
  -- 1. The *function extensionality principle* 
  -- asserts that the function htpy-eq f g is an equivalence for any g.
  FunctionExtensionality : Set _
  FunctionExtensionality = ∀ (f : (x : A) → 𝐁 x) (g : (x : A) → 𝐁 x) → is-equiv (htpy-eq f g)

  -- ------------------------------
  -- 2. The total space Σ[ g ∈ ((x : A) → 𝐁 x) ] is contractible
  HtpyContractible : (f g : (x : A) → 𝐁 x) → Set _
  HtpyContractible f g = is-contr (Σ[ g ∈ ((x : A) → 𝐁 x) ] (f ∼ g))

  -- ------------------------------
  -- 3. The principle of *homotopy induction*: 
  -- the function htpy-eval has a section. 
  --    AH> I'd like to unpack this nonsense a bit...
  --        First: "has a section" ≡ "is a retraction".
  --        A section, let's call it htpy-ind, for htpy-eval would have the type:
  --          htpy-ind : P f refl-∼ → (g : (x : A) → 𝐁 x) → (H : f ∼ g) → P g H
  --        which resembles an induction principle: show that P holds for the
  --        base case (refl-∼) and it holds for the general case.
  --        That this is a section means
  --          htpy-eval ∘ htpy-ind ∼ id 
  module _ {ℓ} (f : (x : A) → 𝐁 x) (P : (g : (x : A) → 𝐁 x) → f ∼ g → Set ℓ) where
    htpy-eval : ((g : (x : A) → 𝐁 x) → (H : f ∼ g) → P g H) → 
               P f refl-∼
    htpy-eval s = s f Refl    

    HtpyInduction : Set _
    HtpyInduction = section htpy-eval

----------------------------------------
-- A proof that the three forms above are equivalent.
-- The gist: Applying an assumption of FunctionExtensionality
-- to the fundamental theorem of identity types yields 
-- each three forms immediately. N.b. one could have just as 
-- well proven another condition of the fund. thm., but 
-- function extensionality is the condition we axiomitize.

module FunExt {ℓ₁ ℓ₂} {A : Set ℓ₁} {𝐁 : A → Set ℓ₂}
       (Fun-Ext : FunctionExtensionality {A = A} {𝐁 = 𝐁}) where
  -- AH> The straightforward use of this axiom
  fun-ext : (f g : (x : A) → 𝐁 x)  → (f ∼ g) → f ≡ g
  fun-ext f g = `sec (Fun-Ext f g)  

  -- We bundle the equivalent forms of functional extensionality
  -- by invoking the fundamental theorem of identity types.
  fun-ext-proof : (f : (x : A) → 𝐁 x) → IdFundProof {𝐁 = f ∼_} f Refl (htpy-eq f)
  fun-ext-proof f = familyEquivalence (Fun-Ext f) 

  -- All forms
  fun-ext-forms : (f : (x : A) → 𝐁 x) → IdFund f refl-∼ (htpy-eq f)
  fun-ext-forms f = fund-thm-id f refl-∼ (htpy-eq f) (fun-ext-proof f) 

  -- (ii) The total space Σ[ g ∈ (x : A) → 𝐁 x ] (f ∼ g) is contractible.
  fun-ext-HtpyContractible : ∀ (f g : (x : A) → 𝐁 x) → HtpyContractible f g
  fun-ext-HtpyContractible f g = fun-ext-forms f .space-contractible 


  -- (iii) The principle of homotopy induction
  fun-ext-induction : (f : (x : A) → 𝐁 x) (P : (g : (x : A) → 𝐁 x) → f ∼ g → Set _) → 
                      HtpyInduction f P 
  fun-ext-induction f P = fun-ext-forms f .id-system P

----------------------------------------
-- Theorem 13.1.2: The weak function extensionality principle
-- 
-- The following are equivalent:
--   (i) the function extensionality principle holds in 𝓤: 
--       for every type family B over A in 𝓤, and any
--       f, g : (x : A) → B x, the map
--         htpy-eq : (f ≡ g) → (f ∼ g)
--       is an equivalence.
--  (ii) The *weak function extensionality principle* holds in 𝓤:
--       for every type family B over A in 𝓤, one has
--       ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
-- AH> Note that this universe nonsense is present because 
--     the two statements are equivalent in *full generality* over
--     A and B. That is, we do not fix A and B when proving the bi-implication.

module _ where 
  open is-contr 
  WeakFunctionExtensionality : Setω
  WeakFunctionExtensionality = 
    ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → 
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

  -- Function extensionality (let's call it "strong") implies weak
  -- function extensionality.
  -- The gist: 
  -- Given f : ((x : A) → is-contr (B x)), we have 
  --   center ∘ f : B x 
  -- Use this as your center of contraction when proving is-contr ((x : A) → B).
  -- Now your goal is to prove (∀ g. center ∘ f ≡ g). 
  -- Applying function extensionality yields a goal of:
  --   center ∘ f ∼ g 
  -- giving us an (x : A) to work with. Since (f x) is a contraction,
  -- we have 
  --   contraction (f x) : (y : B x) → center (f x) ≡ y 
  -- so let y equal (g x) and we prove
  --  center (f x) ≡ g x 
  -- as desired. 
  strong⇒weak : (∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → 
                   FunctionExtensionality {A = A} {𝐁 = B}) → 
                 WeakFunctionExtensionality
  strong⇒weak ext f = 
    center ∘ f , 
    λ g → fun-ext (center ∘ f) g (λ x → (contraction ∘ f) x (g x))
    where open FunExt ext 

  -- Weak function extensionality implies strong.
  -- The gist:
  -- Prove the second condition of the fund. thm. of identity types:
  -- that the total space, Σ[ g ∈ (((x : A) → B x) → f ∼ g) ], is contractible.
  -- FunctionExtensionality then follows as an eqv. condition.
  weak⇒strong : WeakFunctionExtensionality → 
                (∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → FunctionExtensionality {A = A} {𝐁 = B})
  weak⇒strong wk {A = A} {B} f = id-fund .family-equivalence
    where 
      id-fund    : IdFund f refl-∼ (htpy-eq f)
      id-fund-pf : IdFundProof f refl-∼ (htpy-eq f)

      id-fund    = fund-thm-id f refl-∼ (htpy-eq f) id-fund-pf
      id-fund-pf = spaceContractible
        -- The gist:
        -- The goal is to prove:
        --   is-contr (Σ[ h ∈ ((x : A) → B x)) ] (f ∼ h))
        -- The proof is to construct an equivalence between i and r, below, so that
        -- contr-codomain⇒contr-domain may be applied to i, which shifts the goal from proving
        --   is-contr (Σ[ g ∈ (x : A) → B x ] (f ∼ g))
        -- to 
        --   is-contr ((x : A) → Σ[ b ∈ B x ] ((f x) ≡ b)). 
        -- The weak function extensionality assumption gives us this; 
        -- when applied to the right type arguments, wk has the type
        --   (x : A) → is-contr (Σ[ b ∈ B x ] (f x ≡ b))) → 
        --   is-contr ((x : A) → Σ[ b ∈ B x ] ((f x) ≡ b))
        -- The inhabitant of the argument to wk is trivial.
        (contr-codomain⇒contr-domain i (wk {A = A} {B = λ x → Σ-syntax (B x) λ b → f x ≡ b} (λ x → (f x , refl) , λ { (_ , refl) → refl })) eqv-i)
        where 
          -- AH> For insight, compare the definitions below to the axiom of choice in 13.2.1
          i : (Σ[ g ∈ ((x : A) → B x) ] (f ∼ g)) → 
              ((x : A) → Σ[ b ∈ (B x) ] (f x ≡ b))
          i (g , H) = < g , H > 

          r : ((x : A) → Σ[ b ∈ (B x) ] (f x ≡ b)) → 
              (Σ[ g ∈ ((x : A) → B x) ] (f ∼ g)) 
          r p = (fst ∘ p) , (snd ∘ p) 

          eqv-i : is-equiv i 
          eqv-i = has-inverse⇒is-equiv (r , refl-∼ , refl-∼)  

----------------------------------------
-- Axiom 13.1.3 (Function Extensionality)

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {𝐁 : A → Set ℓ₂} where
  postulate
    Fun-Ext : FunctionExtensionality {A = A} {𝐁 = 𝐁}
  open FunExt Fun-Ext public

----------------------------------------
-- Theorem 13.1.5.
-- We generalize the weak function extensionality principle to
-- the following statement:
-- For any type family B over A, one has
--   ((x : A) is-trunkₖ (B x)) → is-truncₖ ((x : A) → B x)
-- 
-- The gist:
-- - The base case is exactly the same as when we proved strong⇒weak extensionality
-- - The step case uses 
--     k-type-closed-under-equivalence : 
--       {A B : Set ℓ} → (k : 𝕋) (e : A ≃ B) → is-trunc k B → is-trunc k A.
--   Here A is (f ≡ g) and B is (f ∼ g). In other words, function extensionality lets us 
--   shift the goal from equivalence to homotopic equivalence. 
--   This then permits the invocation of the inductive hypothesis:
--     is-trunk-wk-ext k : (x : A) → is-trunc k (f x ≡ g x).
--   which can be proven given the argument 
--     i : (x : A) (a b : 𝐁 x) → (a ≡ b).
module _ where 
  open is-contr 
  is-trunk-wk-ext : ∀ k → ((x : A) → is-trunc k (𝐁 x)) → is-trunc k ((x : A) → 𝐁 x)
  is-trunk-wk-ext -𝟚T = strong⇒weak Fun-Ext
  is-trunk-wk-ext {A = A} {𝐁 = 𝐁} (succT k) i f g = 
    k-type-closed-under-equivalence k (htpy-eq f g , Fun-Ext f g) (is-trunk-wk-ext k (λ x → i x (f x) (g x)))
           
----------------------------------------
-- ¬ P is a prop for any type P. (Requires functional extensionality, as we
--  have to prove f ≡ g for f , g : P → ⊥.
-- AH> The text proves this as a consequence of Thm 13.1.5,
--     but it's simple enough to prove directly.

¬P-prop : ∀ (P : Set ℓ) → is-prop (¬ P)
¬P-prop P f g = is-trunk-wk-ext (succT -𝟚T) (λ { _ () }) f g 
  -- Irrelevant⇒is-prop (λ f g → fun-ext f g (λ p → ⊥-elim (f p)) ) f g

----------------------------------------
-- Thm 13.2.1 (Axiom of choice)

module _ (C : (x : A) → 𝐁 x → Set ℓ) where 
  choice : ((x : A) → (Σ[ y ∈ 𝐁 x ] (C x y))) →  
           Σ[ f ∈ ((x : A) → 𝐁 x) ] ((x : A) → C x (f x))
  choice h = fst ∘ h , snd ∘ h

  choice⁻¹ : (Σ[ f ∈ ((x : A) → 𝐁 x) ] ((x : A) → C x (f x))) → 
             (x : A) → (Σ[ y ∈ 𝐁 x ] (C x y))
  choice⁻¹ (f , h) =  < f , h >

  choice-equiv : is-equiv choice
  choice-equiv = has-inverse⇒is-equiv (choice⁻¹ , refl-∼ , refl-∼)

----------------------------------------
-- Corollary 13.2.2:
-- For any two types A and B, and any type family C over B,
-- we have an equivalence:
--   (A → Σ[ y ∈ B ] (C y)) ≃ (Σ[ f ∈ A → B ] ((x : A) → C (f x)))

ΠΣ-distr : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {C : B → Set ℓ₃} → 
          (A → Σ[ y ∈ B ] (C y)) ≃ (Σ[ f ∈ (A → B) ] ((x : A) → C (f x)))
ΠΣ-distr {A = A} {B} {C} = (choice (λ _ → C)) , (choice-equiv (λ _ → C))


-- another direct consequence:
-- A function that chooses fibers of f is equivalent to 
-- a section of f.
fib-distrib : ∀ (f : A → B) → ((b : B) → fib f b) ≃ (Σ[ g ∈ (B → A) ] (f ∘ g ∼ id))
fib-distrib f = (choice (λ y x → f x ≡ y)) , choice-equiv _ 

----------------------------------------
-- Corollary 13.2.3: For a type family B over A, and the projection map
--   fst : (Σ[ x ∈ A ] (B x)) → A 
-- we have an equivalence 
--   sec(fst) ≃ (x : A) → B x 

module _ where 
  open ≃-Reasoning
  fst-sec : 
    section (fst {A = A} {B = 𝐁}) ≃ (∀ (x : A) → 𝐁 x)
  fst-sec {A = A} {𝐁 = 𝐁} = begin 
    -- AH> I don't follow how this step follows from 13.2.1.
    -- I can't be arsed with this proof.
    section fst ≃⟨ ({!    !} , {!   !}) ⟩ 
    (Σ[ p ∈ (Σ[ f ∈ (A → A) ] ((x : A) → 𝐁 (f x))) ] (fst p ∼ id)) ≃⟨ {!   !} ⟩
    {!   !} ∎ 


----------------------------------------
-- Theorem 13.2.4. Blah blah identity system.
-- SKIP

--------------------------------------------------------------------------------
-- § 13.3: Universal Properties
-- TODO:
--   - Mechanize univ. property of Σ types, id  types, 

----------------------------------------
-- The universal property of Σ types



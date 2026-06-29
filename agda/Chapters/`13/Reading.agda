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
    A B : Set ℓ 
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
--
-- Universal properties are "characterizations of all maps out of or 
-- into a given type". Among other applications, universal properties characterize
-- a type up to equivalence. 

--------------------------------------------------------------------------------
-- The universal property of Σ types
-- =============================================================================
--------------------------------------------------------------------------------
-- Thm. 13.3.1
-- 
-- Let B be a type family over A, and let C be a type family over Σ[ x ∈ A ] (B x).
-- Then the map:

ev-pair : ∀ {ℓ} {C : (Σ A 𝐁) → Set ℓ} → 
          (∀ (z : Σ A 𝐁) → C z) → 
          ((x : A) (y : 𝐁 x) → C (x , y))
ev-pair f x y = f (x , y)

-- is an equivalence.

ev-pair⁻¹ : ∀ {ℓ} {C : (Σ A 𝐁) → Set ℓ} → 
            ((x : A) (y : 𝐁 x) → C (x , y)) → 
            (∀ (z : Σ A 𝐁) → C z)
ev-pair⁻¹ f (x , y) = f x y

-- AH> Here is another example where Agda's η-equivalence definitional
-- equality spares us the need for functional extensionality.
ev-pair-equiv : ∀ {ℓ} {C : (Σ A 𝐁) → Set ℓ} → is-equiv (ev-pair {C = C})
ev-pair-equiv = has-inverse⇒is-equiv (ev-pair⁻¹ , Refl , Refl) -- (ev-pair⁻¹ , (Refl , Refl))

-- AH> We have simply demonstrated that currying/uncurrying is an equivalence.
-- Corollary 13.3.2: Currying is the degenerate case.

ev-pair′ : ∀ {X : Set ℓ} → (A × B → X) → A → B → X
ev-pair′ = ev-pair 

ev-pair′-equiv : ∀ {X : Set ℓ} → is-equiv (ev-pair′ {A = A} {B = B} {X = X})
ev-pair′-equiv = ev-pair-equiv

--------------------------------------------------------------------------------
-- THe universal property of identity types
--
-- Something, something, Yoneda. 

--------------------------------------------------------------------------------
-- Theorem 13.3.3: ev-refl is an equivalence.

module _ (a : A) (B : (x : A) → (a ≡ x) → Set ℓ) where
  -- Clearly, this is the converse of based path induction
  ev-refl : ((x : A) (p : a ≡ x) → B x p) → B a refl 
  ev-refl f = f a refl

  -- So we're just stating that the induction principle on identity 
  -- types is an equivalence. The proof is:
  -- 1. that 
  --      ev-refl ∘ ind≡ ∼ id 
  --    is immediate.
  -- 2. In the converse,
  --      ind≡ ∘ ev-refl
  --    = (g : (x : A) (p : a ≡ x) → B x p) → 
  --      ind≡ a B (g a refl) ≡ g
  --    so we need to use function extensionality twice.
  --    Induction on (p : a ≡ x), once it's in scope, makes everything reduce 
  --    to refl.
  univ-id : is-equiv ev-refl
  univ-id = has-inverse⇒is-equiv 
    ((ind≡ a B) , 
      Refl ,
      λ f → fun-ext _ _ (λ x → fun-ext _ _ λ { refl → refl }) ) 

--------------------------------------------------------------------------------
-- Nobody asked, but: a connection to the Yoneda Lemma.
--
-- The Yoneda lemma states, for locally small 𝒞, covariant functor F : 𝒞 → Set,
-- and object A ∈ 𝒞, that the set of natural transformations from F to the hom-functor
-- Hom(A, —) is in bijection to the set F(A):
--    Nat(F , Hom(A, —)) ≃ F(A)
-- Here the Hom-functor Hom(A, —) is:
--  - maps objects X ∈ 𝒞 to the set of arrows Hom(A, X) 
--  - Maps arrows f : X → Y in 𝒞 to the Set arrow g : Hom(A, X) → Hom(A, Y)
--    given by 
--      g(h) = f ∘ h
-- The Yoneda Lemma is actually quite easy to prove. If we interpret natural
-- transformations as parametric polymorphic functions and assume a "category"
-- of Agda types, it goes like this:

module _ (A : Set) 
         (F : Set → Set) 
         (fmap : ∀ {A B : Set} → (A → B) → F A → F B)
         (fmap-id : ∀ {A} → fmap {A} id ∼ id)
         (fmap-compose : ∀ {A B C} → (f : B → C) (g : A → B) → fmap (f ∘ g) ∼ fmap f ∘ fmap g) where 

  open import Data.Product.Properties using (Σ-≡,≡→≡)

  -- We will need to use naturality
  Naturality : (∀ (X : Set) → (A → X) → F X) → Set1
  Naturality η = ∀ (X Y : Set) (f : X → Y) → fmap f ∘ η X ∼ η Y ∘ (f ∘_)

  -- In one direction, pass the identity function
  -- Nat(Hom(A, —), F)
  yoneda→ : Σ[ η ∈ (∀ (X : Set) → (A → X) → F X) ] (Naturality η) → -- Nat(F , Hom(A, —))
            F A                                                     -- F(A) 
  yoneda→ η = η .fst A id

  -- In the other direction, fmap from F A to F X.
  yoneda← : F A → Σ[ η ∈ (∀ (X : Set) → (A → X) → F X) ] (Naturality η)
  yoneda← x = (λ X f → fmap f x) , λ X Y f g → sym (fmap-compose f g x) 

  -- One direction is the fmap identity law; 
  -- the other direction is naturality.
  yoneda-equiv : is-equiv yoneda→
  yoneda-equiv = has-inverse⇒is-equiv 
    (yoneda← , 
    fmap-id , 
    λ { (η , nat) → Σ-≡,≡→≡ 
      ((fun-ext _ _ (λ X → fun-ext _ _ (λ f → nat A X f id))) , 
      -- Not interested in proving this part
      ⊥-elim pfft) })
    where
      postulate pfft : ⊥ 

-- Now, as for connecting Yoneda: we think of ourselves in a collection of
-- categories of types in which objects are elements and the arrows are paths. 
-- Hence, for example, the "action on paths" ap is:
--  ap f : x ≡ y → f x ≡ f y
-- that is, the category is the type A, the objects are the terms (x y : A),
-- (x ≡ y) is the arrow, and f : A → B is the functor. Now treat the type
-- family B : A → Set as a functor, and 
--  Hom(a, —) : A → Set 
--  Hom(a, x) = a ≡ x
-- it follows that Nat(Hom(a, —), B) would be a polymorphic function:
--   ((x : A) → a ≡ x → B x)  
-- and B a is:
--   B a
-- This is precisely what we observe in the text:
--   ev-refl : ((x : A) (p : a ≡ x) → B x) → B a
--   ev-refl f = f a
-- and contrast with:
--   yoneda→ : ((X : Set) → (A → X) → F X) → F A
-- That ev-refl is an equivalence is thus the Yoneda Lemma applied 
-- to the particular categories we think of ourself in.

--------------------------------------------------------------------------------
-- AH> I think it is helpful here to characterize the universal properties of
-- the identity and empty types, which are (roughly) exercises 13.6 and 13.7.

--------------------------------------------------------------------------------
-- The universal property for ⊥ states, basically,
-- all eliminations of the bottom type contract to ex-falso.
-- AH> Exercise 13.6 states it more generally as a chain of bi-implications.
--     I'm just going to presume A is an arbitrary empty type,
--     where is-empty(A) = ¬ A = A → ⊥.

module _ (A : Set ℓ) (e : is-empty A) where
  ⊥-univ : ∀ (P : A → Set ℓ) → is-contr ((x : A) → P x)
  ⊥-univ P = (⊥-elim ∘ e) , (λ f → fun-ext _ _ (⊥-elim ∘ e))

  ⊥-univ′ : ∀ {X : Set ℓ} → is-contr (A → X) 
  ⊥-univ′ {X = X} = ⊥-univ λ _ → X


--------------------------------------------------------------------------------
-- The universal property of ⊤ states that ⊤-eval is an equivalence.
-- Again, we prove it for an arbitrary contractible type (which is
-- therefore equivalent to ⊤).

module _ (A : Set ℓ) (cntr : is-contr A) where
  open is-contr cntr renaming (center to a ; contraction to C)
  ⊤-eval : ∀ {P : A → Set ℓ} → 
           ((x : A) → P x) →
           P a
  ⊤-eval f = f a

  -- Things get a little fun, here.
  -- We will need to show that 
  --   tr P p t ≡ t
  -- where
  --   t : P a
  --   p : a ≡ x
  -- There is a trick, given a contraction C, one can use
  -- to define a separate contraction C′ as
  --   C′ x = C a ⁻¹ ○ C x
  -- which forces 
  --   C′ a ≡ C a ⁻¹ ○ C a ≡ refl
  -- and hence choosing to transfer along (C′ x):
  --   ⊤-eval⁻¹ {P = P} t x = tr P (C′ x) t  
  -- gives us 
  --   ⊤-eval⁻¹ t a ≡ tr P (C′ a) t ≡ tr p refl t ≡ t.
  -- (See Notes/OnEquivalence.lagda.md).
  -- And so, yeah, you could do things that way. Or, you can whip
  -- out the sledgehammer: contractible types are -2-types, and thus
  -- are 0-types (sets). Sets observe the UIP. So (C a) ≡ refl,
  -- and let's call it a day.
  uip : UIP A 
  uip = (Irrelevant⇒UIP ∘ is-prop⇒Irrelevant ∘ is-contr⇒is-prop A) cntr

  -- By the UIP, any contraction on the center a equals refl.
  C-refl : C a ≡ refl
  C-refl = uip a a (C a) refl

  -- This means that transporting t along (C a) fixes t.
  C-tr : ∀ {P : A → Set ℓ} → 
           (t : P a) → 
           tr P (C a) t ≡ t
  C-tr x = tr-tr (C a) refl C-refl

  -- We are now free to define the inverse of ⊤-eval as
  -- transporting along (C x).
  ⊤-eval⁻¹ : ∀ {P : A → Set ℓ} → 
             P a → 
           ((x : A) → P x)
  ⊤-eval⁻¹ {P = P} t x = tr P (C x) t

  -- The first direction:
  --     ⊤-eval ∘ ⊤-eval⁻¹ ∼ id  
  --   = (t : P a) → tr P (C a) t ≡ t
  -- is just C-tr. 
  -- The reverse direction:
  --     ⊤-eval⁻¹ ∘ ⊤-eval ∼ id
  --   = (g : (x : A) → P x) → (λ (x : A) → tr P (C x) (g a)) ≡ g
  -- falls away with fun. ext. and induction over (C x) : x ≡ a.
  ⊤-univ : ∀ {P : A → Set ℓ} → 
           is-equiv (⊤-eval {P = P})
  ⊤-univ {P = P} = has-inverse⇒is-equiv 
    (⊤-eval⁻¹ , 
    C-tr  , 
    λ g → fun-ext _ _ (H g))
    where
      H : (g : (x : A) → P x) → ⊤-eval⁻¹ (g a) ∼ g 
      H g x with C x 
      ... | refl = refl
    

--------------------------------------------------------------------------------
-- §13.4 Composing with equivalences
-- 
-- f : A → B is an equivalence iff precomposing by f is an equivalence. 
-- That is, the following are in bi-implication:
--  (i) f is an equivalence
--  (ii) For any type famly P over B the map
--         ((y : B) (P y)) → ((x : A) → P (f x))
--       given by h ↦ h ∘ f is an equivalence.
--  (iii) For any type X the map
--          (B → X) → (A → X)
--        given by g ↦ g ∘ f is an equivalence.
-- 
-- AH> Something feels inherently Yoneda-ey here, but contra-variant. 

module _ {A B : Set ℓ} (f : A → B) where 

  -- This is the contravariant Hom-functor made dependent.
  Hom[—,X]-dep : ∀ {P : B → Set ℓ} → ((y : B) → P y) → ((x : A) → P (f x))
  Hom[—,X]-dep h = h ∘ f 

  -- The contravariant hom-functor.
  Hom[—,X] : ∀ {X : Set ℓ} → (B → X) → (A → X)
  Hom[—,X] {X = X} = Hom[—,X]-dep {P = λ _ → X}

  
  is-equiv⇒Hom-equiv : {P : B → Set ℓ} → is-equiv f → is-equiv (Hom[—,X]-dep {P = P})
  is-equiv⇒Hom-equiv {P = P} eqv with has-inverse⇒is-coh-invertible f (is-equiv⇒has-inverse eqv)
  ... | record { g′ = f⁻¹ ; 𝔾 = G ; ℍ = H ; 𝕂 = K } = has-inverse⇒is-equiv
    (g , 
    (λ h → fun-ext _ _ (λ x → begin
       tr P (G (f x)) (h (f⁻¹ (f x)))    ≡⟨ tr-tr (G (f x)) (ap f (H x)) (K x) ⟩ 
       tr P (ap f (H x)) (h (f⁻¹ (f x))) ≡⟨ tr-ap f (H x) (h (f⁻¹ (f x)))  ⟩ 
       tr (P ∘ f) (H x) (h (f⁻¹ (f x)))   ≡⟨ apd h (H x) ⟩ 
       h x                               ∎)), 
     λ h → fun-ext _ _ (λ y → begin
       tr P (G y) (h (f (f⁻¹ y))) ≡⟨ apd h (G y) ⟩ 
       h y                        ∎)) 
    where
      open PathReasoning
      g : ((x : A) → P (f x)) → (y : B) → P y
      g h y =   tr P (G y) (h (f⁻¹ y))

  -- The other direction
  Hom-equiv⇒is-equiv : (∀ (X : Set ℓ) → is-equiv (Hom[—,X] {X = X}))  → is-equiv f 
  Hom-equiv⇒is-equiv eqv with is-equiv⇒is-contr-map _ (eqv A) id | is-equiv⇒is-contr-map _ (eqv B) f 
  ... | ((h , H) , h-cntr) | ((g , G) , g-cntr)  = 
    (h , λ x → (begin
      -- We need to give a retraction of f.
      -- The type Σ[ g ∈ B → B ] (g ∘ f ≡ f) is contractible,
      -- with center of contraction `g`.
      -- As (f ∘ h) : B → B, we have (f ∘ h) ≡ g
      f (h x) ≡⟨ ap (λ f′ → f′ x) (ap fst (g-cntr (f ∘ h , fun-ext _ _ (λ y → ap (λ f′ → f (f′ y)) H)))) ⁻¹  ⟩ 
      -- As id : B → B, we have g ≡ id.
      g x     ≡⟨ ap (λ f′ → f′ x) (ap fst (g-cntr (id , refl))) ⟩
      x        ∎)) , 
    -- We need to give a section of f, which we have already as (h , H).
    (h ,  λ x → ap (λ g → g x) H) 
    where
      open PathReasoning

--------------------------------------------------------------------------------
-- § 13.5: The strong induction principle of ℕ 

-- AH> I'm not fucking with our old def'n of _<_

module _ (P : ℕ → Set ℓ) where
  open import Data.Nat using (_<_ ; _≤_)
  open import Data.Nat.Properties

  -- Strong induction cannot be immediately
  -- defined as described in thm 13.5.1 because
  -- it is not structurally recursive.
  strong-ind-ℕ₀ : 
    P 0 → 
    ((n : ℕ) → (∀ (m : ℕ) → m ≤ n → P m) → P (suc n)) → 
    (n : ℕ) → P n
  strong-ind-ℕ₀ p₀ pₛ zero = p₀
  strong-ind-ℕ₀ p₀ pₛ (suc n) = {!pₛ n (λ m p → strong-ind-ℕ₀ p₀ pₛ m)!}
 
  -- We'll instead define it as so.
  strong-ind-ℕ : 
    P 0 → 
    ((n : ℕ) → (∀ (m : ℕ) → m ≤ n → P m) → P (suc n)) → 
    (n : ℕ) → P n
  strong-ind-ℕ p₀ pₛ n = p′ n n ≤-refl 
    where
      p′ : ∀ (n m : ℕ) → m ≤ n → P m
      p′ n .0 _≤_.z≤n = p₀
      p′ (.suc n) (.suc m) (_≤_.s≤s p) = 
        pₛ m (λ i q → p′ n i (≤-trans q p))

  -- Let's now assert that strong-ind-ℕ agrees with the def'n we intended
  test₀ : (p₀ : P 0) → 
          (pₛ : (n : ℕ) → (∀ (m : ℕ) → m ≤ n → P m) → P (suc n)) → 
          strong-ind-ℕ p₀ pₛ 0 ≡ p₀       
  test₀ p₀ pₛ = refl 

  -- AH> Okay---at this point the HoTT theorists will scoff and say:
  --    you have not been careful about the proof witnesses you have chosen.
  --    The text *is* more careful, and so can inhabit test₁. 
  -- I would rather move on to Ch 14.
  test₁ : (p₀ : P 0) → 
          (pₛ : (n : ℕ) → (∀ (m : ℕ) → m ≤ n → P m) → P (suc n)) → 
          (n : ℕ) → strong-ind-ℕ p₀ pₛ (suc n) ≡ pₛ n (λ m p → strong-ind-ℕ p₀ pₛ m)
  test₁ p₀ pₛ n = ap (pₛ n) (fun-ext _ _ (λ m → fun-ext _ _ (λ p → ⊥-elim pfft)))
    where postulate pfft : ⊥ 

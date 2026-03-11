module Chapters.`10.Reading where

open import Prelude
open import Chapters.`09.Reading

{- -----------------------------------------------------------------------------
AH> 


-}

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

Eq-fib : ∀ (f : A → B) (y : B) → fib f y → fib f y → Set _
Eq-fib f y f1 f2 = f1 ≡Σ f2

refl-fib : ∀ {f : A → B} {y : B} → ∀ (p : fib f y) → Eq-fib f y p p
refl-fib (x , p) = refl-≡Σ _

-- Prop 10.3.3: The canonical map
--   ((x, p) ≡ (x′ , p′)) → Eq-fib f y ((x, p), (x′ , p′))
-- induced by the reflexivity of Eq-fib f is an equivalence for any
-- (x, p), (x′, p′) : fib f y.
-- module contr-maps (f : A → B) (y : B) where
--   open PathReasoning
co-map-fib : ∀ (f : A → B) (y : B) {fib1 fib2 : fib f y} → Eq-fib f y fib1 fib2 → fib1 ≡ fib2
co-map-fib f y {fib1 = x , p} {fib2 = x′ , p′} (refl , refl) = refl

map-fib :  ∀ (f : A → B) (y : B) (fib1 fib2 : fib f y) → (fib1 ≡ fib2) → Eq-fib f y fib1 fib2
map-fib f y fib1 fib2 refl = refl-fib _


-- Def 10.3.4: contractible maps
-- AH> This is how the HOTT book defines is-equiv, actually.
is-contr-map : (f : A → B) → Set _
is-contr-map {B = B} f = ∀ (b : B) → is-contr (fib f b)

-- Thm 10.3.5: Any contractible map is an equivalence
is-contr-map-equiv : ∀ (f : A → B) → is-contr-map f → is-equiv f
is-contr-map-equiv {A = A} {B = B} f is-contr-map-f = sec-is-contr-map-f , retr-is-contr-map-f
  where
  g̅ : B → A
  g̅ y with is-contr-map-f y
  ... | (a , _) , _ = a

  G̅ : f ∘ g̅ ∼ id
  G̅ y with is-contr-map-f y
  ... | (_ , p) , _ = p

  sec-is-contr-map-f : section f
  sec-is-contr-map-f = g̅ , G̅

  p : f ∘ g̅ ∘ f ∼ f
  p = G̅ ·ᵣ f

  fib-fx : ∀ {x} → fib f (f x)
  fib-fx {x} = (g̅ ∘ f) x , (p x)

  q : ∀ {x : A} → fib-fx ≡ (x , refl)
  q {x} = is-contr.contraction (is-contr-map-f (f x)) (x , refl)

  retr-f-prf : g̅ ∘ f ∼ id
  retr-f-prf x = ap fst (q {x})

  retr-is-contr-map-f : retraction f
  retr-is-contr-map-f = g̅ , retr-f-prf


--------------------------------------------------------------------
-- §10.4: Eqivalences are contractible maps


-- Def 10.4.1: coherently invertible
------------------------------------
record is-coh-invertible (f : A → B) : Setω where
  field
    g′ : B → A
    G-hom : f ∘ g′ ∼ id
    H-hom : g′ ∘ f ∼ id
    K-hom : G-hom ·ᵣ f ∼ f ·ₗ H-hom

{- 
AH> For further reference, the HOTT book defines coherently invertible maps as 
"half adjoint equivalences":
  
  Def. 4.2.1 (§4.2, pp 173): A function f : A → B is a *half adjoint equivalence*
  if there are g : B → A and homotopies η : g ∘ f ∼ id and ϵ : f ∘ g ∼ id such that
  there exists a homotopy 
    τ : Π(x : A) f (η x) = ϵ (f x)

See that, mapping HAEs to coh-invertibility, f maps to f, g maps to g′, η maps to
H-hom, ϵ maps to G-hom, and τ maps to (the symmetry of) K-hom. -}


-- Prop 10.4.2: Any coherently invertible map has contractible fibers

coh-invertible⇒is-contr-map : ∀ (f : A → B) → is-coh-invertible f → is-contr-map f
coh-invertible⇒is-contr-map {A = A} {B = B} f record { g′ = g′ ; G-hom = G-hom ; H-hom = H-hom ; K-hom = K-hom } y =
  ( g′ y , G-hom y) , contr
    where
      -- K'-hom : (x : A) → G-hom (f x) ≡ (ap f (H-hom x)) ○ refl -- G-hom f
      -- K'-hom = concat-htpy K-hom {!concat-htpy inv-htpy (f ·ₗ H-hom)!}

      K'-hom : (x : A) → tr (λ a → f a ≡ f x) (H-hom x) (G-hom (f x)) ≡ refl
      K'-hom x = {!!} -- apd {!λ a → f a ≡ f x!} {!!}

      a-dep-fun : (x : A) → (p : f x ≡ y) → Eq-fib f y (g′ y , G-hom y) (x , p)
      a-dep-fun x refl = H-hom x ,  K'-hom x

      contr : (x : fib f y) → (g′ y , G-hom y) ≡ x
      contr (a , fa≡y) = co-map-fib f y (a-dep-fun a fa≡y)

{- For an alternative proof to Rijke's Prop 10.4.2, see HOTT Book's Thm 4.2.6 (pp. 176):

  Theorem 4.2.6: If f : A → B is a half adjoint equivalence, then for any y : B,
  the fiber fib f y is contractible.

(Convince yourself that this statement unfolds to: 
  ∀ (y : B) → is-contr (fib f y)
 which is precisely the definition of is-contr-map f.)

The HOTT proof goes as follows:

  Let (g, η, ϵ, τ) : ishae(f), and fix y : B. That is, we have:
    - f : A → B
    - g : B → A 
    - η : g ∘ f ∼ id 
    - ϵ : f ∘ g ∼ id 
    - τ : ∀ (x : A). f ·ₗ η ∼ ϵ ·ᵣ f 
  As our center of contraction for fib f y, we choose (g y , ϵ ·ᵣ y).
  Now take any (x, p) : fib f y; we want to construct a path from 
  (g y, ϵ ·ᵣ y) to (x , p). By lemma 4.2.5, it suffices 
  to give a path γ : g y ≡ x such that f(γ) ○ p = ϵ ·ᵣ y. We put
    γ := g(p)⁻¹ ○ (η ·ᵣ x).
  Then we have 
    f(γ) ○ p = fg(p)⁻¹ ○ f(ηx) ○ p
             = fg(p)⁻¹ ○ ϵ(fx) ○ p
             = ϵy
  where the second equality follows by τx and the third equality is naturality of ϵ.
  AH> Some remarks.
  - The notation g(p) is the action of g on path p: ap g p
  - I'm not sure if e.g. g(p)⁻¹ means (ap g p) ⁻¹ or ap g (p ⁻¹); likewise for g(p)⁻¹
  - Lemma 4.2.5 states that: for any f : A → B, y : B, and (x, p), (x′, p′) : fib f y, we have
      (x, p) ≡ (x′, p′) ≃ Σ[ γ ∈ (x ≡ x′) ] (ap f γ ○ p′ ≡ p)
    I don't know if this maps directly onto any results of Rijke's.
 -}



-- Def. 10.4.3: natural squares of homotopies

-- Def. 10.4.4: ...

-- Lem 10.4.5: has-inverse f → is-coh-invertible f.

-- Thm 10.4.6: Any equivalence is a contractible map.

-- Cor 10.4.7: for any a : A, the type Σ_{x : A} (a ≡ x) is contractible
-- AH> We already proved this in thm-10∙1∙4.

module Chapters.`11.Reading where

open import Prelude
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises

-- open HomReasoning
--------------------------------------------------------------------
-- Chapter 11: The fundamental theorem of identity types


private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C D X Y Z : Set ℓ
    -- 𝐁 𝐂 𝐃 : A → Set ℓ
    -- f g h i : (x : A) → 𝐁 x


--------------------------------------------------------------------
-- §11.1: Families of equivalences

-- Def 11.1.1
tot : {A : Set ℓ} {𝐁 𝐂 : A → Set ℓ} → (∀ (x : A) → 𝐁 x → 𝐂 x) → Σ A 𝐁 → Σ A 𝐂
tot f (x , y) = x , f x y


-- Lemma 11.1.2 For any family of maps 𝑓 : Π_(𝑥:𝐴) 𝐵 𝑥 → 𝐶 𝑥 and any
-- 𝑡 : Σ_(𝑥:𝐴) 𝐶 𝑥, there is an equivalence
-- fib_(tot f) (t) ≃ fib_(f (pr₁ t)) (pr₂ t)

fib-tot-equiv : {𝐁 𝐂 : A → Set ℓ} → (f : ∀ (x : A) → 𝐁 x → 𝐂 x) → (t : Σ A 𝐂) → fib (tot f) t ≃ fib (f (fst t)) (snd t)
fib-tot-equiv f t = ϕ , ϕ-is-equiv
  where
  ϕ : fib (tot f) t → fib (f (fst t)) (snd t)
  ϕ ((x , y) , refl) = y , refl

  ψ : fib (f (fst t)) (snd t) → fib (tot f) t
  ψ (y , refl) = ((fst t) , y) , refl


  𝔾 : ϕ ∘ ψ  ∼ id
  𝔾 (y , refl) = refl

  ℍ : ψ ∘ ϕ  ∼ id
  ℍ (x , refl) = refl

  ϕ-is-equiv : is-equiv ϕ
  ϕ-is-equiv = (ψ , 𝔾) , (ψ , ℍ)

-- lemma 11.1.3
-- let 𝑓 : Π_(𝑥:𝐴) 𝐵 𝑥 → 𝐶 𝑥 be a family of maps
-- The following are equivalent
-- (i) for each x the map f x is an equivalence. We call f a _family of equivalences_
-- (ii) The map tot (f) : Σ_(x : A) B x -> Σ_(x : A)  C x is an equivalence
module 11•1•3 {A : Set ℓ} {𝐁 𝐂 : A → Set ℓ} (f : (x : A) → 𝐁 x → 𝐂 x) where
  -- is-contr-map {B = B} f = ∀ (b : B) → is-contr (fib f b)
  -- 10.3.5 is-contr-map-equiv (f : A → B) : is-contr-map f → is-equiv f
  -- thm•10•4•6 (f : A → B) : is-equiv f → is-contr-map f

  -- Due to lemma 11•1•2 we know that the fibers are equivalent
  lem : (x : A) (c : 𝐂 x) → fib (tot f) (x , c) ≃ fib (f x) c
  lem x c = fib-tot-equiv f (x , c)


  -- thus we know that fib (tot f) (x , c) is contractible if and only if fib (f x) c is contractible by Ex. 10.3
  lem0 : (x : A) (c : 𝐂 x) → is-contr (fib (tot f) (x , c)) ↔ is-contr (fib (f x) c)
  lem0 x c with lem x c
  ... | (ϕ , ϕ-is-equiv) =
      (λ p → 10-3.ex-10-3-i-iii⇒ii ϕ p ϕ-is-equiv) , λ p → 10-3.ex-10-3-ii-iii⇒i ϕ p ϕ-is-equiv

  -- Hence, we know that (tot f) is a contractible map if and only if f x is a contractible map for each x
  lem1 : is-contr-map (tot f) ↔ ((x : A) → is-contr-map (f x))
  lem1 = (λ ctr-map a ca → _↔_.to (lem0 a ca) (ctr-map (a , ca))) , λ { x (a , ca) → _↔_.from (lem0 a ca) (x a ca) }

  -- Thus, we know that (tot f) is an equivalence if and only if f x is an equivalence for each x : A
  -- by using thm•10•4•6 and lem 10.3.5
  thm : is-equiv (tot f) ↔ ((x : A) → is-equiv (f x))
  thm = (λ tot-equiv x → is-contr-map-equiv (f x) (_↔_.to lem1 (thm•10•4•6 (tot f) tot-equiv) x)) ,
                     λ fx-equiv → is-contr-map-equiv (tot f) (_↔_.from lem1 (λ a → thm•10•4•6 (f a) (fx-equiv a)))

-- Lemma 11.1.4
-- Consider a map 𝑓 : 𝐴 → 𝐵, and let 𝐶 be a type family over 𝐵.
-- If 𝑓 is an equivalence,then the map
--       σ_f (𝐶) : λ (x, z). (f x, z) : Σ_{x: A} 𝐶 (f x) → Σ_{y: B} 𝐶 (y)
-- is and equivalence
module 11•1•4 {A B : Set ℓ} {𝐂 : B → Set ℓ}(f : A → B) where
  -- We first define the map σ
  σ : Σ[ x ∈ A ] (𝐂 (f x)) → Σ B 𝐂
  σ (x , z) =  f x , z

  -- Now we show that the fibers of σ and f at t are equivalent,
  -- i.e. fib σ t ≃ fib f (pr₁ t) for all t : Σ B 𝐂
  ϕ : (t : Σ B 𝐂) → fib σ t → fib f (fst t)
  ϕ (y , z) ((x , z) , refl) = x , refl

  ψ : (t : Σ B 𝐂) → fib f (fst t) → fib σ t
  ψ (y , z) (x , refl) = (x , z) , refl

  𝔾 : (t : Σ B 𝐂) → ϕ t ∘ ψ t ∼ id
  𝔾 (y , z) (x , refl) = refl

  ℍ : (t : Σ B 𝐂) → ψ t ∘ ϕ t ∼ id
  ℍ (y , z) ((x , z) , refl) = refl

  lem0 : (t : Σ B 𝐂) → fib σ t ≃ fib f (fst t)
  lem0 t = ϕ t , ((ψ t , 𝔾 t) , ψ t , ℍ t)

  -- The following proof proceeds similar to 11•1•3

  -- we first show that  ϕ is a contractible if and only if f is a contractible for each t : Σ B 𝐂
  lem1 : ((b , c) : Σ B 𝐂) → is-contr (fib σ (b , c)) ↔ is-contr (fib f b)
  lem1 t with lem0 t
  ... | g , g-is-equiv = (λ p → 10-3.ex-10-3-i-iii⇒ii g p g-is-equiv ) , λ p → 10-3.ex-10-3-ii-iii⇒i g p g-is-equiv


  -- Next show that σ is a contractible map if and only if f is a contractible map for each t : Σ B 𝐂
  lem2 : is-contr-map f → is-contr-map σ
  lem2 = backward
    where
      -- forward : is-contr-map σ → is-contr-map f
      -- forward is-contr-σ = λ b → _↔_.to (lem1 (b , {!!})) (is-contr-σ (b , {!!})) -- Why is converse not possible?

      backward : is-contr-map f → is-contr-map σ
      backward is-contr-f (b , c) = _↔_.from (lem1 (b , c)) (is-contr-f b)

  -- finally, we show that if f is an equivalence then  σ is an equivalence
  lem : is-equiv f → is-equiv σ
  lem = (λ equiv-f → is-contr-map-equiv σ ((lem2 (thm•10•4•6 f equiv-f))))

-- Definition 11.1.5
-- Consider a map f : A → B and a family of maps
--     g : (x : A) → C x → D (f x)
-- where C is a type family over A and D is a type family over B.
-- We define tot_f g : Σ_{x : A} C x → Σ_{y:B} D y
-- we say g is a family of maps over f

tot[_]_ : {𝐂 : A → Set ℓ} {𝐃 : B → Set ℓ} (f : A → B) (g : (x : A) → 𝐂 x → 𝐃 (f x))
     → Σ A 𝐂  → Σ[ y ∈ B ] (𝐃 y)
tot[ f ] g = λ (x , z) → (f x , g x z)

has-inverse-comp : {f : B → C} {g : A → B} → has-inverse f → has-inverse g → has-inverse (f ∘ g)
has-inverse-comp {f = f} {g = g} (f̅ , f∘f̅~id , f̅∘f~id) (g̅ , g∘g̅~id , g̅∘g~id) = g̅ ∘ f̅ , ((λ x →  ap f (g∘g̅~id (f̅ x)) ○ f∘f̅~id x) , λ x → ap g̅ (f̅∘f~id (g x)) ○ g̅∘g~id x )

is-equiv-comp : {f : B → C} {g : A → B} → is-equiv f → is-equiv g → is-equiv (f ∘ g)
is-equiv-comp {f = f} {g = g} equiv-f equiv-g = prf
  where
    has-inverse-f : has-inverse f
    has-inverse-f = is-equiv⇒has-inverse equiv-f

    has-inverse-g : has-inverse g
    has-inverse-g = is-equiv⇒has-inverse equiv-g

    has-inverse-f∘g : has-inverse (f ∘ g)
    has-inverse-f∘g = has-inverse-comp has-inverse-f has-inverse-g

    prf : is-equiv (f ∘ g)
    prf = has-inverse⇒is-equiv has-inverse-f∘g

has-inverse-htpy : {f : A → B} {g : A → B} → has-inverse f → f ∼ g → has-inverse g
has-inverse-htpy (f̅ , (f∘f̅~id , f̅∘f~id)) f∼g = f̅ , ((λ x →  ((f∼g ·ᵣ f̅) x)⁻¹ ○ f∘f̅~id x) , λ x →  ((f̅  ·ₗ f∼g)  x) ⁻¹ ○ f̅∘f~id x)

has-inverse-decomp : {f : B → C} {g : A → B} → has-inverse f → has-inverse (f ∘ g) → has-inverse g
has-inverse-decomp {f = f} {g = g} (f̅ , (f∘f̅~id , f̅∘f~id)) has-inverse-f∘g = has-inverse-g
  where
    g-eq : g ∼ f̅ ∘ (f ∘ g)
    g-eq = sym ∘ f̅∘f~id ∘ g

    has-inverse-f̅ : has-inverse f̅
    has-inverse-f̅ = f , (f̅∘f~id , f∘f̅~id)

    has-inverse-g : has-inverse g
    has-inverse-g = has-inverse-htpy (has-inverse-comp has-inverse-f̅ has-inverse-f∘g) (sym-∼ g-eq)

is-equiv-decomp : {f : B → C} {g : A → B} → is-equiv f → is-equiv (f ∘ g) → is-equiv g
is-equiv-decomp is-equiv-f is-equiv-f∘g =
  has-inverse⇒is-equiv
    (has-inverse-decomp
      (is-equiv⇒has-inverse is-equiv-f)
      (is-equiv⇒has-inverse is-equiv-f∘g))

-- Theorem 11.1.6
-- suppose g is a family of maps over f,
-- then the following are equivalent
-- (i) The family of maps g over f is a family of equivalences
-- (ii) the map tot_f (g) is an equivalence
module 11•1•6 {A B : Set ℓ} {𝐂 : A → Set ℓ} (𝐃 : B → Set ℓ) (f : A → B) (equiv-f : is-equiv f)
              (g : (x : A) → 𝐂 x → 𝐃 (f x)) where

  lem1 : is-equiv (tot g) ↔ ((x : A) → is-equiv (g x))
  lem1 = 11•1•3.thm g


  {- We have a commuting triangle

                       tot[ f ] g
     Σ_{x : A} 𝐂 x ----------------> Σ_{y : B} (𝐃 y)
          \                            ̅/|
           \                          /
            \                        /
             \                      /
       tot g  \                    / σ_f = λ (x , z). (f x , z)
               \                  /
                \                /
                _\|             /
                 Σ_{x : A} D (f x)

  -}

  lem2 : tot[_]_ {𝐃 = 𝐃} f g ∼ (11•1•4.σ f ∘ tot g)
  lem2 = refl-∼

  has-inverse-σ : has-inverse (11•1•4.σ {𝐂 = 𝐃} f)
  has-inverse-σ = 11•1•4.lem f equiv-f |> is-equiv⇒has-inverse

  has-inv-tot-g⇔has-inv-tot-f-g : has-inverse (tot g) ↔ has-inverse (tot[_]_ {𝐃 = 𝐃} f g)
  has-inv-tot-g⇔has-inv-tot-f-g = forward , backward
    where
      forward : has-inverse (tot g) → has-inverse (tot[_]_ {𝐃 = 𝐃} f g)
      forward has-inverse-tot-g = has-inverse-comp has-inverse-σ has-inverse-tot-g

      backward : has-inverse (tot[_]_ {𝐃 = 𝐃} f g) → has-inverse (tot g)
      backward has-inverse-tot[f]g = has-inverse-decomp has-inverse-σ (has-inverse-htpy has-inverse-tot[f]g lem2)

  lem3 :  is-equiv (tot g) ↔ is-equiv (tot[_]_ {𝐃 = 𝐃} f g)
  lem3 = has-inverse⇒is-equiv ∘ _↔_.to has-inv-tot-g⇔has-inv-tot-f-g ∘ is-equiv⇒has-inverse
             , has-inverse⇒is-equiv ∘ _↔_.from has-inv-tot-g⇔has-inv-tot-f-g ∘ is-equiv⇒has-inverse

  thm : ((x : A) → is-equiv (g x)) ↔ is-equiv (tot[_]_ {𝐃 = 𝐃} f g)
  thm = _↔_.to lem3 ∘ _↔_.from lem1 , _↔_.to lem1 ∘ _↔_.from lem3




-- § 11.2 The fundamental theorem
-- The fundamental theorem describes what are the necessary and sufficient conditions on a type family 𝐁
-- over a type A equipped with a point a : A
-- to obtain an equivalence (a ≡ x) ≃ 𝐁 x for each x : A


-- Def 11.2.1 Unary Identity System
-- Let A be a type equipped with the term a : A.
-- A (unary) identity system on A at a consists of
-- 1. a type family B over A equipped with b : B a
-- 2. A function  h ↦ h a b : (Π_{x : A} Π_{y : B x} P x y) → P a b
--     (for any family of types P indexed by x : A and y : B x) has a section

rfl-ident-system :
  {ℓ : Level} {A : Set ℓ} {𝐁 : A → Set ℓ} {P : (x : A) (y : 𝐁 x) → Set ℓ} {a : A}
  (b : 𝐁 a) → ((x : A) (y : 𝐁 x) → P x y) → P a b
rfl-ident-system {a = a} b h = h a b

is-unary-ident-system : {ℓ : Level} {A : Set ℓ} {𝐁 : A → Set ℓ} {a : A} (b : 𝐁 a) → Set (lsuc ℓ)
is-unary-ident-system {ℓ = ℓ} {A = A} {𝐁 = 𝐁} {a = a} b =
  (P : (x : A) (y : 𝐁 x) → Set ℓ) → section {B = P a b} (rfl-ident-system {𝐁 = 𝐁} {P = P} b)

-- Thm 11.2.2 (The fundamental theoerm of identity types)
-- Let A be a type equipped with a : A
-- Let B be a type family over A equipped with a point b : B a
-- Let f be a family of maps f : Π_{x : A} (a ≡ x) → B x
-- equipped with an identification f a refl ≡ b

contr-path : {ℓ : Level} {A : Set ℓ} → (a : A) → is-contr A → is-contr A
contr-path a (center , contraction) = (a , λ x → sym (contraction a) ○ contraction x)

module 11•2•2 {ℓ : Level} {A : Set ℓ} {𝐁 : A → Set ℓ}
              (a : A) (b : 𝐁 a) (f : (x : A) → (a ≡ x) → 𝐁 x) where
  -- (i)   The family of maps f is a family of equivalences
  -- (ii)  The total space Σ_{x : A} B x is contractible
  -- (iii) The family B equipped with b : B a is an identity system
  -- All of these are equivalent

  lem1 : is-equiv (tot f) ↔ (∀ (x : A) → is-equiv (f x))
  lem1 = 11•1•3.thm f

  lem2 : is-contr (Σ[ x ∈ A ] (a ≡ x))
  lem2 = thm-10∙1∙4 a

  -- Recall from Ex 10.3 that if you have two of the three then third can be derived
  --  (i) is-contr A (ii) is-contr B (iii) is-equiv f
  -- thus using lem1 and lem2 we obtain the result

  i↔ii : (∀ (x : A) → is-equiv (f x)) ↔ is-contr (Σ A 𝐁)
  i↔ii = (λ x → 10-3.ex-10-3-i-iii⇒ii (tot f) lem2 ((_↔_.from lem1 x)))
            , λ x → _↔_.to lem1 (10-3.ex-10-3-i-ii⇒iii (tot f) lem2 x)


  {- We have the following diagram that commutes (why?)

                                 ev-pair
    Π_{t : Σ_{x : A} B x} P t -------------------> Π_{x : A} Π_{ y : B x } P x y
           \                                       /
            \                                     /
             \                                   /
              \                                 /
               \                               /
    ev-pt a b   \                             / λ h. h (a, b)
                 \                           /
                  \                         /
                   \                       /
                   _\|                   |/_
                              P a b

   We have that
   ◦ ev-pair has a section (why?)

  -}

  open 9-4

  ii↔iii : is-contr (Σ A 𝐁) ↔ is-unary-ident-system {ℓ = ℓ} b
  ii↔iii = forward , backward
    where -- (left-inv (tot-prf (a , b)))
      ev-pair : ∀ {P : (x : A) (y : 𝐁 x) → Set ℓ} → ((t : Σ A 𝐁) → P (fst t) (snd t)) → (x : A) → (y : 𝐁 x) → P x y
      ev-pair f x y = f (x , y)

      ev-pt[a,b] : ∀ {P : (x : A) (y : 𝐁 x) → Set ℓ} → ((t : Σ A 𝐁) → P (fst t) (snd t)) → P a b
      ev-pt[a,b] f = f (a , b)

      φ : ∀ {P : (x : A) (y : 𝐁 x) → Set ℓ} → ((x : A) → (y : 𝐁 x) → P x y) → P a b
      φ h = h a b

      comm : ∀ {P} → ev-pt[a,b] {P = P} ∼ φ ∘ ev-pair
      comm = refl-∼

      ev-pair-sec : ∀ {P} → section (ev-pair {P = P})
      ev-pair-sec = (λ f t → f (fst t) (snd t)) , refl-∼

      9-4a-inst : ∀ {P} → section (ev-pt[a,b] {P = P}) ↔ section φ
      9-4a-inst = 9-4a.f-section↔g-section ev-pt[a,b] ev-pair φ comm ev-pair-sec

      Contr⇒SI-inst = Contr⇒SI.SI {ℓ₁ = ℓ} {A = Σ A 𝐁}
      SI⇒Contr-inst = SI⇒Contr.Contr {A = Σ A 𝐁}

      forward : is-contr (Σ A 𝐁) → is-unary-ident-system {A = A} {𝐁 = 𝐁} {a = a} b
      forward contr P =
        _↔_.to 9-4a-inst
          ((snd
            $ _↔_.from section↔SI
            $ Contr⇒SI-inst (contr-path (a , b) contr) -- We don't get to choose the center
              {B = λ a,b → P (fst a,b) (snd a,b)}))

      -- Now just do the same thing, but backward
      backward : is-unary-ident-system {A = A} {𝐁 = 𝐁} {a = a} b → is-contr (Σ A 𝐁)
      backward hyp =
        SI⇒Contr-inst
          (_↔_.to (section↔SI)
            ( (a , b) ,
              λ {B = P'} →
                _↔_.from 9-4a-inst
                  (hyp λ x y → P' (x , y))))

  -- for convenience
  i↔iii : (∀ (x : A) → is-equiv (f x)) ↔ is-unary-ident-system {ℓ = ℓ} {A = A} {𝐁 = 𝐁} b
  i↔iii = _↔_.to ii↔iii ∘ (_↔_.to i↔ii) , (_↔_.from i↔ii) ∘ _↔_.from ii↔iii


--------------------------------------------------------------------
-- §11.3: Equality on the natural numers


-- Thm 11.3.1 For each m, n : ℕ, the cannonical map
-- (m = n) → Eqℕ (m , n) is an equivalence

-- If we show that Σ_{n : ℕ} Eqℕ (m , n) is contractible for each m : ℕ
-- then we can use thm 11.2.2 (i↔ii) to show that the map is an equivalence

-- AI> Previously we just had two functions toEqℕ and fromEqℕ,
-- now we show that those two functions are inverses of each other.
-- thus the type (m = n) and Eqℕ (m , n) are isomorphic
-- or that the judgemental equality coincides with observational equality

module 11•3•1 where
  open import Chapters.`01-08.Reading hiding (ap)

  lem : (m : ℕ) → is-contr (Σ[ n ∈ ℕ ] Eqℕ m n)
  lem m = (m , refl-Eqℕ m) , λ x → γ m (fst x) (snd x)
    where
      f : ∀ {m} → (Σ[ n ∈ ℕ ] Eqℕ m n) → Σ[ n ∈ ℕ ] Eqℕ (suc m) n
      f (n , e) = (suc n , e)


      γ : (m : ℕ) → ∀ (n : ℕ) (e : Eqℕ m n) → _≡_ {A = Σ[ n ∈ ℕ ] Eqℕ m n} (m , refl-Eqℕ m) (n , e)
      γ zero zero ⋆ = refl
      -- γ zero (suc n) e is absurd
      -- γ (suc n) zero e is absurd
      γ (suc m) (suc n) e =  ap (f {m = m}) (γ m n e)

  thm : (m n : ℕ) → is-equiv (toEqℕ m n)
  thm m n = _↔_.from (11•2•2.i↔ii m (refl-Eqℕ m) (λ x → toEqℕ m x)) (lem m) n


--------------------------------------------------------------------
-- §11.4: Embeddings


-- Embeddings are homotopical analogue of the set theoritic notion of injective map
-- Def 11.4.1
record is-emb {A B : Set ℓ} (f : A → B) : Set ℓ where
  constructor Embed
  field
    ap-equiv : (x y : A) → is-equiv (ap {x = x} {y = y} f)

  map : A → B
  map = f

_↪[_] : Set ℓ → Set ℓ → Set ℓ -- becuase A ↪ B is already defined in prelude
A ↪[ B ] = Σ[ f ∈ (A → B) ] is-emb f

-- Theorem 11.4.1 Any Equivalence is an embedding
thm•11•4•1 : (e : A ≃ B) → (is-emb (fst e))
thm•11•4•1 {A = A} {B = B} (f , f-equiv) = Embed lem•11•4•1
  where

    -- if we show that Σ_{y : A} f x ≡ f y is an equivalence
    -- then we can use theorem 11.2.2 to prove what we want

    -- but first observe that
    -- inv : (f x ≡ f y) → (f y ≡ f x)
    -- is an equivalence
    open import Chapters.`09.Exercises
    lem0 : (x y : A) → is-equiv (9-1.inv (f x) (f y))
    lem0 x y = 9-1.inv-is-equiv B (f x) (f y)

    -- we have that the fiber `fib f (f x)` is contractible for each x
    -- by theorem 10.4.6
    lem1 : is-contr-map f
    lem1 = thm•10•4•6 f f-equiv

    -- tot "uncurries" a function i.e. goes from ∀ x → f x → g x  to (x , f x)  → (x , g x)
    -- so tot (λ y → 9-1.inv (f x) (f y)) : ∀ (x : A) → Σ_{y} inv (f x) (f y) → Σ_{y} (f y) (f x)

    lem11 : (x : A) → is-equiv (tot (λ y → 9-1.inv (f x) (f y)))
    lem11 = λ x → _↔_.from (11•1•3.thm (λ y → 9-1.inv (f x) (f y))) (lem0 x)

    -- if the function f is an equivalence and its domain is contractible, then the co-domain is contractible
    lem : (x : A) → is-contr (Σ[ y ∈ A ] (f x ≡ f y))
    lem x = 10-3.ex-10-3-ii-iii⇒i {B = Σ[ y ∈ A ] (f y ≡ f x)}
                                    (tot (λ y → 9-1.inv (f x) (f y))) (lem1 (f x)) (lem11 x)

    lem•11•4•1 : (x y : A) → is-equiv (ap {x = x} {y = y} f)
    lem•11•4•1 x y = _↔_.from (11•2•2.i↔ii x refl (λ y → ap {x = x} {y = y} f)) (lem x) y


--------------------------------------------------------------------
-- §11.5: Disjointness of coproducts
-- Characterize the identity types of a co-product
-- open import Chapters.`01-08.Reading using (_⊎_; inl; inr)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Chapters.`01-08.Reading using (∅)
-- Theorem 11.5.1 : Let A and B be types. Then there are equivalences
--     inl x = inl x′  ≃ x = x′
--     inl x = inr′    ≃ ∅
--     inr y = inl x′  ≃ ∅
--     inr y = inl y′  ≃ y = y′
--  for x x′ : A and y y′ : B

-- Defn 11.5.2
-- Let A and B be types we define the Eq-copr
-- Also called the observational equality of coproducts
Eq-copr[_,_] : (A B : Set) → A + B → A + B → Set
Eq-copr[ A , B ] (inj₁ x) (inj₁ x′) = x ≡ x′
Eq-copr[ A , B ] (inj₁ x) (inj₂ y′) = ⊥
Eq-copr[ A , B ] (inj₂ y) (inj₁ x′) = ⊥
Eq-copr[ A , B ] (inj₂ y) (inj₂ y′) = y ≡ y′

-- Lemma 11.5.3: The observational equality relation Eq-copr_{A , B} on A + B is
-- reflexive, and therefore there is a map
-- Eq-copr-eq : Π_{s, t : A + B} (s = t) → Eq-copr_{A , B} (s , t)
Eq-copr-eq : ∀ (s t : A ⊎ B) → (s ≡ t) → Eq-copr[ A , B ] s t
Eq-copr-eq (inj₁ x) t refl = refl
Eq-copr-eq (inj₂ y) t refl = refl


-- The refexivity term ρ is constructed using induction on p : A ⊎ B
refl-Eq-copr : (p : A ⊎ B) → Eq-copr[ A , B ] p p
refl-Eq-copr (inj₁ x) = refl
refl-Eq-copr (inj₂ x) = refl


-- Proposition 11.5.4
-- For any s : A + B the total space
-- Σ_{t : A + B} Eq-copr_{A, B}(s , t)
-- is contractible

module 11•5•4 {A B : Set} where
  lem•11•5•4-helper1 : (x : A) → (Σ[ t ∈ A ⊎ B ] Eq-copr[ A , B ] (inj₁ x) t) ≃
        ((Σ[ x′ ∈ A ] Eq-copr[ A , B ] (inj₁ x) (inj₁ x′)) + (Σ[ y′ ∈ B ] Eq-copr[ A , B ] (inj₁ x) (inj₂ y′)))
  lem•11•5•4-helper1 x = f , has-inverse⇒is-equiv (f̅ , (G  , H))  where
    f : (Σ[ t ∈ A ⊎ B ] Eq-copr[ A , B ] (inj₁ x) t) →
        ((Σ[ x′ ∈ A ] Eq-copr[ A , B ] (inj₁ x) (inj₁ x′)) + (Σ[ y′ ∈ B ] Eq-copr[ A , B ] (inj₁ x) (inj₂ y′)))
    f (inj₁ x , e) = inj₁ (x , e)

    f̅ : ((Σ[ x′ ∈ A ] Eq-copr[ A , B ] (inj₁ x) (inj₁ x′)) + (Σ[ y′ ∈ B ] Eq-copr[ A , B ] (inj₁ x) (inj₂ y′)))
      → (Σ[ t ∈ A ⊎ B ] Eq-copr[ A , B ] (inj₁ x) t)
    f̅ (inj₁ ( x , e)) = inj₁ x , e

    G : f ∘ f̅ ∼ id
    G (inj₁ x) = refl
    H : f̅ ∘ f ∼ id
    H (inj₁ x , e) = refl


  lem•11•5•4-helper1b : (y : B) → (Σ[ t ∈ A ⊎ B ] Eq-copr[ A , B ] (inj₂ y) t) ≃
        ((Σ[ x′ ∈ A ] Eq-copr[ A , B ] (inj₂ y) (inj₁ x′)) + (Σ[ y′ ∈ B ] Eq-copr[ A , B ] (inj₂ y) (inj₂ y′)))
  lem•11•5•4-helper1b y = f , has-inverse⇒is-equiv (f̅ , (G  , H))  where
    f : (Σ[ t ∈ A ⊎ B ] Eq-copr[ A , B ] (inj₂ y) t) →
        ((Σ[ x′ ∈ A ] Eq-copr[ A , B ] (inj₂ y) (inj₁ x′)) + (Σ[ y′ ∈ B ] Eq-copr[ A , B ] (inj₂ y) (inj₂ y′)))
    f (inj₂ x , e) = inj₂ (x , e)

    f̅ : ((Σ[ x′ ∈ A ] Eq-copr[ A , B ] (inj₂ y) (inj₁ x′)) + (Σ[ y′ ∈ B ] Eq-copr[ A , B ] (inj₂ y) (inj₂ y′))) →
        (Σ[ t ∈ A ⊎ B ] Eq-copr[ A , B ] (inj₂ y) t)
    f̅ (inj₂ (y , e)) = (inj₂ y) , e

    G : f ∘ f̅ ∼ id
    G (inj₂ y) = refl
    H : f̅ ∘ f ∼ id
    H (inj₂ y , e) = refl


  lem•11•5•4-helper2 : (x : A) → (((Σ[ x′ ∈ A ] x ≡ x′) + Σ[ y ∈ B ] ∅) ≃ (Σ[ x′ ∈ A ] x ≡ x′))
  lem•11•5•4-helper2 x = f , has-inverse⇒is-equiv (f̅ , (G  , H)) where
    f : (((Σ[ x′ ∈ A ] x ≡ x′) + Σ[ y ∈ B ] ∅) → (Σ[ x′ ∈ A ] x ≡ x′))
    f (inj₁ x) = x


    f̅ : (Σ[ x′ ∈ A ] x ≡ x′) → ((Σ[ x′ ∈ A ] x ≡ x′) + Σ[ y ∈ B ] ∅)
    f̅ x = inj₁ x

    G : f ∘ f̅ ∼ id
    G x = refl
    H : f̅ ∘ f ∼ id
    H (inj₁ x) = refl



  lem•11•5•4-helper2b : (y : B) → ((Σ[ x ∈ A ] ∅) + (Σ[ y′ ∈ B ] y ≡ y′)) ≃ (Σ[ y′ ∈ B ] y ≡ y′)
  lem•11•5•4-helper2b y = f , has-inverse⇒is-equiv (f̅ , (G  , H)) where
    f : ((Σ[ x ∈ A ] ∅) + (Σ[ y′ ∈ B ] y ≡ y′)) → (Σ[ y′ ∈ B ] y ≡ y′)
    f (inj₂ y) = y


    f̅ : (Σ[ y′ ∈ B ] y ≡ y′) → ((Σ[ x ∈ A ] ∅) + (Σ[ y′ ∈ B ] y ≡ y′))
    f̅ y = inj₂ y

    G : f ∘ f̅ ∼ id
    G x = refl
    H : f̅ ∘ f ∼ id
    H (inj₂ x) = refl



  -- We proceed by showing Σ_{t : A + B} Eq-copr_{A, B}(inl x , t) is contractible
  -- and Σ_{t : A + B} Eq-copr_{A, B}(inr y , t) is contractible after inducting on s
  prop : (s : A ⊎ B) → is-contr (Σ[ t ∈ A ⊎ B ] Eq-copr[ A , B ] s t)
  prop (inj₁ x) with lem•11•5•4-helper1 x | lem•11•5•4-helper2 x
  ... | (f , f-eq) | (g , g-eq) = 10-3.ex-10-3-ii-iii⇒i (g ∘ f) (thm-10∙1∙4 x) equiv-g∘f where
    equiv-g∘f : is-equiv (g ∘ f)
    equiv-g∘f = is-equiv-comp g-eq f-eq

  prop (inj₂ y) with lem•11•5•4-helper1b y | lem•11•5•4-helper2b y
  ... | (f , f-eq) | (g , g-eq) = 10-3.ex-10-3-ii-iii⇒i (g ∘ f) (thm-10∙1∙4 y) equiv-g∘f where
    equiv-g∘f : is-equiv (g ∘ f)
    equiv-g∘f = is-equiv-comp g-eq f-eq


thm•11•5•1 : (s t : A ⊎ B) → is-equiv (Eq-copr-eq s t)
thm•11•5•1 s t = _↔_.from (11•2•2.i↔ii s (refl-Eq-copr s) (λ x → Eq-copr-eq s x)) (11•5•4.prop s) t


--------------------------------------------------------------------
-- §11.6: The structure identity principle



-- rfl-ident-system :
--   {ℓ : Level} {A : Set ℓ} {𝐁 : A → Set ℓ} {P : (x : A) (y : 𝐁 x) → Set ℓ} {a : A}
--   (b : 𝐁 a) → ((x : A) (y : 𝐁 x) → P x y) → P a b
-- rfl-ident-system {a = a} b h = h a b

-- is-unary-ident-system : {ℓ : Level} {A : Set ℓ} {𝐁 : A → Set ℓ} {a : A} (b : 𝐁 a) → Set (lsuc ℓ)
-- is-unary-ident-system {ℓ = ℓ} {A = A} {𝐁 = 𝐁} {a = a} b =
--   (P : (x : A) (y : 𝐁 x) → Set ℓ) → section {B = P a b} (rfl-ident-system {𝐁 = 𝐁} {P = P} b)


-- Def 11.6.1
-- Dependent identity system
module 11•6•1 {ℓ : Level} {A : Set ℓ} {𝐁 𝐂 : A → Set ℓ} (𝐃 : (x : A) → 𝐁 x → 𝐂 x → Set ℓ)
               (a : A) (b : 𝐁 a) (c : 𝐂 a)
               (c-ident-system : is-unary-ident-system {𝐁 = 𝐂} {a = a} c)
               (d : 𝐃 a b c) where
  is-dep-ident-system : Set (lsuc ℓ)
  is-dep-ident-system = is-unary-ident-system {A = 𝐁 a} {𝐁 = λ y → 𝐃 a y c} {a = b} d


-- Thm 11.6.2
-- Structure identity principle
-- The following are equivalent

-- (i) Any family of maps (b = y) → 𝐃 a y c indexed by y : 𝐁 a is a family of equivalences
-- (ii) The total space Σ_{y : 𝐁 a} 𝐃 a y c is contractible
-- (iii) 𝐃 is a dependent identity system over 𝐂 at b : 𝐁 a

-- (iv) Any family of maps ( (a, b) = (x , y)) → Σ_{z : 𝐂 x} 𝐃 x y z index by (x, y) : Σ_{x : A} 𝐁 x is a family of equivalences
-- (v) The total space Σ_{(x , y) Σ_{x : A} 𝐁 x} Σ_{z : 𝐂 x} D x y z is contractible
-- (vi) The type family (x , y) ↦ Σ_{z : 𝐂 x} D x y z is an identity system at (a , b) : Σ_{x : A} 𝐁 x



module 11•6•2 {ℓ : Level} {A : Set ℓ} {𝐁 𝐂 : A → Set ℓ} (𝐃 : (x : A) → 𝐁 x → 𝐂 x → Set ℓ) (a : A) (b : 𝐁 a) (c : 𝐂 a) (d : 𝐃 a b c) (c-ident-system : is-unary-ident-system {𝐁 = 𝐂} {a = a} c) where
  i↔ii : {f : (y : 𝐁 a) → (b ≡ y) → 𝐃 a y c} → (∀ (x : 𝐁 a) → is-equiv (f x)) ↔ is-contr (Σ[ y ∈ 𝐁 a ] 𝐃 a y c)
  i↔ii {f = f} = 11•2•2.i↔ii {𝐁 = λ y → 𝐃 a y c} b d f

  ii↔iii : {f : (y : 𝐁 a) → (b ≡ y) → 𝐃 a y c}
         → is-contr (Σ[ y ∈ 𝐁 a ] 𝐃 a y c) ↔ 11•6•1.is-dep-ident-system 𝐃 a b c c-ident-system d
  ii↔iii {f = f} = 11•2•2.ii↔iii {𝐁 = λ y → 𝐃 a y c} b d f


  iv↔v : {f : (q : Σ[ x ∈ A ] 𝐁 x) → ((a , b) ≡ q) → Σ[ z ∈ 𝐂 (fst q) ] 𝐃 (fst q) (snd q) z}
       → (∀ (p : Σ[ x ∈ A ] 𝐁 x) → is-equiv (f p)) ↔ is-contr (Σ[ p ∈ (Σ[ x ∈ A ] 𝐁 x) ] (Σ[ z ∈ 𝐂 (fst p) ] 𝐃 (fst p) (snd p) z))
  iv↔v {f = f} = 11•2•2.i↔ii (a , b) (f (a , b) refl) f


  v↔vi : {f : (q : Σ[ x ∈ A ] 𝐁 x) → ((a , b) ≡ q) → Σ[ z ∈ 𝐂 (fst q) ] 𝐃 (fst q) (snd q) z} →
    is-contr (Σ[ p ∈ (Σ[ x ∈ A ] 𝐁 x) ] (Σ[ z ∈ 𝐂 (fst p) ] 𝐃 (fst p) (snd p) z))
       ↔ is-unary-ident-system {A = Σ[ x ∈ A ] 𝐁 x} {𝐁 = λ q → Σ[ z ∈ 𝐂 (fst q) ] 𝐃 (fst q) (snd q) z} {a = (a , b)} (f (a , b) refl)
  v↔vi {f = f} = 11•2•2.ii↔iii (a , b) (f (a , b) refl) f


  ii↔v : {f : (x : A) → (a ≡ x) → 𝐂 x}
       → is-contr ((Σ[ y ∈ 𝐁 a ] 𝐃 a y c)) ↔ is-contr (Σ[ p ∈ (Σ[ x ∈ A ] 𝐁 x) ] (Σ[ z ∈ 𝐂 (fst p) ] 𝐃 (fst p) (snd p) z))
  ii↔v {f = f} = (λ x → 10-3.ex-10-3-ii-iii⇒i (fwd2 ∘ fwd) x {!!}) , λ x → 10-3.ex-10-3-ii-iii⇒i (bwk ∘ bwk2) x {!!}
     where
       fwd : (Σ[ p ∈ Σ A 𝐁 ] (Σ[ z ∈ 𝐂 (fst p) ] (𝐃 (fst p) (snd p) z))) → (Σ[ q ∈ Σ[ x ∈ A ] 𝐂 x ] (Σ[ y ∈ 𝐁 (fst q) ] 𝐃 (fst q) y (snd q) ))
       fwd ((a , b) , c , d) = (a , c) , (b , d)

       bwk : (Σ[ q ∈ Σ[ x ∈ A ] 𝐂 x ] (Σ[ y ∈ 𝐁 (fst q) ] 𝐃 (fst q) y (snd q) )) → (Σ[ p ∈ Σ A 𝐁 ] (Σ[ z ∈ 𝐂 (fst p) ] (𝐃 (fst p) (snd p) z)))
       bwk ((a , c) , b , d) = (a , b) , c , d

       G : fwd ∘ bwk ∼ id
       G ((a , c) , b , d) = refl

       H : bwk  ∘ fwd ∼ id
       H ((a , b) , c , d) = refl

       lem1 : (Σ[ p ∈ Σ A 𝐁 ] (Σ[ z ∈ 𝐂 (fst p) ] (𝐃 (fst p) (snd p) z))) ≃ (Σ[ q ∈ Σ[ x ∈ A ] 𝐂 x ] (Σ[ y ∈ 𝐁 (fst q) ] 𝐃 (fst q) y (snd q) ))
       lem1 = fwd , ((bwk , G) , (bwk , H))

       𝐂-contr : is-contr (Σ A 𝐂)
       𝐂-contr = (_↔_.from (11•2•2.ii↔iii a c f) c-ident-system)

       fwd2 : (Σ[ q ∈ Σ[ x ∈ A ] 𝐂 x ] (Σ[ y ∈ 𝐁 (fst q) ] 𝐃 (fst q) y (snd q) )) → (Σ[ y ∈ 𝐁 a ] 𝐃 a y c)
       fwd2 ((a′ , c′) , b , d) = {!!}
           -- tr (λ (x , z) → (Σ[ y ∈ 𝐁 x ] (𝐃 x y z)))
           --            ({!(snd 𝐂-contr) (a , c)!}) ({! b!} , {!!})

       bwk2 : (Σ[ y ∈ 𝐁 a ] 𝐃 a y c) → (Σ[ q ∈ Σ[ x ∈ A ] 𝐂 x ] (Σ[ y ∈ 𝐁 (fst q) ] 𝐃 (fst q) y (snd q) ))
       bwk2 (y , d) = (a , c) , (y , d)

       G2 : fwd2 ∘ bwk2 ∼ id
       G2 = {!!}

       H2 : bwk2 ∘ fwd2 ∼ id
       H2 ((fst₁ , snd₂) , fst₂ , snd₁) = {!!}

       lem2 : (Σ[ q ∈ Σ[ x ∈ A ] 𝐂 x ] (Σ[ y ∈ 𝐁 (fst q) ] 𝐃 (fst q) y (snd q) )) ≃ (Σ[ y ∈ 𝐁 a ] 𝐃 a y c)
       lem2 = {!!}


ex•11•6•2 : {A B : Set ℓ} {f : A → B} (b : B)(s1 s2 : Σ[ x ∈ A ] (f x ≡ b)) → (s1 ≡ s2) ≃ fib (ap f) ((snd s1) ○ (snd s2)⁻¹)
ex•11•6•2 {A = A} {B = B} {f = f} b (x , p) (y , q) = {!  !}
  where
    open import Chapters.`10.Reading
    lem1 : ∀ (x : A) → is-contr (Σ[ y ∈ A ] x ≡ y)
    lem1 x = thm-10∙1∙4 x

    lem4 : is-contr (Σ[ q ∈ (f x ≡ b) ] p ≡ q)
    lem4 = thm-10∙1∙4 p

    g : (Σ[ q ∈ f x ≡ b ] (refl ≡ (p ○ q ⁻¹))) → (Σ[ q ∈ (f x ≡ b) ] p ≡ q)
    g (refl , e) = refl , (e ○ right-identity p)⁻¹

    equiv-g : is-equiv g
    equiv-g = has-inverse⇒is-equiv ((λ { (p , refl) → p , (right-inv p) ⁻¹ }) , ((λ { (refl , refl) → refl }) , λ { (refl , e) → {!!} }))

    lem3 : (Σ[ q ∈ f x ≡ b ] (refl ≡ (p ○ q ⁻¹))) ≃ (Σ[ q ∈ (f x ≡ b) ] p ≡ q)
    lem3 = g , equiv-g

    lem2 : is-contr (Σ[ q ∈ f x ≡ b ] (refl ≡ (trans p (sym q))))
    lem2 = 10-3.ex-10-3-ii-iii⇒i g lem4 equiv-g

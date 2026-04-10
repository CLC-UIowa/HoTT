module Chapters.`11.Reading where

open import Prelude
open import Chapters.`09.Reading
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

-- Theorem 11.1.6
-- suppose g is a family of maps over f,
-- then the following are equivalent
-- (i) The family of maps g over f is a family of equivalences
-- (ii) the map tot_f (g) is an equivalence
module 11•1•6 {A B : Set ℓ}{𝐂 : A → Set ℓ}(𝐃 : B → Set ℓ) (f : A → B) (equiv-f : is-equiv f)
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

rfl-ident-system : {𝐁 : A → Set ℓ} {P : (x : A) (y : 𝐁 x) → Set ℓ₁} {a : A} (b : 𝐁 a) →
                  ((x : A) (y : 𝐁 x) → P x y) → P a b
rfl-ident-system {a = a} b h = h a b

is-unary-ident-system : {A : Set ℓ} {𝐁 : A → Set ℓ} {P : (x : A) (y : 𝐁 x) → Set ℓ₁} {a : A} (b : 𝐁 a) → Set (ℓ ⊔ ℓ₁)

is-unary-ident-system {P = P} b = section (rfl-ident-system {P = P} b)


-- Thm 11.2.2 (The fundamental theoerm of identity types)
-- Let A be a type equipped with a : A
-- Let B be a type family over A equipped with a point b : B a
-- Let f be a family of maps f : Π_{x : A} (a ≡ x) → B x
-- equipped with an identification f a refl ≡ b

tr2 : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} {T : (a : A) → B a → Set ℓ} {a a' : A} {b : B a} {b' : B a'} → _≡_ {A = Σ A B} (a , b) (a' , b') → T a b → T a' b'
tr2 {T = T} a,b≡a',b' t = tr (λ (x , y) → T x y) a,b≡a',b' t


module 11•2•2 {ℓ : Level} {A : Set ℓ} {𝐁 : A → Set ℓ} {P : (x : A) (y : 𝐁 x) → Set ℓ}
              (a : A) (b : 𝐁 a) (f : (x : A) → (a ≡ x) → 𝐁 x) (f-ident : f a refl ≡ b) where
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


  ii↔iii : is-contr (Σ A 𝐁) ↔ is-unary-ident-system {A = A} {𝐁 = 𝐁} {P = P} {a = a} b
  ii↔iii = forward , backward
    where
      forward : is-contr (Σ A 𝐁) → is-unary-ident-system {A = A} {𝐁 = 𝐁} {P = P} {a = a} b
      forward (tot-center , tot-prf) = (λ p a' b' → tr2 {ℓ = ℓ} {A = A} {B = 𝐁} {T = P} (sym (tot-prf (a , b)) ○ tot-prf (a' , b')) p ) , λ p → {!!}

      backward : is-unary-ident-system {A = A} {𝐁 = 𝐁} {P = P} {a = a} b → is-contr (Σ A 𝐁)
      backward = {!!}

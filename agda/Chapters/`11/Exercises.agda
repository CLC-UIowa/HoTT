module Chapters.`11.Exercises where

open import Prelude
open import Chapters.`01-08.Reading hiding (tr)
open import Chapters.`01-08.Exercises
open import Chapters.`09.Reading
open import Chapters.`09.Exercises
open import Chapters.`10.Reading
open import Chapters.`10.Exercises
open import Chapters.`11.Reading


module 11•1a where
  -- show that the map ∅ → A is an embedding for any type A
  ex : ∅ ↪[ A ]
  ex = (λ ()) , Embed (λ ())


module 11•1b where
  -- show that inl : A → A + B and inr : B → A + B are embeddings
  -- for any two types A and B

  ex1 : is-emb {A = A} {B = A ⊎ B} inl
  ex1 = Embed (λ x y → ((λ { refl → refl }) , λ { refl → refl }) , ((λ { refl → refl }) , λ { refl → refl }))

  ex2 : is-emb {A = B} {B = A ⊎ B} inr
  ex2 = Embed (λ x y → ((λ { refl → refl }) , λ { refl → refl }) , ((λ { refl → refl }) , λ { refl → refl }))


module 11•1c where
  -- show that inl : A → A + B is an equivalence iff B is empty
  -- show that inr : B → A + B is an equivalence iff A is empty

  ex1 : is-equiv {A = A} {B = A ⊎ B} inl ↔ (B → ∅)
  ex1 {A = A} {B = B} = fwd , λ x → ((λ { (inl x) → x ; (inr b) → ex-falso (x b) })
                        , λ { (inl x) → refl ; (inr b) → ex-falso (x b) })
                        , ( (λ { (inl x) → x ; (inr b) → ex-falso (x b) }) , λ { x → refl } )
    where
      fwd : is-equiv {A = A} {B = A ⊎ B} inl → (B → ∅)
      fwd ((f , G) , f' , H) b with G (inr b)
      ... | ()

  ex2 : is-equiv {A = B} {B = A ⊎ B} inr ↔ (A → ∅)
  ex2 {A = A} = fwd , λ x → ((λ { (inl a) → ex-falso (x a) ; (inr x) → x }) , λ { (inl a) → ex-falso (x a) ; (inr b) → refl })
                            , ((λ { (inl a) → ex-falso (x a) ; (inr b) → b }) , λ x → refl)
    where
      fwd : is-equiv {A = B} {B = A ⊎ B} inr → (A → ∅)
      fwd ((f , G) , f' , H) a with G (inl a)
      ... | ()


module 11•2 where
  -- consider an equivalence e : A ≃ B.
  -- Construct and equivalence
  -- p ↦ p̃ : (e(x) = y) ≃ x = e⁻¹(y)
  -- for every x : A and y : B, such that, the triangle (see text)
  -- commutes for every p : e (x) = y
  -- G is the homotopy that witnesses e ∘ e⁻¹ ~ id
{-          ap_e (p̃)
     e(x) ======== e (e⁻¹ y)
      \                ||
       \               ||
        \              ||
         \             || G y
          \            ||
        p  \           ||
            \          ||
             \         ||
              \        ||
               \       ||
                   y

-}

  open PathReasoning
  lem : {A B : Set ℓ} → (x : A) (y : B) (e : A ≃ B) → (((fst e) x) ≡ y) ≃ (x ≡ (fst (sym-≃ e)) y)
  lem x y e = (λ e1 → sym (begin  fst (sym-≃ e) y ≡⟨ Paths.ap (λ y → fst (sym-≃ e) y) (sym e1) ⟩
                                  fst (sym-≃ e) (fst e x) ≡⟨ {!  e .snd .snd .snd x !} ⟩
                                  x ∎) ) , (((λ e1 → {!!}) , {!!}) , {!!})

module 11•3 {A B : Set ℓ} {f g : A → B} where
  -- show that (f ∼ g) → (is-emb f ↔ is-emb g)
  -- for any f, g : A → B
  f→g : (f ∼ g) → is-emb f → is-emb g
  f→g H (Embed ap-equiv) = Embed
      (λ x y → has-inverse⇒is-equiv ((λ { e →  k x y (H x ○ e ○ (sym (H y))) }) ,
         ((λ x₁ → {!k-sec x y!}) , λ { refl → {!!} })))
     where
       k = λ (x y : A) → (fst ∘ fst) (ap-equiv x y)
       k-sec = λ (x y : A) → (snd ∘ fst) (ap-equiv x y)


  ex : (f ∼ g) → is-emb f ↔ is-emb g
  ex H =  f→g H , {!!}

-- SB> Should be easy
is-equiv-∼ : {A B : Set ℓ} {f g : A → B} → (f ∼ g) → is-equiv f → is-equiv g
is-equiv-∼ f∼g is-equiv-f = has-inverse⇒is-equiv (has-inverse-htpy (is-equiv⇒has-inverse is-equiv-f) f∼g)

ap-comp-∼ : {A B C : Set ℓ} (f : A → B) (g : B → C) {x y : A} → (Paths.ap g) ∘ (Paths.ap {x = x} {y = y} f) ∼ Paths.ap (g ∘ f)
ap-comp-∼ f g = λ z → Paths.ap-comp f g z

has-inverse-has-inverse : {A B : Set ℓ} {f : A → B} (has-inv-f : has-inverse f) → has-inverse (fst (has-inv-f))
has-inverse-has-inverse {f = f} (g , g-inv-prf) = f , ((snd g-inv-prf) , (fst g-inv-prf))

module 11•4 {A B X : Set ℓ} {f : A → X} {g : B → X} {h : A → B} {H : f ∼ g ∘ h} where
  open Paths using (tr)

  -- Consider a commuting triangle
{-
       h
  A --------> B
  \           /
   \         /
  f \       / g
    _\|   |/_
        X

-}
  -- with H : f ~ g ∘ h

  -- (a) Suppose g is an embedding. Show that f is an embedding iff h is an embedding
  -- (b) Suppose h is an equivalence. Show that f is an embedding iff g is an embedding



  ex-a : (is-emb g) → (is-emb f ↔ is-emb h)
  ex-a is-emb-g = forward , backward
    where
      forward : is-emb f → is-emb h
      forward is-emb-f = Embed emb
        where -- SB> Sorry, I couldn't figure out how to put "where" syntax inside the lambda, so I did this nonsense instead
          emb : (x y : A) → is-equiv (Paths.ap h)
          emb x y = emb'
            where
              is-equiv-ap-comp : is-equiv (Paths.ap (g ∘ h))
              is-equiv-ap-comp = is-emb.ap-equiv ((_↔_.to $ 11•3.ex H) is-emb-f) x y

              is-equiv-comp-ap : is-equiv ((Paths.ap g) ∘ (Paths.ap h))
              is-equiv-comp-ap = is-equiv-∼ (sym-∼ (ap-comp-∼ h g)) is-equiv-ap-comp

              is-equiv-ap-g : is-equiv (Paths.ap {x = h x} {y = h y} g)
              is-equiv-ap-g = is-emb.ap-equiv is-emb-g (h x) (h y)

              emb' : is-equiv (Paths.ap h)
              emb' = is-equiv-decomp is-equiv-ap-g is-equiv-comp-ap

      backward : is-emb h → is-emb f
      backward is-emb-h = Embed emb
        where
          is-emb-ap-comp : is-emb (g ∘ h)
          is-emb-ap-comp = Embed emb'
            where
              emb' : (x y : A) → is-equiv (Paths.ap (g ∘ h))
              emb' x y = is-equiv-ap-comp
                where
                  is-equiv-ap-g : is-equiv (Paths.ap {x = h x} {y = h y} g)
                  is-equiv-ap-g = is-emb.ap-equiv is-emb-g (h x) (h y)

                  is-equiv-comp-ap : is-equiv ((Paths.ap g) ∘ (Paths.ap h))
                  is-equiv-comp-ap = is-equiv-comp is-equiv-ap-g (is-emb.ap-equiv is-emb-h x y)

                  is-equiv-ap-comp : is-equiv (Paths.ap (g ∘ h))
                  is-equiv-ap-comp = is-equiv-∼ (ap-comp-∼ h g) is-equiv-comp-ap

          emb : (x y : A) → is-equiv (Paths.ap f)
          emb x y = is-emb.ap-equiv ((_↔_.from $ 11•3.ex H) is-emb-ap-comp) x y

  ex-b-aux : (is-equiv h) → (is-emb g → is-emb f)
  ex-b-aux is-equiv-h = backward
    where
      is-emb-h : is-emb h
      is-emb-h = thm•11•4•1 (h , is-equiv-h)

      backward : is-emb g → is-emb f
      backward is-emb-g = (_↔_.from $ ex-a is-emb-g) is-emb-h

  ex-b : (is-equiv h) → (is-emb f ↔ is-emb g)
  ex-b is-equiv-h = forward , backward
    where
      h-inv : B → A
      h-inv = fst $ is-equiv⇒has-inverse is-equiv-h

      has-inverse-h-inv : has-inverse h-inv
      has-inverse-h-inv = has-inverse-has-inverse (is-equiv⇒has-inverse is-equiv-h)

      is-equiv-h-inv : is-equiv h-inv
      is-equiv-h-inv = has-inverse⇒is-equiv has-inverse-h-inv


      forward : is-emb f → is-emb g
      forward is-emb-f = {!ex-b-aux!}

      backward : is-emb g → is-emb f
      backward = ex-b-aux is-equiv-h

module 11•5 {A B C : Set ℓ} (f : A ↪[ B ]) (g : B ↪[ C ]) where
  -- Consider 2 embeddings f : A ↪ B and g : B ↪ C. Show that the following are equivalent
  -- (i) the composite g ∘ f is an equivalence
  -- (ii) both f and g are equivalences

  i↔ii : is-equiv ((fst g) ∘ (fst f)) ↔ (is-equiv (fst f) × is-equiv (fst g))
  i↔ii = forward , backward
    where
      forward : is-equiv ((fst g) ∘ (fst f)) → (is-equiv (fst f) × is-equiv (fst g))
      forward is-equiv-g∘f = is-equiv-f , is-equiv-g
        where
          has-inverse-g∘f : has-inverse ((fst g) ∘ (fst f))
          has-inverse-g∘f = is-equiv⇒has-inverse is-equiv-g∘f

          f-inv : B → A
          f-inv = (fst has-inverse-g∘f) ∘ (fst g)
          -- f ((g ∘ f)⁻¹ (g x) = x
          -- f ∘ (g ∘ f)⁻¹ ∘ g ∼ id
          -- Want: f ∘ k ∘ g ∼ id , Have: k ∘ (g ∘ f) ∼ id , (g ∘ f) ∘ k ∼ id
          -- Have: (g ∘ f ∘ k) x = x
          -- g (f (k x)) = x
          --
          -- If g (f (f-inv x)) = g x, then f (f-inv x) = x
          --
          -- (g ∘ f ∘ f-inv)
          -- ∼ ((g ∘ f) ∘ k ∘ g)
          -- ~ g

          -- TODO: refactor, or not
          has-inverse-f : has-inverse (fst f)
          has-inverse-f =
            (f-inv , (λ x → `sec (is-emb.ap-equiv (snd g) (fst f (f-inv x)) x) (is-equiv-g∘f .proj₁ .snd (proj₁ g x))) , λ x →
                                                                                                                            f .snd .is-emb.ap-equiv (f-inv (proj₁ f x)) (id x) .snd .proj₁
                                                                                                                            (g .snd .is-emb.ap-equiv (f .proj₁ (f-inv (proj₁ f x)))
                                                                                                                             (f .proj₁ (id x)) .proj₁ .proj₁
                                                                                                                             (is-equiv-g∘f .proj₁ .snd (proj₁ g (proj₁ f x)))))

          is-equiv-f : is-equiv (fst f)
          is-equiv-f = has-inverse⇒is-equiv has-inverse-f

          g-inv : C → B
          g-inv = (fst f) ∘ fst has-inverse-g∘f

          has-inverse-g : has-inverse (fst g)
          has-inverse-g = g-inv , is-equiv-g∘f .proj₁ .snd , λ x →
                                                                g .snd .is-emb.ap-equiv (g-inv (proj₁ g x)) (id x) .proj₁ .proj₁
                                                                (is-equiv-g∘f .proj₁ .snd (proj₁ g x))

          is-equiv-g : is-equiv (fst g)
          is-equiv-g = has-inverse⇒is-equiv has-inverse-g

      backward : (is-equiv (fst f) × is-equiv (fst g)) → is-equiv ((fst g) ∘ (fst f))
      backward (is-equiv-f , is-equiv-g) = is-equiv-comp is-equiv-g is-equiv-f


module 11•8 {A : Set ℓ}  where
  open PathReasoning
  part-a : {𝐁 𝐂 : A → Set ℓ}(f g : (x : A) →  𝐁 x → 𝐂 x) → ((x : A) → (f x) ∼ (g x)) → (tot f ∼ tot g)
  part-a f g f∼g (a , Ba) = Paths.ap (λ y → (a , y)) (f∼g a Ba)

  part-b : {𝐁 𝐂 𝐃 : A → Set ℓ}(f : (x : A) →  𝐁 x → 𝐂 x) (g : (x : A) →  𝐂 x → 𝐃 x)
         → tot (λ x → g x ∘ (f x)) ∼ (tot g ∘ tot f)
  part-b f g (a , Ba) = refl

  part-c : {𝐁 : A → Set ℓ} → tot (λ x → id {A = 𝐁 x}) ∼ id
  part-c (a , Ba) = refl

  part-d : {𝐁 : A → Set ℓ} (a : A) → (f : ∀ x → 𝐁 x → (a ≡ x)) → (∀ x → retraction {A = 𝐁 x} {B = (a ≡ x)} (f x))
        → (∀ x → is-equiv {A = 𝐁 x} {B = (a ≡ x)}  (f x))
  part-d {𝐁 = 𝐁} a f retr-f x = lem4 -- ((fst retr-f) , {!10-2.retract-is-contractible!}) , retr-f
      where
        r : ∀ x → (a ≡ x) → 𝐁 x
        r x = fst (retr-f x)

        lem : retraction (tot f)
        lem = (tot r) , (λ { (x , Bx) → Paths.ap (λ y → (x , y)) ((retr-f x) .snd Bx) })
        lem2 : is-contr (Σ[ x ∈ A ] a ≡ x) → is-contr (Σ A 𝐁)
        lem2 = 10-2.retract-is-contractible (tot f) lem

        lem3 : is-equiv (r x)
        lem3 = _↔_.from (11•2•2.i↔ii a (r a refl) r) (lem2 (thm-10∙1∙4 a)) x

        lem4 : is-equiv (f x)
        lem4 = is-equiv-decomp lem3 (is-equiv-∼ ( sym-∼ (retr-f x .snd)) (((λ z → z) , (λ x₁ → refl)) , (id , (λ x₁ → refl))))
        -- r ∘ f = id


        -- 10-3.ex-10-3-i-ii⇒iii (f x) (contr-b x) (contr-a≡x x)
      -- where
      --   contr-a≡x : ∀ x → is-contr (a ≡ x) -- is-contr (Σ[ x ∈ A ] a ≡ x)
      --   contr-a≡x = {!!}

      --   contr-b : ∀ x → is-contr (𝐁 x)
      --   contr-b = {!!}

  part-e : {𝐁 : A → Set ℓ} (a : A)(f : ∀ x → (a ≡ x) → 𝐁 x) → (∀ x → section (f x)) → (∀ x → is-equiv (f x))
  part-e {𝐁 = 𝐁} a f sec-f = {!!}

module 11•9 {A B : Set ℓ} {f : A → B} where
  ex : (∀ (x y : A) → section (Paths.ap {x = x} {y = y} f)) → is-emb f
  ex sec-ap-f = Embed λ x y → 11•8.part-e x (λ y → Paths.ap {x = x} {y = y} f) (sec-ap-f x) y


-- We say that map f : A → B is path split when
-- f has a section
-- and the map ap f (x , y) : x ≡ y → f x ≡ f y for each x y has a section
is-path-split : {A B : Set ℓ} → (A → B) → Set ℓ
is-path-split {A = A} {B = B} f = section f × ∀ (x y : A) → section (Paths.ap {x = x} {y = y} f)

module 11•10 {A B : Set ℓ} {f : A → B} where
  -- show that the following is equivalent
  -- (i) : The map f is an equivalence
  -- (ii) : The map f is path-split

  -- Note that any equivalence is an embedding,
  i→ii : is-equiv f → is-path-split f
  i→ii is-equiv-f = (is-equiv-f .proj₁) , λ x y → fst (lem .is-emb.ap-equiv x y)
      where
        lem = thm•11•4•1 (f , is-equiv-f)


  ii→i : is-path-split f → is-equiv f
  ii→i (sec-f , sec-ap-f) = sec-f ,
                              ((fst sec-f) ,
                                λ x → sec-ap-f (proj₁ sec-f (f x)) (id x) .proj₁ (sec-f .snd (f x)))

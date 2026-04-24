module Chapters.`11.Exercises where

open import Prelude
open import Chapters.`01-08.Reading
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
  ex2 = {!!}


module 11•1c where
  -- show that inl : A → A + B is an equivalence iff B is empty
  -- show that inr : B → A + B is an equivalence iff A is empty

  ex1 : is-equiv {A = A} {B = A ⊎ B} inl ↔ (B → ∅)
  ex1 {A = A} {B = B} = fwd , λ x → ((λ { (inl x) → x ; (inr b) → ex-falso (x b) }) , λ { (inl x) → refl ; (inr b) → ex-falso (x b) })
    , ( (λ { (inl x) → x ; (inr b) → ex-falso (x b) }) , λ { x → refl } )
    where
      fwd : is-equiv {A = A} {B = A ⊎ B} inl → (B → ∅)
      fwd ((f , G) , f' , H) b with G (inr b)
      ... | ()

  ex2 : is-equiv {A = B} {B = A ⊎ B} inr ↔ (A → ∅)
  ex2 = {!!}


module 11•2 (e : A ≃ B) where
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



module 11•4 where
  -- Consider a comuting triangle
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

module 11•5 {A B C : Set ℓ} (f : A ↪[ B ]) (g : B ↪[ C ]) where
  -- Consider 2 embeddings f : A ↪ B and g : B ↪ C. Show that the following are equivalent
  -- (i) the composite g ∘ f is an equivalence
  -- (ii) both f and g are equivalences

  i↔ii : is-equiv ((fst g) ∘ (fst f)) ↔ (is-equiv (fst f) × is-equiv (fst g))
  i↔ii = {!!}

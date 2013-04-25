module NaturalTransformation where

open import Level
open import Relation.Binary.PropositionalEquality

open import Category
open import Functor

record Natural {o₁ o₂ ℓ₁ ℓ₂} {C : Cat o₁ ℓ₁} {D : Cat o₂ ℓ₂}
       (F G : Fun C D) : Set (o₁ ⊔ ℓ₁ ⊔ ℓ₂)  where
  open Cat
    using (Hom)
  open Cat D
    using ()
    renaming (_∘_ to _∘d_)
  open Fun F
    using (F₀; F₁)
  open Fun G
    using ()
    renaming (F₀ to G₀; F₁ to G₁)

  field
    cmp : ∀ {X} → Hom D (F₀ X) (G₀ X)
    nat : ∀ {X Y} {f : Hom C X Y} →
          G₁ f ∘d cmp ≡ cmp ∘d F₁ f

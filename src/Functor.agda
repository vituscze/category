module Functor where

open import Level
open import Category
open import Relation.Binary.PropositionalEquality

record Fun {o₁ o₂ ℓ₁ ℓ₂} (C : Cat o₁ ℓ₁) (D : Cat o₂ ℓ₂) : Set (o₁ ⊔ ℓ₁ ⊔ o₂ ⊔ ℓ₂) where
  open Cat
  open Cat C
    using ()
    renaming (_∘_ to _∘c_; id to idc)
  open Cat D
    using ()
    renaming (_∘_ to _∘d_; id to idd)

  field
    F₀ : Obj C → Obj D
    F₁ : ∀ {A B} → Hom C A B → Hom D (F₀ A) (F₀ B)

    resp-id : ∀ {A} → idd ≡ F₁ (idc {A})
    resp-∘  : ∀ {X Y Z} (f : Hom C Y Z) (g : Hom C X Y) →
              F₁ (f ∘c g) ≡ F₁ f ∘d F₁ g

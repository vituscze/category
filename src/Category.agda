module Category where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record Cat o ℓ : Set (suc (o ⊔ ℓ)) where
  infixr 20 _∘_

  field
    Obj : Set o
    Hom : Rel Obj ℓ

    id  : ∀ {A}     → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C

    idˡ   : ∀ {A B} {f : Hom A B} → f ∘ id ≡ f
    idʳ   : ∀ {A B} {f : Hom A B} → id ∘ f ≡ f
    assoc : ∀ {A B C D} {f : Hom C D} {g : Hom B C} {h : Hom A B} →
            f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h


_op : ∀ {o ℓ} → Cat o ℓ → Cat o ℓ
c op = record
  { Obj = Obj
  ; Hom = λ A B → Hom B A
  ; id  = id
  ; _∘_ = λ f g → g ∘ f
  ; idˡ = idʳ
  ; idʳ = idˡ
  ; assoc = sym assoc
  }
  where
  open Cat c

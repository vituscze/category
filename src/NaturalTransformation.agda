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

    .nat : ∀ {X Y} {f : Hom C X Y} →
          G₁ f ∘d cmp ≡ cmp ∘d F₁ f

functorCat : ∀ {o₁ o₂ ℓ₁ ℓ₂} → Cat o₁ ℓ₁ → Cat o₂ ℓ₂ → Cat (o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂) (o₁ ⊔ ℓ₁ ⊔ ℓ₂)
functorCat C D = record
  { Obj = Fun C D
  ; Hom = Natural
  ; id  = id-nat
  ; _∘_ = ∘-nat
  ; idˡ = {!!}
  ; idʳ = {!!}
  ; assoc = {!!}
  }
  where
  open Cat
  open Fun
  open Natural

  id-nat : {F : Fun C D} → Natural F F
  id-nat {F} = record
    { cmp = id D
    ; nat = trans (idˡ D) (sym (idʳ D))
    }

  ∘-nat : {F G H : Fun C D} → Natural G H → Natural F G → Natural F H
  ∘-nat {F} {G} {H} α β = record
    { cmp = cmp α ∘d cmp β
    ; nat = λ {_} {_} {f} → begin
         F₁ H f ∘d (cmp α   ∘d cmp β)  ≡⟨ assoc D ⟩
        (F₁ H f ∘d  cmp α)  ∘d cmp β   ≡⟨ cong (λ x → x ∘d cmp β) (nat α) ⟩
        (cmp α  ∘d  F₁ G f) ∘d cmp β   ≡⟨ sym (assoc D) ⟩
         cmp α  ∘d (F₁ G f  ∘d cmp β)  ≡⟨ cong (λ x → cmp α ∘d x) (nat β) ⟩
         cmp α  ∘d (cmp β   ∘d F₁ F f) ≡⟨ assoc D ⟩
        (cmp α  ∘d  cmp β)  ∘d F₁ F f  ∎
    }
    where
    open ≡-Reasoning

    _∘d_ = _∘_ D

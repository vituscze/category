module NaturalTransformation where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Category
open import Functor

record Natural {o₁ o₂ ℓ₁ ℓ₂} {C : Cat o₁ ℓ₁} {D : Cat o₂ ℓ₂}
       (F G : Fun C D) : Set (o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂) where
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
    cmp  : ∀ X → Hom D (F₀ X) (G₀ X)

    .nat : ∀ {X Y} {f : Hom C X Y} →
           G₁ f ∘d cmp X ≡ cmp Y ∘d F₁ f

module FunCat {o₁ o₂ ℓ₁ ℓ₂} {C : Cat o₁ ℓ₁} {D : Cat o₂ ℓ₂} where
  open Cat
  open Fun
  open Natural

  open ≡-Reasoning

  infix 2 _≡n_

  _≡n_ : {F G : Fun C D} → Rel (Natural F G) (o₁ ⊔ ℓ₂)
  _≡n_ X Y = ∀ {x} → Natural.cmp X x ≡ Natural.cmp Y x

  _∘d_ = _∘_ D

  id₀ : {F : Fun C D} → Natural F F
  id₀ {F} = record
    { cmp = λ _ → id D
    ; nat = trans (idˡ D) (sym (idʳ D))
    }

  _∘₀_ : {F G H : Fun C D} → Natural G H → Natural F G → Natural F H
  _∘₀_ {F} {G} {H} α β = record
    { cmp = λ _ → cmp α _ ∘d cmp β _
    ; nat = λ {_} {_} {f} → begin
       F₁ H f  ∘d (cmp α _  ∘d cmp β _) ≡⟨ assoc D ⟩
      (F₁ H f  ∘d  cmp α _) ∘d cmp β _  ≡⟨ cong (λ x → x ∘d cmp β _) (nat α) ⟩
      (cmp α _ ∘d  F₁ G f)  ∘d cmp β _  ≡⟨ sym (assoc D) ⟩
       cmp α _ ∘d (F₁ G f   ∘d cmp β _) ≡⟨ cong (λ x → cmp α _ ∘d x) (nat β) ⟩
       cmp α _ ∘d (cmp β _  ∘d F₁ F f)  ≡⟨ assoc D ⟩
      (cmp α _ ∘d  cmp β _) ∘d F₁ F f   ∎
    }

  .∘₀-idʳ : {F G : Fun C D} {α : Natural F G} → id₀ ∘₀ α ≡n α
  ∘₀-idʳ = idʳ D

  .∘₀-idˡ : {F G : Fun C D} {α : Natural F G} → α ∘₀ id₀ ≡n α
  ∘₀-idˡ = idˡ D

  .∘₀-assoc : {F G H I : Fun C D}
              {α : Natural H I} {β : Natural G H} {γ : Natural F G} →
              α ∘₀ (β ∘₀ γ) ≡n (α ∘₀ β) ∘₀ γ
  ∘₀-assoc = assoc D

{-# OPTIONS --allow-unsolved-metas #-}

module lambda.system-d where

open import Data.Nat
open import Data.Fin hiding (lift)

open import lambda.vec
open import lambda.untyped

infixr 21 _∧_
infixr 22 _⇒_

data type : Set where
  base : ℕ → type
  _⇒_ _∧_ : type → type → type

context : ℕ → Set
context = vec type


infix 10 _⊢_∶_

data _⊢_∶_ {n : ℕ} (Γ : context n) : term n → type → Set where
  ax : ∀ {i} → Γ ⊢ var i ∶ lookup i Γ
  lam : ∀ {A B x} → Γ ▸ A ⊢ x ∶ B → Γ ⊢ lam x ∶ A ⇒ B
  app : ∀ {A B x y} → Γ ⊢ x ∶ (A ⇒ B) → Γ ⊢ y ∶ A → Γ ⊢ app x y ∶ B
  ∧ⁱ : ∀ {A B x} → Γ ⊢ x ∶ A → Γ ⊢ x ∶ B → Γ ⊢ x ∶ A ∧ B
  ∧ᵉˡ : ∀ {A B x} → Γ ⊢ x ∶ A ∧ B → Γ ⊢ x ∶ A
  ∧ᵉʳ : ∀ {A B x} → Γ ⊢ x ∶ A ∧ B → Γ ⊢ x ∶ B

⊢_∶_ : term 0 → type → Set
⊢ x ∶ t = ε ⊢ x ∶ t

-- This lemma is actually false, because i did not setup the context
-- inclusions properly. It's not really complicated to fix: just
-- transpose the whole machinery from lambda.stack to lambda.vec. The
-- only thing is that it's a bit long and boring to get the same job
-- done on an indexed datatype. Substitution is hard to get right...
lift-p : ∀ {n A X Γ} {x : term n} → Γ ⊢ x ∶ A → Γ ▸ X ⊢ lift x ∶ A
lift-p ax = ax
lift-p (lam x) = {!!}
lift-p (app x y) = app (lift-p x) (lift-p y)
lift-p (∧ⁱ x₁ x₂) = ∧ⁱ (lift-p x₁) (lift-p x₂)
lift-p (∧ᵉˡ x) = ∧ᵉˡ (lift-p x)
lift-p (∧ᵉʳ x) = ∧ᵉʳ (lift-p x)

↑-p : ∀ {n m X Γ Δ} {ρ : Fin n → term m} →
      ((i : Fin n) → Δ ⊢ ρ i ∶ lookup i Γ) →
      (i : Fin (suc n)) → (Δ ▸ X) ⊢ ↑ ρ i ∶ lookup i (Γ ▸ X)
↑-p ρT zero = ax
↑-p ρT (suc i) = lift-p (ρT i)

subst-p : ∀ {n m A} {x : term n} {Γ : context n} {Δ : context m} {ρ : Fin n → term m} →
        Γ ⊢ x ∶ A → ((i : Fin n) → Δ ⊢ ρ i ∶ lookup i Γ) → Δ ⊢ subst x ρ ∶ A
subst-p (ax {i}) ρT = ρT i
subst-p (lam x) ρT = lam (subst-p x (↑-p ρT))
subst-p (app x y) ρT = app (subst-p x ρT) (subst-p y ρT)
subst-p (∧ⁱ x₁ x₂) ρT = ∧ⁱ (subst-p x₁ ρT) (subst-p x₂ ρT)
subst-p (∧ᵉˡ x) ρT = ∧ᵉˡ (subst-p x ρT)
subst-p (∧ᵉʳ x) ρT = ∧ᵉʳ (subst-p x ρT)

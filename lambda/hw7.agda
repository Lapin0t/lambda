module lambda.hw7 where

open import Data.Nat
open import Data.Fin

open import lambda.untyped
open import lambda.system-f-curry renaming (⊢_∶_ to ⊢F_∶_; type to typeF)
open import lambda.system-d renaming (⊢_∶_ to ⊢D_∶_; type to typeD)

module Q₁ where
  -- Source terms
  t₁ t₂ t₃ t₄ : term 0
  t₁ = lam (app (var zero) (var zero))
  t₂ = app t₁ (lam (var zero))
  t₃ = app t₁ t₁
  t₄ = lam (lam (app (var (suc zero)) (app (var zero) (var (suc zero)))))

  -- Utilities
  A B : typeD
  A = base 0
  B = base 1

  V₀ : ∀ {n} → typeF (suc n)
  V₀ = var zero

  V₁ : ∀ {n} → typeF (suc (suc n))
  V₁ = var (suc zero)

  -- Answers for system F
  F₁ : typeF 0
  F₁ = (∀' V₀ ⇒ V₀) ⇒ (∀' V₀ ⇒ V₀)

  F₁-p : ⊢F t₁ ∶ F₁
  F₁-p = lam (app (sub ax) ax)

  -- Answers for system D
  σ₁ : typeD
  σ₁ = (A ∧ A ⇒ B) ⇒ B

  σ₁-p : ⊢D t₁ ∶ σ₁
  σ₁-p = lam (app (∧ᵉʳ ax) (∧ᵉˡ ax))

module lambda.system-d where

open import Data.Nat
open import Data.Fin
open import Data.Vec

open import lambda.untyped

infixr 21 _∧_
infixr 22 _⇒_

data type : Set where
  base : ℕ → type
  _⇒_ _∧_ : type → type → type

context : ℕ → Set
context = Vec type


infix 10 _⊢_∶_

data _⊢_∶_ {n : ℕ} (Γ : context n) : term n → type → Set where
  ax : ∀ {i} → Γ ⊢ var i ∶ lookup i Γ
  lam : ∀ {A B x} → (A ∷ Γ) ⊢ x ∶ B → Γ ⊢ lam x ∶ A ⇒ B
  app : ∀ {A B x y} → Γ ⊢ x ∶ (A ⇒ B) → Γ ⊢ y ∶ A → Γ ⊢ app x y ∶ B
  ∧ⁱ : ∀ {A B x} → Γ ⊢ x ∶ A → Γ ⊢ x ∶ B → Γ ⊢ x ∶ A ∧ B
  ∧ᵉˡ : ∀ {A B x} → Γ ⊢ x ∶ A ∧ B → Γ ⊢ x ∶ A
  ∧ᵉʳ : ∀ {A B x} → Γ ⊢ x ∶ A ∧ B → Γ ⊢ x ∶ B

⊢_∶_ : term 0 → type → Set
⊢ x ∶ t = [] ⊢ x ∶ t

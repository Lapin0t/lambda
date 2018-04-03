module lambda.system-f where

open import Data.Nat
open import Data.Fin hiding (lift)
open import lambda.vec
open import lambda.untyped

infixr 22 _⇒_
infix 20 ∀'_

data type (n : ℕ) : Set where
  var : Fin n → type n
  ∀'_ : type (suc n) → type n
  _⇒_ : type n → type n → type n

type₀ : Set
type₀ = type 0

context : ℕ → ℕ → Set
context n = vec (type n)

lift : ∀ {n} → type n → type (suc n)
lift (var i) = var (suc i)
lift (∀' x) = ∀' (lift x)
lift (x ⇒ y) = lift x ⇒ lift y

infixl 30 ↑_
↑_ : ∀ {n m} → (Fin n → type m) → Fin (suc n) → type (suc m)
(↑ ρ) zero = var zero
(↑ ρ) (suc i) = lift (ρ i)

subst : ∀ {n m} → type n → (Fin n → type m) → type m
subst (var x) ρ = ρ x
subst (∀' x) ρ = ∀' (subst x (↑ ρ))
subst (x ⇒ y) ρ = (subst x ρ) ⇒ (subst y ρ)

idˢ : ∀ {n} → Fin n → type n
idˢ i = var i

_∘ˢ_ : ∀ {n m p} → (Fin m → type p) → (Fin n → type m) → (Fin n → type p)
(ρ ∘ˢ μ) i = subst (μ i) ρ

1ˢ : ∀ {n} → type n → Fin (suc n) → type n
1ˢ x zero = x
1ˢ x (suc i) = var i

_∷ˢ_ : ∀ {n m} → type m → (Fin n → type m) → Fin (suc n) → type m
(e ∷ˢ ρ) zero = e
(e ∷ˢ ρ) (suc i) = ρ i

subst₁ : ∀ {n} → type (suc n) → type n → type n
subst₁ x y = subst x (1ˢ y)

lift-c : ∀ {n m} → context n m → context (suc n) m
lift-c ε = ε
lift-c (Γ ▸ x) = lift-c Γ ▸ lift x


infix 10 _⊢_∶_

data _⊢_∶_ {n m : ℕ} (Γ : context n m) : term m → type n → Set where
  ax : ∀ {i} → Γ ⊢ var i ∶ lookup i Γ
  lam : ∀ {A B x} → Γ ▸ A ⊢ x ∶ B → Γ ⊢ lam x ∶ A ⇒ B
  app : ∀ {A B x y} → Γ ⊢ x ∶ A ⇒ B → Γ ⊢ y ∶ A → Γ ⊢ app x y ∶ B
  gen : ∀ {A x} → lift-c Γ ⊢ x ∶ A → Γ ⊢ x ∶ ∀' A
  sub : ∀ {A B x} → Γ ⊢ x ∶ ∀' A → Γ ⊢ x ∶ subst₁ A B

⊢_∶_ : ∀ {n} → term 0 → type n → Set
⊢ x ∶ t = ε ⊢ x ∶ t

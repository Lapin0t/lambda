module lambda.vec where

open import Data.Nat
open import Data.Fin hiding (_+_)

infixr 40 _▸_

data vec (T : Set) : ℕ → Set where
  ε : vec T 0
  _▸_ : ∀ {n} → vec T n → T → vec T (suc n)

lookup : ∀ {n} → {T : Set} → Fin n → vec T n → T
lookup zero (Γ ▸ x) = x
lookup (suc i) (Γ ▸ x) = lookup i Γ

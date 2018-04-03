module lambda.vec where

open import Data.Nat
open import Data.Fin


data vec {l} (T : Set l) : ℕ → Set l where
  ε : vec T 0
  _▸_ : ∀ {n} → vec T n → T → vec T (suc n)

lookup : ∀ {l n} → {T : Set l} → Fin n → vec T n → T
lookup zero (Γ ▸ x) = x
lookup (suc i) (Γ ▸ x) = lookup i Γ

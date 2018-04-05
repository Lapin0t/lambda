module lambda.untyped where

open import Data.Nat
open import Data.Fin hiding (lift)

data term (n : ℕ) : Set where
  lam : term (suc n) → term n
  var : Fin n → term n
  app : term n → term n → term n

data norm {n : ℕ} : term n → Set
data neut {n : ℕ} : term n → Set

data norm {n} where
  lam : {x : term (suc n)} → norm x → norm (lam x)
  gnd : {x : term n} → neut x → norm x

data neut {n} where
  var : {i : Fin n} → neut (var i)
  app : {x y : term n} → neut x → norm y → neut (app x y)

lift : ∀ {n} → term n → term (suc n)
lift (lam x) = lam (lift x)
lift (var i) = var (suc i)
lift (app x y) = app (lift x) (lift y)

lift₁ : ∀ {n} → term (suc n) → term (suc (suc n))
lift₁ (lam x) = lam (lift₁ x)
lift₁ (var zero) = var zero
lift₁ (var (suc i)) = var (suc (suc i))
lift₁ (app x y) = app (lift₁ x) (lift₁ y)

↑ : ∀ {n m} → (Fin n → term m) → Fin (suc n) → term (suc m)
↑ ρ zero = var zero
↑ ρ (suc i) = lift (ρ i)

subst : ∀ {n m} → term n → (Fin n → term m) → term m
subst (lam x) ρ = lam (subst x (↑ ρ))
subst (var i) ρ = ρ i
subst (app x y) ρ = app (subst x ρ) (subst y ρ)

subst₁ : ∀ {n} → term (suc n) → term n → term n
subst₁ x y = subst x (λ {zero → y; (suc i) → var i})

data _→β_ {n : ℕ} : term n → term n → Set where
  β-beta : ∀ {x y} → app (lam x) y →β subst₁ x y
  β-app₁ : ∀ {x y z} → x →β y → app x z →β app y z
  β-app₂ : ∀ {x y z} → y →β z → app x y →β app x z
  β-lam : ∀ {x y} → x →β y → lam x →β lam y

data _β*_ {n : ℕ} : term n → term n → Set where
  ε : ∀ {x} → x β* x
  _←_ : ∀ {x y z} → x →β y → y β* z → x β* z

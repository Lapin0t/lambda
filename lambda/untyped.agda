module lambda.untyped where

open import Data.Nat
open import Data.Fin

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

module lambda.stack where

open import Relation.Binary.PropositionalEquality

infixr 40 _▸_
infixl 35 _∈_

data stack (T : Set) : Set where
  ε : stack T
  _▸_ : stack T → T → stack T

data _∈_ {T : Set} (x : T) : stack T → Set where
  here : ∀ {Γ} → x ∈ Γ ▸ x
  there : ∀ {Γ y} → x ∈ Γ → x ∈ Γ ▸ y

data _⊇_ {T : Set} : stack T → stack T → Set where
  bot : ε ⊇ ε
  skip : ∀ {Γ Δ x} → Γ ⊇ Δ → Γ ▸ x ⊇ Δ
  keep : ∀ {Γ Δ x} → Γ ⊇ Δ → Γ ▸ x ⊇ Δ ▸ x

module _ {T : Set} where

  id : ∀ {Γ : stack T} → Γ ⊇ Γ
  id {ε} = bot
  id {Γ ▸ x} = keep id


  shift : ∀ {Γ Δ} {x : T} → Γ ⊇ Δ → x ∈ Δ → x ∈ Γ
  shift bot ()
  shift (skip x) v = there (shift x v)
  shift (keep _) here = here
  shift (keep x) (there y) = there (shift x y)

  shift-id : ∀ {Γ : stack T} {x} → (e : x ∈ Γ) → shift id e ≡ e
  shift-id here = refl
  shift-id (there e) = cong there (shift-id e)

  _∘⊇_ : {Γ Δ Λ : stack T} → Γ ⊇ Δ → Δ ⊇ Λ → Γ ⊇ Λ
  bot ∘⊇ bot = bot
  skip x ∘⊇ y = skip (x ∘⊇ y)
  keep x ∘⊇ skip y = skip (x ∘⊇ y)
  keep x ∘⊇ keep y = keep (x ∘⊇ y)

  ∘⊇-idˡ : {Γ Δ : stack T} → (w : Γ ⊇ Δ) → id ∘⊇ w ≡ w
  ∘⊇-idˡ bot = refl
  ∘⊇-idˡ (skip x) = cong skip (∘⊇-idˡ x)
  ∘⊇-idˡ (keep x) = cong keep (∘⊇-idˡ x)

  ∘⊇-idʳ : {Δ Γ : stack T} → (w : Γ ⊇ Δ) → w ∘⊇ id ≡ w
  ∘⊇-idʳ bot = refl
  ∘⊇-idʳ (skip x) = cong skip (∘⊇-idʳ x)
  ∘⊇-idʳ (keep x) = cong keep (∘⊇-idʳ x)

  ∘⊇-assoc : {Γ Δ Λ Ω : stack T} → (w₁ : Γ ⊇ Δ) → (w₂ : Δ ⊇ Λ) → (w₃ : Λ ⊇ Ω) → (w₁ ∘⊇ w₂) ∘⊇ w₃ ≡ w₁ ∘⊇ (w₂ ∘⊇ w₃)
  ∘⊇-assoc bot bot bot = refl
  ∘⊇-assoc (skip w₁) w₂ w₃ = cong skip (∘⊇-assoc w₁ w₂ w₃)
  ∘⊇-assoc (keep w₁) (skip w₂) w₃ = cong skip (∘⊇-assoc w₁ w₂ w₃)
  ∘⊇-assoc (keep w₁) (keep w₂) (skip w₃) = cong skip (∘⊇-assoc w₁ w₂ w₃)
  ∘⊇-assoc (keep w₁) (keep w₂) (keep w₃) = cong keep (∘⊇-assoc w₁ w₂ w₃)

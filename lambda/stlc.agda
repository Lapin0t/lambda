-- This is mostly based on the ``Dependently-typed Functional Programming''
-- lecture from Pierre-Evariste Dagand (17--18, MPRI).
-- ref: https://gitlab.inria.fr/fpottier/mpri-2.4-public/

module lambda.stlc where

open import Relation.Binary.PropositionalEquality
open import Function hiding (id)
open import Data.Product
open import Agda.Builtin.Unit

open import lambda.stack


infixr 50 _⇒_

data type : Set where
  unit : type
  _⇒_ : type → type → type


context : Set
context = stack type


data _⊢_ (Γ : context) : type → Set where
  lam : ∀ {A B} → Γ ▸ A ⊢ B → Γ ⊢ A ⇒ B
  var : ∀ {A} → A ∈ Γ → Γ ⊢ A
  app : ∀ {A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  tt : Γ ⊢ unit


module norm where

  infix 30 _⊢ⁿ_
  infix 30 _⊢ᵉ_
  infix 40 _⟶_
  infix 45 _⟦⇒⟧_
  infix 50 _⟦×⟧_

  data _⊢ᵉ_ (Γ : context) : type → Set
  data _⊢ⁿ_ (Γ : context) : type → Set

  data _⊢ⁿ_ (Γ : context) where
    lam : ∀ {A B} → Γ ▸ A ⊢ⁿ B → Γ ⊢ⁿ A ⇒ B
    tt : Γ ⊢ⁿ unit
    ground : Γ ⊢ᵉ unit → Γ ⊢ⁿ unit

  data _⊢ᵉ_ (Γ : context) where
    var : ∀ {A} → A ∈ Γ → Γ ⊢ᵉ A
    app : ∀ {A B} → Γ ⊢ᵉ A ⇒ B → Γ ⊢ⁿ A → Γ ⊢ᵉ B

  ⌊_⌋ⁿ : ∀ {Γ A} → Γ ⊢ⁿ A → Γ ⊢ A
  ⌊_⌋ᵉ : ∀ {Γ A} → Γ ⊢ᵉ A → Γ ⊢ A

  ⌊ lam x ⌋ⁿ = lam ⌊ x ⌋ⁿ
  ⌊ tt ⌋ⁿ = tt
  ⌊ ground x ⌋ⁿ = ⌊ x ⌋ᵉ

  ⌊ var x ⌋ᵉ = var x
  ⌊ app x y ⌋ᵉ = app ⌊ x ⌋ᵉ ⌊ y ⌋ⁿ


  record sem : Set₁ where
    field
      _⊢ : context → Set
      ren : ∀ {Γ Δ} → Γ ⊇ Δ → Δ ⊢ → Γ ⊢

  _⟶_ : (A B : sem) → Set
  A ⟶ B = ∀ {Γ} → Γ ⊢A → Γ ⊢B
    where open sem A renaming (_⊢ to _⊢A)
          open sem B renaming (_⊢ to _⊢B)

  renameⁿ : ∀ {Γ Δ T} → Γ ⊇ Δ → Δ ⊢ⁿ T → Γ ⊢ⁿ T
  renameᵉ : ∀ {Γ Δ T} → Γ ⊇ Δ → Δ ⊢ᵉ T → Γ ⊢ᵉ T

  renameⁿ wk (lam b)       = lam (renameⁿ (keep wk) b)
  renameⁿ wk (ground grnd) = ground (renameᵉ wk grnd)
  renameⁿ wk tt            = tt

  renameᵉ wk (var v)       = var (shift wk v)
  renameᵉ wk (app f s)     = app (renameᵉ wk f) (renameⁿ wk s)

  renameⁿ-id : ∀ {Γ T} → (x : Γ ⊢ⁿ T) → renameⁿ id x ≡ x
  renameᵉ-id : ∀ {Γ T} → (x : Γ ⊢ᵉ T) → renameᵉ id x ≡ x

  renameⁿ-id (lam x) = cong lam (renameⁿ-id x)
  renameⁿ-id tt = refl
  renameⁿ-id (ground x) = cong ground (renameᵉ-id x)

  renameᵉ-id (var x) = cong var (shift-id x)
  renameᵉ-id (app x y) = cong₂ app (renameᵉ-id x) (renameⁿ-id y)

  semⁿ : type → sem
  semⁿ T = record {
    _⊢ = λ Γ → Γ ⊢ⁿ T ;
    ren = renameⁿ }

  semᵉ : type → sem
  semᵉ T = record {
    _⊢ = λ Γ → Γ ⊢ᵉ T ;
    ren = renameᵉ }

  ⟦unit⟧ : sem
  ⟦unit⟧ = semⁿ unit

  ⟦tt⟧ : ∀ {P} → P ⟶ ⟦unit⟧
  ⟦tt⟧ ρ = tt

  _⟦⇒⟧_ : sem → sem → sem
  P ⟦⇒⟧ Q = record {
    _⊢ = λ Γ → ∀ {Δ} → Δ ⊇ Γ → Δ ⊢P → Δ ⊢Q ;
    ren = λ wk₁ k wk₂ → k (wk₂ ∘⊇ wk₁) }
    where open sem P renaming (_⊢ to _⊢P)
          open sem Q renaming (_⊢ to _⊢Q)


  _⟦×⟧_ : sem → sem → sem
  P ⟦×⟧ Q = record { _⊢ = λ Γ → (Γ ⊢P) × (Γ ⊢Q)
                   ; ren = λ { wk (x , y) → ( ren-P wk x , ren-Q wk y ) } }
    where open sem P renaming (_⊢ to _⊢P ; ren to ren-P)
          open sem Q renaming (_⊢ to _⊢Q ; ren to ren-Q)

  ⟦lam⟧ : ∀ {P Q R} → P ⟦×⟧ Q ⟶ R → P ⟶ Q ⟦⇒⟧ R
  ⟦lam⟧ {P} η p = λ wk q → η (ren-P wk p , q)
    where open sem P renaming (ren to ren-P)

  ⟦app⟧ : ∀ {P Q R} → P ⟶ Q ⟦⇒⟧ R → P ⟶ Q → P ⟶ R
  ⟦app⟧ η μ = λ px → η px id (μ px)

  ⟦_⟧ : type → sem
  ⟦ unit ⟧  = ⟦unit⟧
  ⟦ S ⇒ T ⟧ = ⟦ S ⟧ ⟦⇒⟧ ⟦ T ⟧

  ⊤̂ : sem
  ⊤̂ = record { _⊢ = λ _ → ⊤
             ; ren = λ _ _ → tt }

  ⟦_⟧c : (Γ : context) → sem
  ⟦ ε ⟧c     = ⊤̂
  ⟦ Γ ▸ T ⟧c = ⟦ Γ ⟧c ⟦×⟧ ⟦ T ⟧

  _⟦⊢⟧_ : context → type → Set
  Γ ⟦⊢⟧ T = ⟦ Γ ⟧c ⟶ ⟦ T ⟧

  lookup : ∀ {Γ T} → T ∈ Γ → Γ ⟦⊢⟧ T
  lookup here (_ , v)      = v
  lookup (there x) (γ , _) = lookup x γ

  eval : ∀ {Γ T} → Γ ⊢ T → Γ ⟦⊢⟧ T
  eval {Γ} {A ⇒ B} (lam x) = ⟦lam⟧ {⟦ Γ ⟧c} {⟦ A ⟧} {⟦ B ⟧} (eval x)
  eval (var x) = lookup x
  eval {Γ} {B} (app {A} x y) = ⟦app⟧ {⟦ Γ ⟧c} {⟦ A ⟧} {⟦ B ⟧} (eval x) (eval y)
  eval {Γ} tt = ⟦tt⟧ {⟦ Γ ⟧c}


  [_]⊢_ : context → type → Set
  [ Γ ]⊢ T = Γ ⊢⟦T⟧
    where open sem ⟦ T ⟧ renaming (_⊢ to _⊢⟦T⟧)

  [_]⊢c_ : context → context → Set
  [ Γ ]⊢c Δ = Γ ⊢⟦Δ⟧c
    where open sem ⟦ Δ ⟧c renaming (_⊢ to _⊢⟦Δ⟧c)

  reify : ∀ {T Γ} → [ Γ ]⊢ T  → Γ ⊢ⁿ T
  reflect : ∀ {Γ} → (T : type) → Γ ⊢ᵉ T → [ Γ ]⊢ T

  reify {unit} v = v
  reify {A ⇒ B} x = lam (reify (x (skip id) (reflect A (var here))))

  reflect unit x = ground x
  reflect (A ⇒ B) x = λ w s → reflect B (app (ren w x) (reify s))
    where open sem (semᵉ (A ⇒ B))

  reify-id : ∀ {Γ T} → Γ ⟦⊢⟧ T → Γ ⊢ⁿ T
  reify-id {Γ} x = reify (x (id-c Γ))
    where
      open sem
      id-c : ∀ Γ → [ Γ ]⊢c Γ
      id-c ε = tt
      id-c (Γ ▸ T) = ren ⟦ Γ ⟧c (skip id) (id-c Γ) , reflect T (var here)

  norm : ∀ {Γ T} → Γ ⊢ T → Γ ⊢ⁿ T
  norm = reify-id ∘ eval

module lambda.hw7 where

open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Nat
open import Data.Fin hiding (lift)

open import lambda.untyped
open import lambda.vec
open import lambda.system-f renaming (⊢_∶_ to ⊢F_∶_; type to typeF)
                            hiding (subst; ↑; lift; subst₁)
open import lambda.system-d renaming (⊢_∶_ to ⊢D_∶_; type to typeD;
  _⊢_∶_ to _⊢D_∶_; context to contextD)


-- Peio BORTHELLE -- Homework 7

-- Maybe it's a bit unusual to present things like this, we didn't do any Agda
-- but it would really have been more hassle formalizing the homework in Coq.
-- So here it is, there are some utilities in the other files and also some
-- bonus simply-typed lambda calculus. It was a bit more fun for me than to
-- write again some long derivation tree with no guarantee at all that there
-- isn't a stupid mistake kicking in. I tried to get the notations close to
-- what we had in the lesson, hope this doesn't look too alien.


-- Utilities
A B C : typeD
A = base 0
B = base 1
C = base 1

V₀ : ∀ {n} → typeF (suc n)
V₀ = var zero

V₁ : ∀ {n} → typeF (suc (suc n))
V₁ = var (suc zero)


module Q₁ where
  -- Source terms
  t₁ t₂ t₃ t₄ : term 0
  t₁ = lam (app (var zero) (var zero))
  t₂ = app t₁ (lam (var zero))
  t₃ = app t₁ t₁
  t₄ = lam (lam (app (var (suc zero)) (app (var zero) (var (suc zero)))))

  -- a) system F
  F₁ F₂ F₄ : typeF 0
  F₁ = (∀' V₀ ⇒ V₀) ⇒ (∀' V₀ ⇒ V₀)
  F₂ = ∀' V₀ ⇒ V₀
  F₄ = ∀' ∀' (V₀ ⇒ V₁) ⇒ ((V₀ ⇒ V₁) ⇒ V₀) ⇒ V₁

  F₁-p : ⊢F t₁ ∶ F₁
  F₁-p = lam (∀' V₀ ⇒ V₀) (app (sub (∀' V₀ ⇒ V₀) ax) ax)

  F₂-p : ⊢F t₂ ∶ F₂
  F₂-p = app (lam (∀' V₀ ⇒ V₀) (app (sub (∀' V₀ ⇒ V₀) ax) ax)) (gen (lam V₀ ax))

  -- t₃ is not normalizing: it has a non-trivial beta-reduction to itself.
  -- Because system F is strongly normalizing this prooves that it has no valid
  -- typing judgment.
  t₃-no-norm : t₃ β* t₃
  t₃-no-norm = β-beta ← ε

  F₄-p : ⊢F t₄ ∶ F₄
  F₄-p = gen (gen (lam (V₀ ⇒ V₁) (lam ((V₀ ⇒ V₁) ⇒ V₀) (app ax (app ax ax)))))

  -- b) system D
  σ₁ σ₂ σ₄ : typeD
  σ₁ = (A ∧ A ⇒ B) ⇒ B
  σ₂ = A ⇒ A
  σ₄ = (A ⇒ B) ⇒ ((A ⇒ B) ⇒ A) ⇒ B

  σ₁-p : ⊢D t₁ ∶ σ₁
  σ₁-p = lam (app (∧ᵉʳ ax) (∧ᵉˡ ax))

  σ₂-p : ⊢D t₂ ∶ σ₂
  σ₂-p = app (lam (app (∧ᵉʳ ax) (∧ᵉˡ ax))) (∧ⁱ (lam ax) (lam ax))

  -- Same as system F for t₃ because of the strongly normalizing property.

  σ₄-p : ⊢D t₄ ∶ σ₄
  σ₄-p = lam (lam (app ax (app ax ax)))

module Q₂ where
  --
  σ₁ σ₂ σ₃ σ₄ : typeD
  σ₁ = ((A ∧ B) ⇒ C) ⇒ A ⇒ B ⇒ C
  σ₂ = (A ⇒ B ⇒ C) ⇒ (A ∧ B) ⇒ C
  σ₃ = (C ⇒ A ∧ C ⇒ B) ⇒ C ⇒ (A ∧ B)
  σ₄ = C ⇒ (A ∧ B) ⇒ (C ⇒ A ∧ C ⇒ B)

  σ₁-p : ∀ {t} → ¬ ⊢D t ∶ σ₁
  σ₁-p p = {!!}

  σ₂-p : ⊢D lam (lam (app (app (var (suc zero)) (var zero)) (var zero))) ∶ σ₂
  σ₂-p = lam (lam (app (app ax (∧ᵉˡ ax)) (∧ᵉʳ ax)))

  σ₃-p : ⊢D lam (lam (app (var (suc zero)) (var zero))) ∶ σ₃
  σ₃-p = lam (lam (∧ⁱ (app (∧ᵉˡ ax) ax) (app (∧ᵉʳ ax) ax)))

  σ₄-p : ⊢D lam (lam (lam (var (suc zero)))) ∶ σ₄
  σ₄-p = lam (lam (∧ⁱ (lam (∧ᵉˡ ax)) (lam (∧ᵉʳ ax))))

module Q₃ where
  -- I got stuck on applying the substitution lemma on function type that are
  -- not lambda abstractions but ∧ eliminations. I don't manage to get from
  -- a proof of that type to a proof with the argument type on the top of the
  -- context. Maybe the substitution lemma is not well choosen.
  subj-red : ∀ {n T} → {x y : term n} → {Γ : contextD n} → Γ ⊢D x ∶ T → x →β y → Γ ⊢D y ∶ T
  subj-red ax ()
  subj-red (∧ⁱ x₁ x₂) p = ∧ⁱ (subj-red x₁ p) (subj-red x₂ p)
  subj-red (∧ᵉˡ x) p = ∧ᵉˡ (subj-red x p)
  subj-red (∧ᵉʳ x) p = ∧ᵉʳ (subj-red x p)
  subj-red (app (lam x) y) β-beta = subst-p x (λ { zero → y; (suc i) → ax })
  subj-red (app (∧ᵉˡ x) y) β-beta = {!   !}
  subj-red (app (∧ᵉʳ x) y) β-beta = {!   !}
  subj-red (app x y) (β-app₁ p) = app (subj-red x p) y
  subj-red (app x y) (β-app₂ p) = app x (subj-red y p)
  subj-red (lam x) (β-lam p) = lam (subj-red x p)

module Q₄ where
  -- The BNF grammar i use is:
  --
  --  <NF> ::= "λ" <VAR> "." <NF> | <NE>
  --  <NE> ::= <NE> <NF> | <VAR>
  --
  -- I implemented this grammar as a judgment on untyped lambda terms
  -- with the datatypes `lambda.untyped.norm` and `lambda.untyped.neut`.

  -- Proof that NF and NE don't allow further derivation
  -- This proof as well as the reciprocical were quite mechanized but still
  -- a bit cumbersome.
  nf-last : ∀ {n} → {x : term n} → norm x → ¬ ∃[ y ] (x →β y)
  ne-last : ∀ {n} → {x : term n} → neut x → ¬ ∃[ y ] (x →β y)

  nf-last (lam x) (lam y , β-lam p) = nf-last x (y , p)
  nf-last (gnd x) (lam y , p) = ne-last x (lam y , p)
  nf-last (gnd x) (var i , p) = ne-last x (var i , p)
  nf-last (gnd x) (app a b , p) = ne-last x (app a b , p)

  ne-last var (y , ())
  ne-last (app () y) (_ , β-beta)
  ne-last (app x y) (app a b , β-app₁ p) = ne-last x (a , p)
  ne-last (app x y) (app a b , β-app₂ p) = nf-last y (b , p)

  -- Proof that terms with no further derivation are in NF
  last-nf : ∀ {n} → (x : term n) → ¬ ∃[ y ] (x →β y) → norm x
  last-ne : ∀ {n y} → (x : term n) → ¬ ∃[ z ] (app x y →β z) → neut x

  last-nf (lam x) p = lam (last-nf x λ { (y , p₂) → p (lam y , β-lam p₂) })
  last-nf (var x) p = gnd var
  last-nf (app x y) p = gnd (app
    (last-ne x λ { (z , p₁) → p (z , p₁) })
    (last-nf y λ { (a , b) → p (app x a , β-app₂ b) }))

  last-ne {y = y} (lam x) p with p (subst₁ x y , β-beta)
  ...               | ()
  last-ne (var x) p = var
  last-ne {y = y} (app x z) p = app
    (last-ne x λ { (a , b) → p (app a y , β-app₁ b) })
    (last-nf z λ { (a , b) → p (app (app x a) y , (β-app₁ (β-app₂ b))) })

  const : ∀ {n} → contextD n
  const {zero} = ε
  const {suc n} = const ▸ base 0


  -- Again because i messed up the renaming/substitution on ⊢D terms, i
  -- did not get to formalize the typing properly here.
  type-n : ∀ {n} → {x : term n} → norm x → ∃ (λ Γ → ∃ (λ T → Γ ⊢D x ∶ T))
  type-e : ∀ {n} → {x : term n} → neut x → ∃ (λ Γ → ∃ (λ T → Γ ⊢D x ∶ T))

  -- Here we compute inductively on the subterm, then "unload" the top of
  -- the context A and the result type B into the type A ⇒ B.
  type-n (lam x) = {!   !}
  type-n (gnd x) = type-e x

  -- Here we create a context with fresh base types, assigning the matching
  -- one to the term.
  type-e (var {i}) = {!   !}

  -- Here we compute inductively on both subterms:
  --   Γx ⊢D x ∶ Tx    Γy ⊢D y ∶ Ty
  -- x is a neutral term so it has a type looking like
  --   T ⇒ A₁ ∧ T ⇒ A₁ ⇒ A₂ ∧ …
  -- We then simply extend it with An = Ty. This requires some proof
  -- rewriting with ∧ᵉ*.
  type-e (app x y) = {!   !}


-- Question 5
-- a) The definition of the conjunction in system F is:
--     conjⁱ : Γ ⊢F x ∶ A → Γ ⊢F y ∶ B → Γ ⊢F (x , y) ∶ A ∧F B
--     conjᵉʳ : Γ ⊢F x ∶ A ∧F B → Γ ⊢F π₀ x ∶ A
--     conjᵉˡ : Γ ⊢F x : A ∧F B → Γ ⊢F π₁ x ∶ B
--    The difference is that in system D, the conjunction is more of
--    an intersection: if a single term has 2 type judgements, then
--    it has a judgment for the intersection, whereas for system F
--    it is a couple of 2 different terms.

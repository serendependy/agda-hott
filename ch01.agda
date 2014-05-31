
{-# OPTIONS --without-K #-}

module ch01 where

module FunctionTypes-01s02 where -- already given

module UniverseLevels-01s03 where
  open import Level public

open UniverseLevels-01s03 public

module DepFunctionTypes-01s04 where
  swap : ∀ {α β γ} → {A : Set α} {B : Set β} {C : Set γ} → 
         (A → B → C) → (B → A → C)
  swap {A = A} {B = B} {C = C} f = λ (b : B) → λ (a : A) → f a b

module ProductTypes-01s05 {α β : Level} where

  -- The Unit type
  data ⊤ : Set where
    ★ : ⊤

  -- Recursor
  rec-⊤ : ∀ {γ} (C : Set γ) → C → ⊤ → C
  rec-⊤ C c ★ = c

  ind-⊤ : ∀ {γ} (C : ⊤ → Set γ) → C ★ → ((x : ⊤) → C x)
  ind-⊤ C c ★ = c

  -- The product type
  data _×_ (A : Set α) (B : Set β) : Set (α ⊔ β) where
    _,_ : (fst : A) → (snd : B) → A × B

  module Products {A : Set α} {B : Set β} where

    -- projections
    proj₁ : A × B → A
    proj₁ (fst , snd) = fst

    proj₂ : A × B → B
    proj₂ (fst , snd) = snd

    -- recursors
    rec-A×B : ∀ {γ} → (C : Set γ) →
              (A → B → C) → A × B → C
    rec-A×B C g (fst , snd) = g fst snd

    -- projections defined in terms of recursors
    pr₁ : A × B → A
    pr₁ = rec-A×B A (λ a → λ b → a)

    pr₂ : A × B → B
    pr₂ = rec-A×B B (λ a → λ b → b)

    ind-A×B : ∀ {γ} (C : A × B → Set γ) → 
              ((a : A) → (b : B) → C (a , b)) → ((x : A × B) → C x)
    ind-A×B C f (fst , snd) = f fst snd

module DependentProductTypes-01s06 where

  data Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
    _,_ : (fst : A) → (snd : B fst) → Σ A B

  _×_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
  A × B = Σ A (λ _ → B)

  module DP {α β : Level} {A : Set α} {B : A → Set β} where

    rec-ΣAB : ∀ {γ} → (C : Set γ) → 
              ((a : A) → B a → C) → (Σ A B → C)
    rec-ΣAB C f (fst , snd) = f fst snd

    proj₁ : Σ A B → A
    proj₁ (fst , snd) = fst

    proj₂ : (p : Σ A B) → B (proj₁ p)
    proj₂ (fst , snd) = snd

    ind-ΣAB : (C : Σ A B → Set (α ⊔ β)) →
              ((a : A) → (b : B a) → C (a , b)) → ((p : Σ A B) → C p)
    ind-ΣAB C f (fst , snd) = f fst snd

  open DP public using (proj₁ ; proj₂)

  ac : ∀ {α β γ} {A : Set α} {B : Set β} → {R : A → B → Set γ}
       → ((a : A) → Σ B (λ b → R a b))
       → Σ (A → B) (λ f → ((a : A) → R a (f a)))
  ac g = (λ x → proj₁ (g x)) , (λ x → proj₂ (g x))

  Magma : Set₁
  Magma = Σ Set (λ A → (A → A → A))
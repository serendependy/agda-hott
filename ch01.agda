{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)

module ch01 where

module FunctionTypes-01s02 where -- already given

module UniverseLevels-01s03 where
  open import Level public using (Level ; _⊔_)

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
    proj₁ = rec-ΣAB A (λ a _ → a) 

    ind-ΣAB : ∀ {γ} (C : Σ A B → Set γ) →
              ((a : A) → (b : B a) → C (a , b)) → ((p : Σ A B) → C p)
    ind-ΣAB C f (fst , snd) = f fst snd

    proj₂ : (p : Σ A B) → B (proj₁ p)
    proj₂ = ind-ΣAB (λ p → B (proj₁ p)) (λ a b → b)

  open DP public using (proj₁ ; proj₂)

  ac : ∀ {α β γ} {A : Set α} {B : Set β} → {R : A → B → Set γ}
       → ((a : A) → Σ B (λ b → R a b))
       → Σ (A → B) (λ f → ((a : A) → R a (f a)))
  ac g = (λ x → proj₁ (g x)) , (λ x → proj₂ (g x))

  record Magma (A : Set) : Set₁ where
    field
      f : A → A → A

  record PointedMagma (A : Set) : Set₁ where
    field
      m : Magma A
      e : A

module CoproductTypes-01s07 {α β : Level} where
  
  data _⊹_ (A : Set α) (B : Set β) : Set (α ⊔ β) where
    inl : A → A ⊹ B
    inr : B → A ⊹ B

  data ⊥ : Set where

  rec-A⊹B : ∀ {γ} {A B} → (C : Set γ) → (A → C) → (B → C) → A ⊹ B → C
  rec-A⊹B C g₀ g₁ (inl x) = g₀ x
  rec-A⊹B C g₀ g₁ (inr x) = g₁ x

  rec-⊥ : ∀ {γ} → (C : Set γ) → ⊥ → C
  rec-⊥ C ()

  ind-A⊹B : ∀ {γ} {A B} → (C : A ⊹ B → Set γ)
            → ((a : A) → C (inl a)) → ((b : B) → C (inr b))
            → (cop : A ⊹ B) → C cop
  ind-A⊹B C g₀ g₁ (inl x) = g₀ x
  ind-A⊹B C g₀ g₁ (inr x) = g₁ x

  ind-⊥ : ∀ {γ} → (C : ⊥ → Set γ) → (z : ⊥) → C z
  ind-⊥ C ()

module Booleans-01s08 where

  open CoproductTypes-01s07 using (_⊹_ ; inr ; inl) 

  data Boolean : Set where
    0₂ : Boolean
    1₂ : Boolean

  if_then_else_ : ∀ {γ} {C : Set γ} → Boolean → C → C → C
  if 0₂ then c₁ else c₂ = c₂
  if 1₂ then c₁ else c₂ = c₁

  ind_if_then_else_ : ∀ {γ} (C : Boolean → Set γ)
                      → (b : Boolean) → C 1₂ → C 0₂ → C b
  ind C if 0₂ then c₁ else c₂ = c₂
  ind C if 1₂ then c₁ else c₂ = c₁

  b≡0₂⊹b≡1₂ : ∀ b → (b ≡ 0₂) ⊹ (b ≡ 1₂)
  b≡0₂⊹b≡1₂ b = ind (λ x → (x ≡ 0₂) ⊹ (x ≡ 1₂))
                    if b then inr refl else inl refl

  open DependentProductTypes-01s06 using (Σ ; _,_)

  _⊹'_ : Set → Set → Set
  A ⊹' B = Σ Boolean (λ b → if b then B else A)

  inl' : {A B : Set} → A → A ⊹' B
  inl' a = 0₂ , a

  inr' : {A B : Set} → B → A ⊹' B
  inr' b = 1₂ , b

module NaturalNumbers-01s09 where

  open import Data.Nat
    using (ℕ ; zero ; suc)

  rec-ℕ : ∀ {γ} → (C : Set γ) → (c⁰ : C) → (cˢ : ℕ → C → C) → ℕ → C
  rec-ℕ C c⁰ cˢ 0 = c⁰
  rec-ℕ C c⁰ cˢ (suc n) = cˢ n (rec-ℕ C c⁰ cˢ n)

  double : ℕ → ℕ
  double zero = zero
  double (suc n) = suc (suc (double n))

  double' : ℕ → ℕ
  double' = rec-ℕ ℕ 0 (λ y n → suc (suc n))

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  suc m + n = suc (m + n)

  _+'_ : ℕ → ℕ → ℕ
  _+'_ = rec-ℕ (ℕ → ℕ) (λ z → z) (λ n g m → suc (g m))

  ind-ℕ : ∀ {γ} → (C : ℕ → Set γ) → C 0 → ((n : ℕ) → C n → C (suc n)) → ((n : ℕ) → C n)
  ind-ℕ C c⁰ cˢ zero = c⁰
  ind-ℕ C c⁰ cˢ (suc n) = cˢ n (ind-ℕ C c⁰ cˢ n)
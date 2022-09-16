module FSub.Typing where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Context hiding (Ctx)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FSub.Syntax
open FSub.Syntax.TypeSubstitution using ()
                                  renaming (weaken to weakenTy; plug to plugTy)

Ctx : ℕ → Set
Ctx = TypeContext.Ctx

infix 4 _⊢_<:_
infix 4 _⊢_∶_

data _⊢_<:_ {n} (Γ : Ctx n) : Type n → Type n → Set where
  <:-⊤ : ∀{τ : Type n} → Γ ⊢ τ <: ⊤
  <:-refl : ∀{τ : Type n} → Γ ⊢ τ <: τ
  <:-fun : ∀{τ₁ τ₂ ρ₁ ρ₂} →
           Γ ⊢ τ₂ <: τ₁ → Γ ⊢ ρ₁ <: ρ₂ →
           Γ ⊢ (τ₁ ⇒ ρ₁) <: (τ₂ ⇒ ρ₂)
  <:-var : ∀{x u τ} →
           (TypeContext.lookup Γ x ≡ u) → Γ ⊢ u <: τ →
           Γ ⊢ (TyVar x) <: τ
  <:-trans : ∀{τ₁ τ₂ τ₃} →
             Γ ⊢ τ₁ <: τ₂ → Γ ⊢ τ₂ <: τ₃ →
             Γ ⊢ τ₁ <: τ₃
  <:-ℿ : ∀{S₁ S₂ τ₁ τ₂} → Γ ⊢ S₂ <: S₁ → Γ ⊢ (ℿ S₁ τ₁) <: (ℿ S₂ τ₂)

data _⊢_∶_ {n} (Γ : Ctx n) : Term n → Type n → Set where
  ∶-var : ∀{x τ} → (TypeContext.lookup Γ x ≡ τ) → Γ ⊢ (TVar x) ∶ τ
  ∶-ƛ : ∀{τ₁ τ₂ t} → (τ₁ ∷ Γ) ⊢ t ∶ (weakenTy τ₂) → Γ ⊢ (ƛ τ₁ t) ∶ (τ₁ ⇒ τ₂)
  ∶-ƛ-app : ∀{τ₁ τ₂ t₁ t₂} →
            Γ ⊢ t₁ ∶ (τ₁ ⇒ τ₂) → Γ ⊢ t₂ ∶ τ₁ →
            Γ ⊢ (t₁ ∙ t₂) ∶ τ₂
  ∶-Λ : ∀{τ₁ τ₂ t} → (τ₁ ∷ Γ) ⊢ t ∶ τ₂ → Γ ⊢ (Λ τ₁ t) ∶ (ℿ τ₁ τ₂)
  ∶-Λ-app : ∀{τ τ' u t} →
            Γ ⊢ t ∶ (ℿ u τ') → Γ ⊢ τ <: u →
            Γ ⊢ (t ◎ τ) ∶ (plugTy τ' τ)
  ∶-sub : ∀{τ₁ τ₂ t} → Γ ⊢ t ∶ τ₁ → Γ ⊢ τ₁ <: τ₂ → Γ ⊢ t ∶ τ₂

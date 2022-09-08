module FSub.Typing where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FSub.Syntax

Ctx : ℕ → Set
Ctx = TypeContext.Ctx

infix 4 _⊢_<:_

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


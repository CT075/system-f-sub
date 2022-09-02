module FSub.Typing where

open import Data.Context

open import FSub.Syntax

infix 4 _⊢_<:_

data _⊢_<:_ {n} (Γ : Ctx Type n) : Type n → Type n → Set where
  <:-⊤ : ∀{τ : Type n} → Γ ⊢ τ <: ⊤
  <:-refl : ∀{τ : Type n} → Γ ⊢ τ <: τ
  <:-fun : ∀{τ₁ τ₂ ρ₁ ρ₂} →
           Γ ⊢ τ₂ <: τ₁ → Γ ⊢ ρ₁ <: ρ₂ →
           Γ ⊢ (τ₁ ⇒ ρ₁) <: (τ₂ ⇒ ρ₂)


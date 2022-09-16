module FSub.Typing where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Context hiding (Ctx)
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])

open import FSub.Syntax

open Context

weakenTy = TypeOps.weaken
plugTy = TypeOps.plug

infix 4 _⊢_<:_
infix 4 _⊢_∶_

data _⊢_<:_ {ts vs} (Γ : Ctx ts vs) : Type ts → Type ts → Set where
  <:-⊤ : ∀{τ : Type ts} → Γ ⊢ τ <: ⊤
  <:-refl : ∀{τ : Type ts} → Γ ⊢ τ <: τ
  <:-fun : ∀{τ₁ τ₂ ρ₁ ρ₂} →
           Γ ⊢ τ₂ <: τ₁ → Γ ⊢ ρ₁ <: ρ₂ →
           Γ ⊢ (τ₁ ⇒ ρ₁) <: (τ₂ ⇒ ρ₂)
  <:-var : ∀{x u τ} →
           (Context.lookupTy Γ x ≡ u) → Γ ⊢ u <: τ →
           Γ ⊢ (TyVar x) <: τ
  <:-trans : ∀{τ₁ τ₂ τ₃} →
             Γ ⊢ τ₁ <: τ₂ → Γ ⊢ τ₂ <: τ₃ →
             Γ ⊢ τ₁ <: τ₃
  <:-ℿ : ∀{S₁ S₂ τ₁ τ₂} → Γ ⊢ S₂ <: S₁ → Γ ⊢ (ℿ S₁ τ₁) <: (ℿ S₂ τ₂)

data _⊢_∶_ {ts vs} (Γ : Ctx ts vs) : Term ts vs → Type ts → Set where
  ∶-var : ∀{x τ} → (Context.lookupVar Γ x ≡ τ) → Γ ⊢ (TVar x) ∶ τ
  ∶-ƛ : ∀{τ₁ τ₂ t} → (`∶ τ₁ ∷ Γ) ⊢ t ∶ τ₂ → Γ ⊢ (ƛ τ₁ t) ∶ (τ₁ ⇒ τ₂)
  ∶-ƛ-app : ∀{τ₁ τ₂ t₁ t₂} →
            Γ ⊢ t₁ ∶ (τ₁ ⇒ τ₂) → Γ ⊢ t₂ ∶ τ₁ →
            Γ ⊢ (t₁ ∙ t₂) ∶ τ₂
  ∶-Λ : ∀{τ₁ τ₂ t} → (`<: τ₁ ∷ Γ) ⊢ t ∶ τ₂ → Γ ⊢ (Λ τ₁ t) ∶ (ℿ τ₁ τ₂)
  ∶-Λ-app : ∀{τ τ' u t} →
            Γ ⊢ t ∶ (ℿ u τ') → Γ ⊢ τ <: u →
            Γ ⊢ (t ◎ τ) ∶ (plugTy τ' τ)
  ∶-sub : ∀{τ₁ τ₂ t} → Γ ⊢ t ∶ τ₁ → Γ ⊢ τ₁ <: τ₂ → Γ ⊢ t ∶ τ₂

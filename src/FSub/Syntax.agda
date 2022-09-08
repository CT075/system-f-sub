module FSub.Syntax where

open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.Extra
open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec as Vec
import Data.Context as Context

-- TODO: differentiate type vars and term vars
data Type (n : ℕ) : Set where
  ⊤ : Type n
  TyVar : (x : Fin n) → Type n
  _⇒_ : Type n → Type n → Type n
  ℿ : Type (suc n) → Type n

data Term (tyvars : ℕ) (tvars : ℕ) : Set where
  TVar : (x : Fin tvars) → Term tyvars tvars
  ƛ : Type tyvars → Term tyvars (suc tvars) → Term tyvars tvars
  Λ : Type tyvars → Term (suc tyvars) tvars → Term tyvars tvars
  _∙_ : Term tyvars tvars → Term tyvars tvars → Term tyvars tvars
  _∘_ : Term tyvars tvars → Type tyvars → Term tyvars tvars

module TypeSubst {T : ℕ → Set} (l : Lift T Type) where
  infixl 8 _/_

  open Lift l

  _/_ : ∀ {m n : ℕ} → Type m → Sub T m n → Type n
  ⊤ / _ = ⊤
  TyVar x / σ = lift (Vec.lookup σ x)
  (τ₁ ⇒ τ₂) / σ = (τ₁ / σ) ⇒ (τ₂ / σ)
  ℿ τ / σ = ℿ (τ / σ ↑)

  private
    appType : Application Type T
    appType = record { _/_ = _/_ }

  open Application appType

module Substitution where
  typeSubst : TermSubst Type
  typeSubst = record { var = TyVar; app = TypeSubst._/_ }

  module VarTypeSubst = TypeSubst (TermSubst.varLift typeSubst)

  varApp : Application Type Fin
  varApp = record { _/_ = VarTypeSubst._/_ }

  open Application varApp public using () renaming (_/_ to _/Var_)

  weaken : ∀{n : ℕ} → Type n → Type (suc n)
  weaken t = t /Var VarSubst.wk

module TypeContext where
  open Context public hiding (Ctx)

  Ctx : ℕ → Set
  Ctx = Context.Ctx Type

  weakenOps : Extension Type
  weakenOps = record { weaken = Substitution.weaken }

  open Context.WeakenOps Type weakenOps public

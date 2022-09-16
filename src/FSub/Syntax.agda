module FSub.Syntax where

open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Fin.Substitution.Extra
open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec as Vec
import Data.Context as Context

data Type (n : ℕ) : Set where
  ⊤ : Type n
  TyVar : Fin n → Type n
  _⇒_ : Type n → Type n → Type n
  ℿ : Type n → Type (suc n) → Type n

-- It would be good to be able to distinguish between type and term variables
data Term (n : ℕ) : Set where
  TVar : Fin n → Term n
  ƛ : Type n → Term (suc n) → Term n
  Λ : Type n → Term (suc n) → Term n
  _∙_ : Term n → Term n → Term n
  _◎_ : Term n → Type n → Term n

module TypeApp {T : ℕ → Set} (l : Lift T Type) where
  infixl 8 _/_

  open Lift l

  _/_ : ∀ {m n : ℕ} → Type m → Sub T m n → Type n
  ⊤ / _ = ⊤
  TyVar x / σ = lift (Vec.lookup σ x)
  (τ₁ ⇒ τ₂) / σ = (τ₁ / σ) ⇒ (τ₂ / σ)
  ℿ T τ / σ = ℿ (T / σ) (τ / σ ↑)

  private
    appType : Application Type T
    appType = record { _/_ = _/_ }

  open Application appType using (_/✶_)

module TermApp {T : ℕ → Set}
               (tyLift : Lift T Type) (termLift : Lift T Term) where
  infixl 8 _/_

  open Lift termLift
  open TypeApp {T} tyLift using () renaming (_/_ to _/Ty_)

  _/_ : ∀ {m n : ℕ} → Term m → Sub T m n → Term n
  TVar x / σ = lift (Vec.lookup σ x)
  ƛ T t / σ = ƛ (T /Ty σ) (t / σ ↑)
  Λ T t / σ = Λ (T /Ty σ) (t / σ ↑)
  (t₁ ∙ t₂) / σ = (t₁ / σ) ∙ (t₂ / σ)
  (t ◎ τ) / σ = (t / σ) ◎ (τ /Ty σ)

  private
    appTerm : Application Term T
    appTerm = record { _/_ = _/_ }

  open Application appTerm using (_/✶_)

module TypeSubstitution where
  typeSubst : TermSubst Type
  typeSubst = record { var = TyVar; app = TypeApp._/_ }

  module VarTypeApp = TypeApp (TermSubst.varLift typeSubst)

  typeLift = TermSubst.termLift typeSubst
  module TypeTypeApp = TypeApp typeLift

  varTyApp : Application Type Fin
  varTyApp = record { _/_ = VarTypeApp._/_ }

  tyTyApp : Application Type Type
  tyTyApp = record { _/_ = TypeTypeApp._/_ }

  open Application varTyApp public using () renaming (_/_ to _/TyVar_)
  open Application tyTyApp public using () renaming (_/_ to _/TyTy_)

  weaken : ∀{n : ℕ} → Type n → Type (suc n)
  weaken t = t /TyVar VarSubst.wk

  open Lift typeLift
  plug : ∀{n : ℕ} → Type (suc n) → Type n → Type n
  plug t t' = t /TyTy (sub t')

module TypeContext where
  open Context public hiding (Ctx)

  Ctx : ℕ → Set
  Ctx = Context.Ctx Type

  weakenOps : Extension Type
  weakenOps = record { weaken = TypeSubstitution.weaken }

  open Context.WeakenOps Type weakenOps public

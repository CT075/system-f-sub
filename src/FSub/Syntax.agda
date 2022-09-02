module FSub.Syntax where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

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

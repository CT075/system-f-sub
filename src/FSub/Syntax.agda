module FSub.Syntax where

open import Data.Fin using (Fin; suc; zero)
import Data.Fin.Substitution as S
open import Data.Fin.Substitution.Lemmas
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Function

import Data.Vec as Vec
import Data.Context as C

data Type (n : ℕ) : Set where
  ⊤ : Type n
  TyVar : Fin n → Type n
  _⇒_ : Type n → Type n → Type n
  ℿ : Type n → Type (suc n) → Type n

-- TODO: Distinguish between the nats used for type and term variable
data Term (ts : ℕ) (vs : ℕ) : Set where
  TVar : Fin vs → Term ts vs
  ƛ : Type ts → Term ts (suc vs) → Term ts vs
  Λ : Type ts → Term (suc ts) vs → Term ts vs
  _∙_ : Term ts vs → Term ts vs → Term ts vs
  _◎_ : Term ts vs → Type ts → Term ts vs

module TypeApp {T : ℕ → Set} (l : S.Lift T Type) where
  infixl 8 _/_

  open S.Lift l

  _/_ : ∀ {m n : ℕ} → Type m → S.Sub T m n → Type n
  ⊤ / _ = ⊤
  TyVar x / σ = lift (Vec.lookup σ x)
  (τ₁ ⇒ τ₂) / σ = (τ₁ / σ) ⇒ (τ₂ / σ)
  ℿ t τ / σ = ℿ (t / σ) (τ / σ ↑)

  private
    appType : S.Application Type T
    appType = record { _/_ = _/_ }

  open S.Application appType

module TypeOps where
  private
    typeSubst : S.TermSubst Type
    typeSubst = record { var = TyVar; app = TypeApp._/_ }

    module VarTypeSubst = TypeApp (S.TermSubst.varLift typeSubst)

    typeLift = S.TermSubst.termLift typeSubst
    module TypeTypeSubst = TypeApp typeLift

    varApp : S.Application Type Fin
    varApp = record { _/_ = VarTypeSubst._/_ }

  open S.Application varApp public using () renaming (_/_ to _/Var_)

  weaken : ∀{n : ℕ} → Type n → Type (suc n)
  weaken t = t /Var S.VarSubst.wk

  weaken* : ∀{n : ℕ} → (m : ℕ) → Type n → Type (m + n)
  weaken* zero t = t
  weaken* (suc m) t = weaken (weaken* m t)

  private
    tyApp : S.Application Type Type
    tyApp = record { _/_ = TypeTypeSubst._/_ }

  open S.Application tyApp public using () renaming (_/_ to _/Ty_)
  open S.Lift typeLift using (sub)

  plug : ∀{n : ℕ} → Type (suc n) → Type n → Type n
  plug t t' = t /Ty (sub t')

  module Context where
    open C hiding (Ctx)

    Ctx : ℕ → Set
    Ctx = C.Ctx Type

    private
      weakenOps : Extension Type
      weakenOps = record { weaken = weaken }

    open C.WeakenOps Type weakenOps public

module TermOps where
  module Context where
    data Entry (ts : ℕ) : ℕ → Set where
      pack : {vs : ℕ} → Type ts → Entry ts vs

    unpack : ∀{ts vs : ℕ} → Entry ts vs → Type ts
    unpack (pack τ) = τ

    weakenVar : ∀{ts vs : ℕ} → Entry ts vs → Entry ts (suc vs)
    weakenVar (pack τ) = pack τ

    weakenType : ∀{ts vs : ℕ} → Entry ts vs → Entry (suc ts) vs
    weakenType (pack τ) = pack (TypeOps.weaken τ)

    open C hiding (Ctx)

    Ctx : ℕ → ℕ → Set
    Ctx ts = C.Ctx (Entry ts)

    weakenAll : ∀{ts vs : ℕ} → Ctx ts vs → Ctx (suc ts) vs
    weakenAll = map weakenType

    module _ {ts : ℕ} where
      private
        weakenOps : Extension (Entry ts)
        weakenOps = record { weaken = weakenVar }

      open C.WeakenOps (Entry ts) weakenOps public

module Context where
  open C using ([]; _∷_)

  record Ctx (ts : ℕ) (vs : ℕ) : Set where
    field
      tys : TypeOps.Context.Ctx ts
      vars : TermOps.Context.Ctx ts vs

  empty : Ctx zero zero
  empty = record { tys = []; vars = [] }

  infixr 5 `<:_∷_
  infixr 5 `∶_∷_

  open Ctx

  `<:_∷_ : ∀{ts vs : ℕ} → Type ts → Ctx ts vs → Ctx (suc ts) vs
  `<: τ ∷ Γ =
    record { tys = τ ∷ (tys Γ)
           ; vars = TermOps.Context.weakenAll (vars Γ)
           }

  `∶_∷_ : ∀{ts vs : ℕ} → Type ts → Ctx ts vs → Ctx ts (suc vs)
  `∶ τ ∷ Γ = record { tys = tys Γ ; vars = (TermOps.Context.pack τ) ∷ vars Γ }

  lookupTy : ∀{ts vs} → Ctx ts vs → (n : Fin ts) → Type ts
  lookupTy Γ = TypeOps.Context.lookup (tys Γ)

  lookupVar : ∀{ts vs} → Ctx ts vs → (n : Fin vs) → Type ts
  lookupVar {ts} {vs} Γ n =
    TermOps.Context.unpack (TermOps.Context.lookup (vars Γ) n)

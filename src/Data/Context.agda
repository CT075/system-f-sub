module Data.Context where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Unary using (Pred)

infixr 5 _∷_

data Ctx {ℓ} (T : Pred ℕ ℓ) : ℕ → Set ℓ where
  [] : Ctx T zero
  _∷_ : ∀ {n : ℕ} → T n → Ctx T n → Ctx T (suc n)

module _ {ℓ} {T : Pred ℕ ℓ} where
  head : ∀ {n : ℕ} → Ctx T (suc n) → T n
  head (t ∷ ts) = t

  tail : ∀ {n : ℕ} → Ctx T (suc n) → Ctx T n
  tail (t ∷ ts) = ts

  drop : ∀ {n : ℕ} m → Ctx T (m + n) → Ctx T n
  drop zero Γ = Γ
  drop (suc m) (_ ∷ Γ) = drop m Γ

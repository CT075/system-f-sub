module Data.Fin.Substitution.Extra where

open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (_∷_; map)
--open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Unary using (Pred)

record Extension {ℓ} (T : Pred ℕ ℓ) : Set ℓ where
  field weaken : ∀ {n} → T n → T (suc n)

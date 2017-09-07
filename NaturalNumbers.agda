module NaturalNumbers where

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  suc m + n = suc (m + n)
  infixr 5 _+_

  open import Logic

  assoc-+ : ∀ x y z → ((x + y) + z) ≡ (x + (y + z))
  assoc-+ zero y z = relf
  assoc-+ (suc x) y z = goal where
    IH : ((x + y) + z) ≡ (x + y + z)
    IH = assoc-+ x y z
    goal : suc ((x + y) + z) ≡ suc (x + y + z)
    goal = cong suc _ _ IH

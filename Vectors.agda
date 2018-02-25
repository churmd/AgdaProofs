module Vectors where

  open import NaturalNumbers

  data Vec (X : Set) : ℕ → Set where
    [] : Vec X zero
    _∷_ : ∀{n} → X → Vec X n → Vec X (suc n)

  vec-hd : {X : Set} {n : ℕ} → Vec X (suc n) → X
  vec-hd (x ∷ v) = x

  vec-tl : {X : Set} {n : ℕ} → Vec X (suc n) → Vec X n
  vec-tl (x ∷ v) = v

  

module List where

  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

  infixr 4 _∷_

  _++_ : {A : Set} → List A → List A → List A
  [] ++ y = y
  (x ∷ x₁) ++ y = x ∷ (x₁ ++ y)

  infixl 5 _++_

  open import Logic

  --List concatenation monoid proofs
  ++-id1 : {A : Set} → (xs : List A) → ([] ++ xs) ≡ xs
  ++-id1 xs = relf

  ++-id2 : {A : Set} → (xs : List A) → (xs ++ []) ≡ xs
  ++-id2 [] = relf
  ++-id2 (x ∷ xs) = cong (λ ■ → x ∷ ■) _ _ (++-id2 xs)

  ++-assoc : {A : Set} (xs ys zs : List A) →
                ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  ++-assoc [] ys zs = relf
  ++-assoc (x ∷ xs) ys zs = goal where
    IH : (xs ++ ys ++ zs) ≡ (xs ++ (ys ++ zs))
    IH = ++-assoc xs ys zs
    goal : (x ∷ xs ++ ys ++ zs) ≡ (x ∷ xs ++ (ys ++ zs))
    goal = cong (λ ■ → x ∷ ■) _ _ IH

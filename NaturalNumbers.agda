module NaturalNumbers where
  -- Data definition of the natural numbers
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  -- Addition
  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  suc m + n = suc (m + n)
  infixr 5 _+_

  open import Logic

  -- Addition identity 1
  add-id₁ : ∀ n → n ≡ (zero + n)
  add-id₁ n = relf

  -- Addition identity 2
  add-id₂ : ∀ n → n ≡ (n + zero)
  add-id₂ zero = relf
  add-id₂ (suc n) = cong suc _ _ (add-id₂ n)

  -- Associativity of Addition
  add-assoc : ∀ x y z → ((x + y) + z) ≡ (x + (y + z))
  add-assoc zero y z = relf
  add-assoc (suc x) y z = goal where
    IH : ((x + y) + z) ≡ (x + y + z)
    IH = add-assoc x y z
    goal : suc ((x + y) + z) ≡ suc (x + y + z)
    goal = cong suc _ _ IH

  -- A lemma to move a suc inside an addition
  suc-Lemma : ∀ n m → suc(n + m) ≡ (n + suc m)
  suc-Lemma zero m = relf
  suc-Lemma (suc n) m = goal where
    IH : suc (n + m) ≡ (n + suc m)
    IH = suc-Lemma n m
    goal : suc (suc (n + m)) ≡ suc (n + suc m)
    goal = cong suc _ _ IH

  -- commutativity of addition
  add-comm : ∀ m n → (m + n) ≡ (n + m)
  add-comm zero n = add-id₂ n
  add-comm (suc m) n = goal where
    IH : (m + n) ≡ (n + m)
    IH = add-comm m n

    P1 : suc (m + n) ≡ suc (n + m)
    P1 = cong suc _ _ IH

    P2 : suc(n + m) ≡ (n + suc m)
    P2 = suc-Lemma n m

    goal : suc (m + n) ≡ (n + suc m)
    goal = trans _ _ _ P1 P2

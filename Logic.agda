module Logic where

  data _≡_ {A : Set} : A → A → Set where
    relf : {x : A} → x ≡ x

  sym : {A : Set} → (a b : A) → a ≡ b → b ≡ a
  sym a .a relf = relf

  tran : {A : Set} → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
  tran a .a .a relf relf = relf

  cong : {A B : Set} → (f : A → B) → (a b : A) → a ≡ b → f a ≡ f b
  cong f a .a relf = relf

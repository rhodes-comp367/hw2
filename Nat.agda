module Nat where

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

plus : Nat → Nat → Nat
plus zero n = n
plus (suc m) n = suc (plus m n)

times : Nat → Nat → Nat
times zero n = zero
times (suc m) n = plus n (times m n)

data Nat= : Nat → Nat → Set where
  zero= : Nat= zero zero
  suc= : ∀ {m n} → Nat= m n → Nat= (suc m) (suc n)

refl : (n : Nat) → Nat= n n
refl zero = zero=
refl (suc n) = suc= (refl n)

sym : {m n : Nat} → Nat= m n → Nat= n m
sym zero= = zero=
sym (suc= e) = suc= (sym e)

trans : {l m n : Nat} → Nat= l m → Nat= m n → Nat= l n
trans zero= zero= = zero=
trans (suc= e) (suc= f) = suc= (trans e f)


module Int where

open import Nat

data Int : Set where
  -- (+ n) represents positive n.
  + : Nat → Int
  -- (- n) represents negative n.
  - : Nat → Int
  -- 0 can be represented as (+ zero) or (- zero).

ineg : Int → Int
ineg (+ n) = - n
ineg (- n) = + n

isuc : Int → Int
isuc (+ n) = + (suc n)
isuc (- zero) = + (suc zero)
isuc (- (suc n)) = - n

ipred : Int → Int
ipred (- n) = - (suc n)
ipred (+ zero) = - (suc zero)
ipred (+ (suc n)) = + n

iplus : Int → Int → Int
iplus (+ zero) n = n
iplus (- zero) n = n
iplus (+ (suc m)) n = isuc (iplus (+ m) n)
iplus (- (suc m)) n = ipred (iplus (- m) n)

data Int= : Int → Int → Set where
  +/- : Int= (+ zero) (- zero)
  -/+ : Int= (- zero) (+ zero)
  +/+ : {m n : Nat} → Nat= m n → Int= (+ m) (+ n)
  -/- : {m n : Nat} → Nat= m n → Int= (- m) (- n)

-- reflexivity of integer equality.
irefl : (i : Int) → Int= i i
irefl (+ n) = +/+ (refl n)
irefl (- n) = -/- (refl n)

-- applying `ineg` twice gives back the same integer.
ineg-ineg : (i : Int) → Int= (ineg (ineg i)) i
ineg-ineg = ?

-- applying `ipred` then `isuc` gives back the same integer.
isuc-ipred : (i : Int) → Int= (isuc (ipred i)) i
isuc-ipred = ?

-- symmetry of integer equality.
isym : {i j : Int} → Int= i j → Int= j i
isym = ?

-- transitivity of integer equality.
itrans : {i j k : Int} → Int= i j → Int= j k → Int= i k
itrans = ?

-- applying `isuc` to equal integers gives equal integers.
isuc= : {i j : Int} → Int= i j → Int= (isuc i) (isuc j)
isuc= = ?

-- adding zero & an integer gives the same integer.
iplus-zero1 : (i : Int) → Int= (iplus (+ zero) i) i
iplus-zero1 = ?

-- adding an integer & zero gives the same integer.
iplus-zero2 : (i : Int) → Int= (iplus i (+ zero)) i
iplus-zero2 = ?


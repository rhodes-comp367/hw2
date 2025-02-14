module IntSol where

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

irefl : (i : Int) → Int= i i
irefl (+ n) = +/+ (refl n)
irefl (- n) = -/- (refl n)

ineg-ineg : (i : Int) → Int= (ineg (ineg i)) i
ineg-ineg (+ n) = +/+ (refl n)
ineg-ineg (- n) = -/- (refl n)

isuc-ipred : (i : Int) → Int= (isuc (ipred i)) i
isuc-ipred (- n) = -/- (refl n)
isuc-ipred (+ zero) = -/+
isuc-ipred (+ (suc n)) = +/+ (suc= (refl n))

isym : {i j : Int} → Int= i j → Int= j i
isym +/- = -/+
isym -/+ = +/-
isym (+/+ e) = +/+ (sym e)
isym (-/- e) = -/- (sym e)

itrans : {i j k : Int} → Int= i j → Int= j k → Int= i k
itrans +/- -/+ = +/+ zero=
itrans -/+ +/- = -/- zero=
itrans +/- (-/- zero=) = +/-
itrans -/+ (+/+ zero=) = -/+
itrans (+/+ zero=) +/- = +/-
itrans (-/- zero=) -/+ = -/+
itrans (+/+ e) (+/+ f) = +/+ (trans e f)
itrans (-/- e) (-/- f) = -/- (trans e f)

isuc= : {i j : Int} → Int= i j → Int= (isuc i) (isuc j)
isuc= +/- = +/+ (suc= zero=)
isuc= -/+ = +/+ (suc= zero=)
isuc= (+/+ e) = +/+ (suc= e)
isuc= (-/- zero=) = +/+ (suc= zero=)
isuc= (-/- (suc= e)) = -/- e

ipred= : {i j : Int} → Int= i j → Int= (ipred i) (ipred j)
ipred= +/- = -/- (suc= zero=)
ipred= -/+ = -/- (suc= zero=)
ipred= (+/+ zero=) = -/- (suc= zero=)
ipred= (+/+ (suc= e)) = +/+ e
ipred= (-/- e) = -/- (suc= e)

iplus-zero1 : (i : Int) → Int= (iplus (+ zero) i) i
iplus-zero1 i = irefl i

iplus-zero2 : (i : Int) → Int= (iplus i (+ zero)) i
iplus-zero2 (+ zero) = +/+ zero=
iplus-zero2 (- zero) = +/-
iplus-zero2 (+ (suc n)) = isuc= (iplus-zero2 (+ n))
iplus-zero2 (- (suc n)) = ipred= (iplus-zero2 (- n))


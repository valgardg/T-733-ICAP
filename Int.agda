module Int where

open import Nat hiding (_+'_)
open import PropositionalEquality



-- Integers with zero, suc, pred

data ℤ''' : Set where
  zero : ℤ'''
  suc : ℤ''' → ℤ'''         -- intuitively, suc i = i + 1
  pred : ℤ''' → ℤ'''        -- pred i = i - 1


{-
What we really want is not ℤ''', but a certain *quotient* of it,
by an equivalence relation discussed below. 
-}

~'''_ : ℤ''' → ℤ'''
~''' zero = zero
~''' (suc i) = pred (~''' i)
~''' (pred i) = suc (~''' i) 

infix 10 ~'''_

_+'''_ : ℤ''' → ℤ''' → ℤ'''
zero +''' j = j
suc i +''' j =  suc (i +''' j)
pred i +''' j =  pred (i +''' j)  

infixl 6 _+'''_ 


_-'''_ : ℤ''' → ℤ''' → ℤ'''
i -''' j = i +''' ~''' j

infixl 6 _-'''_


_*'''_ : ℤ''' → ℤ''' → ℤ'''
zero *''' j = zero
suc i *''' j = j +''' (i *''' j)
pred i *''' j = ~''' j +''' (i *''' j)

infixl 7 _*'''_




data _≡'''_ : ℤ''' → ℤ''' → Set where
  zero-zero : zero ≡''' zero
  cong-suc : {i j : ℤ'''} → i ≡''' j → suc i ≡''' suc j
  cong-pred : {i j : ℤ'''} → i ≡''' j → pred i ≡''' pred j 
  pred-suc : {i : ℤ'''} → pred (suc i) ≡''' i
  suc-pred : {i : ℤ'''} → suc (pred i) ≡''' i
  pred-sucʳ : {i : ℤ'''} → i ≡''' pred (suc i)
  suc-predʳ : {i : ℤ'''} → i ≡''' suc (pred i)
  trans''' : {i j k : ℤ'''} → i ≡''' j → j ≡''' k → i ≡''' k 


{-
_≡'''_ : ℤ''' → ℤ''' → Set
i ≡''' j = conv'' i ≡'' conv'' j
-}



-- "Difference integers"


data ℤ'' : Set where
  [_:-_] : ℕ → ℕ → ℤ''

infix 5 [_:-_]

pos : ℤ'' → ℕ
pos [ p :- _ ] = p

neg : ℤ'' → ℕ
neg [ _ :- n ] = n

conv'' : ℤ''' → ℤ''
{-
conv'' zero = [ zero :- zero ]
conv'' (suc i)  =  [ suc (pos (conv'' i)) :- neg (conv'' i) ] 
conv'' (pred i) =  [ pos (conv'' i) :- suc (neg (conv'' i)) ] 
-}
conv'' zero =  [ zero :- zero ]
conv'' (suc i) with conv'' i
... | [ p :- n ] =  [ suc p :- n ] 
conv'' (pred i) with conv'' i
... | [ p :- n ] =  [ p :- suc n ] 


~''_ : ℤ'' → ℤ''
~'' [ p :- n ] = [ n :- p ]

infix 10 ~''_


_+''_ : ℤ'' → ℤ'' → ℤ''
[ p :- n ] +'' [ q :- m ] = [ p + q :- n + m ]

infixl 6 _+''_

_*''_ : ℤ'' → ℤ'' → ℤ''
[ p :- n ] *'' [ q :- m ] = [  p * q + n * m :-  p * m + n * q ]

infixl 7 _*''_

_≡''_ : ℤ'' → ℤ'' → Set
[ p :- n ] ≡'' [ q :- m ] =  p + m ≡ n + q 

infix 5 _≡''_


~''-≡'' : (i i* : ℤ'') → i ≡'' i* → ~'' i ≡'' ~'' i*
~''-≡'' [ p :- n ] [ p* :- n* ] r = sym r

+''-≡'' : (i i* : ℤ'') → (j j* : ℤ'') →
                            i ≡'' i* → j ≡'' j* → i +'' j ≡'' i* +'' j*
+''-≡'' [ p :- n ] [ p* :- n* ] [ q :- m ] [ q* :- m* ] r s = {!!}


-- Signed naturals

data ℤ' : Set where
  ⊞_ : ℕ → ℤ'
  ⊟_ : ℕ → ℤ'

infix 8 ⊞_
infix 8 ⊟_

~' : ℤ' → ℤ'
~' (⊞ n) = ⊟ n
~' (⊟ n) = ⊞ n


_⊖_ : ℕ → ℕ → ℤ'
m ⊖ zero = ⊞ m 
zero ⊖ suc n = ⊟ suc n
suc m ⊖ suc n = m ⊖ n
 

_+'_ : ℤ' → ℤ' → ℤ'
⊞ m +' ⊞ n = ⊞ (m + n)
⊞ m +' ⊟ n = m ⊖ n
⊟ m +' ⊞ n = n ⊖ m
⊟ m +' ⊟ n = ⊟ (m + n) 

infixl 6 _+'_


_*'_ : ℤ' → ℤ' → ℤ'
_*'_ = {!!} 


conv' : ℤ'' → ℤ'
conv' [ p :- n ] =  p ⊖ n 

infix 5 _≡'_

data _≡'_ : ℤ' → ℤ' → Set where
  refl : {i : ℤ'} → i ≡' i
  ⊞⊟-zero : ⊞ zero ≡' ⊟ zero
  ⊟⊞-zero : ⊟ zero ≡' ⊞ zero


~'-≡' : (i i* : ℤ') → i ≡' i* → ~' i ≡' ~' i*
~'-≡' i .i refl = refl
~'-≡' .(⊞ 0) .(⊟ 0) ⊞⊟-zero = ⊟⊞-zero
~'-≡' .(⊟ 0) .(⊞ 0) ⊟⊞-zero = ⊞⊟-zero 

+'-≡' : (i i* : ℤ') → (j j* : ℤ') → i ≡' i* → j ≡' j* → i +' j ≡' i* +' j*
+'-≡' i .i j .j refl refl = refl
+'-≡' i .i .(⊞ 0) .(⊟ 0) refl ⊞⊟-zero = {!!}  -- need digging deeper, some lemmas
+'-≡' i .i .(⊟ 0) .(⊞ 0) refl ⊟⊞-zero = {!!}
+'-≡' .(⊞ 0) .(⊟ 0) (⊞ m) (⊞ m*) ⊞⊟-zero q = q
+'-≡' .(⊞ 0) .(⊟ 0) (⊞ m) (⊟ m*) ⊞⊟-zero q = q
+'-≡' .(⊞ 0) .(⊟ 0) (⊟ 0) (⊞ .0) ⊞⊟-zero ⊟⊞-zero = refl
-- +'-≡' .(⊞ 0) .(⊟ 0) (⊟ (suc m)) (⊞ m*) ⊞⊟-zero ()
+'-≡' .(⊞ 0) .(⊟ 0) (⊟ 0) (⊟ .0) ⊞⊟-zero refl = ⊞⊟-zero
+'-≡' .(⊞ 0) .(⊟ 0) (⊟ suc m) (⊟ m*) ⊞⊟-zero q = q
+'-≡' .(⊟ 0) .(⊞ 0) (⊞ m) (⊞ m*) ⊟⊞-zero q = q
+'-≡' .(⊟ 0) .(⊞ 0) (⊞ .0) (⊟ 0) ⊟⊞-zero ⊞⊟-zero = refl
+'-≡' .(⊟ 0) .(⊞ 0) (⊟ m) (⊞ m*) ⊟⊞-zero q = q
+'-≡' .(⊟ 0) .(⊞ 0) (⊟ .0) (⊟ 0) ⊟⊞-zero refl = ⊟⊞-zero
+'-≡' .(⊟ 0) .(⊞ 0) (⊟ .(suc m*)) (⊟ suc m*) ⊟⊞-zero refl = refl 



-- Signed naturals, negatives shifted by one

data ℤ : Set where
  ⊞_ : ℕ → ℤ
  ⊟suc_ : ℕ → ℤ

conv : ℤ' → ℤ
conv (⊞ m) = ⊞ m
conv (⊟ zero) = ⊞ zero
conv (⊟ suc m) = ⊟suc m 


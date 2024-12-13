-- Intro to computer-assisted proof

-- Natural numbers

{-# OPTIONS --allow-unsolved-metas #-}

module Nat where

open import PropositionalEquality
open import Bool
open import Logic

{-
ℕ is entered as \bN
-}

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two 

{-# BUILTIN NATURAL ℕ #-}


_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

--{-# BUILTIN NATPLUS _+_ #-}

infixl 6 _+_


_+'_ : ℕ → ℕ → ℕ
zero  +' m = m
suc m +' n = m +' suc n

infixl 6 _+'_

+-identityˡ : (m : ℕ) → zero + m ≡ m
+-identityˡ m = proof
    zero + m
  =⟨⟩  
    m
  ∎

+-identityʳ : (m : ℕ) → m + zero ≡ m
+-identityʳ zero = proof
    zero + zero
  =⟨⟩
    zero
  ∎  
+-identityʳ (suc m) = proof
    (suc m) + zero
  =⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m 
  ∎

+-assoc : (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc m n p = {!!}

+-lemma : (m n : ℕ) → m + suc n ≡ suc (m + n)
+-lemma zero n = refl
+-lemma (suc m) n = cong suc (+-lemma m n)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-identityʳ n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-lemma n m))  


_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n =  n + (m * n)  


infixl 7 _*_


*-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc m n p = {!!}


*-zeroʳ : (m : ℕ) → m * zero ≡ zero
*-zeroʳ m = {!!}

*-suc : (m n : ℕ) → m * suc n ≡ m + m * n
*-suc m n = {!!} 

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm m n = {!!}

*-distribʳ : (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distribʳ zero n p = refl
*-distribʳ (suc m) n p = -- trans (cong (_+_ p) (*-distribʳ m _ _)) (sym (+-assoc p _ _ ))
 proof
   (suc m + n) * p
 =⟨⟩
   suc (m + n) * p
 =⟨⟩  
   p + (m + n) * p
 ≡⟨ cong (_+_ p) (*-distribʳ m n p)  ⟩  
   p + (m * p + n * p)
 ≡⟨ sym (+-assoc p _ _) ⟩
   (p + m * p) + n * p
 =⟨⟩
   suc m * p + n * p
 ∎
 
_^_ : ℕ → ℕ → ℕ
m ^ zero = one                  -- we should probably worry about zero ^ zero
m ^ suc n = m * (m ^ n) 

infixr 8 _^_

^-distribˡ : (m n p : ℕ) → m ^ (n + p) ≡ m ^ n * m ^ p
^-distribˡ m zero p = sym (+-identityʳ _)
^-distribˡ m (suc n) p = proof
   m ^ (suc n + p)
 =⟨⟩
   m ^ (suc (n + p))
 =⟨⟩
   m * m ^ (n + p)
 ≡⟨ cong (_*_ m) (^-distribˡ m n p) ⟩
   m * (m ^ n * m ^ p)
 ≡⟨ sym (*-assoc m _ _) ⟩
   (m * m ^ n) * m ^ p
 =⟨⟩
   m ^ (suc n) * m ^ p
 ∎

^-distribʳ : (m n p : ℕ) → (m * n) ^ p ≡ m ^ p * n ^ p
^-distribʳ m n zero = refl
^-distribʳ m n (suc p) = proof
    (m * n) ^ (suc p)
  =⟨⟩
    (m * n) * (m * n) ^ p
  ≡⟨ cong (_*_ (m * n)) (^-distribʳ m n p) ⟩
    (m * n) * (m ^ p * n ^ p)
  ≡⟨ sym (*-assoc (m * n) _ _) ⟩
    ((m * n) * m ^ p) * n ^ p
  ≡⟨ cong (λ q → q * n ^ p) (*-assoc m _ _) ⟩
    (m * (n * m ^ p)) * n ^ p
  ≡⟨ cong (λ q → (m * q) * n ^ p) (*-comm n _) ⟩
    (m * (m ^ p * n)) * n ^ p
  ≡⟨ cong (λ q → q * n ^ p) (sym (*-assoc m _ _)) ⟩
    ((m * m ^ p) * n) * n ^ p
  ≡⟨ *-assoc (m * m ^ p) _ _ ⟩
    (m * m ^ p) * (n * n ^ p)
  =⟨⟩
    m ^ (suc p) * n ^ (suc p)
  ∎

^-act : (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^-act m n zero = cong (_^_ m) (*-zeroʳ n)
^-act m n (suc p) = proof
    m ^ (n * suc p)
  ≡⟨ cong (_^_ m) (*-suc n _) ⟩
    m ^ (n + n * p)
  ≡⟨ ^-distribˡ _ n _ ⟩
    m ^ n * m ^ (n * p)
  ≡⟨ cong (_*_ (m ^ n)) (^-act m n p) ⟩
    m ^ n * (m ^ n) ^ p
  =⟨⟩
   (m ^ n) ^ suc p
  ∎



{-
∸ is entered as \.-
-}

_∸_ : ℕ → ℕ → ℕ       -- "monus" 
m      ∸ zero = m
zero  ∸ suc n = zero       -- note this case!
suc m ∸ suc n = m ∸ n 

infixl 6 _∸_



-- deciding equality of naturals

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc _ = false
suc _ == zero  = false
suc m == suc n = m == n


==-true : (m n : ℕ) → m == n ≡ true → m ≡ n
==-true zero zero p = refl
==-true zero (suc _) ()
==-true (suc _) zero ()
==-true (suc m) (suc n) p =  cong suc (==-true m n p)   

suc-injective : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

==-false : (m n : ℕ) → m == n ≡ false → ¬ m ≡ n
==-false zero zero () q
==-false zero (suc _) p ()
==-false (suc _) zero p ()
==-false (suc m) (suc n) p q = (==-false m n p)  (suc-injective q) 




{-
≟ is entered as \?=
-}


_≟_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc _ = no (λ ()) 
suc m ≟ zero  = no (λ ()) 
suc m ≟ suc n with m ≟ n
...   | yes p = yes (cong suc p) 
...   | no ¬p = no  (λ q → ¬p (suc-injective q))


lemma : (m n : ℕ) → ⌊ m ≟ n ⌋ ≡ ⌊ suc m ≟ suc n ⌋
lemma m n with m ≟ n
lemma m n | yes p = refl
lemma m n | no ¬p = refl

==-correct : (m n : ℕ) → m == n ≡ ⌊ m ≟ n ⌋
==-correct zero zero = refl
==-correct zero (suc n) = refl
==-correct (suc m) zero = refl
==-correct (suc m) (suc n) = trans (==-correct m n) (lemma m n) 



{-
_≟_ : (m n : ℕ) → Dec (m ≡ n)
m ≟ n with m == n
... | false = no (==-false m n {!!})
... | true = yes (==-true m n {!!} )
-}




{-
≤ is entered as \le
-}

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_


1≤4 : 1 ≤ 4
1≤4 = s≤s (z≤n {3})

≤-suc : {m : ℕ} → m ≤ suc m
≤-suc {zero} = z≤n 
≤-suc {suc m} = s≤s (≤-suc {m}) 

≤-refl : {m : ℕ} → m ≤ m
≤-refl {zero} = z≤n
≤-refl {suc m} = s≤s ≤-refl 

≤-trans : {m n o : ℕ} → m ≤ n → n ≤ o → m ≤ o
≤-trans {.0} {n} {o} z≤n q = z≤n {o}
≤-trans {.(suc m)} {.(suc n)} {.(suc o)} (s≤s {m} {n} p) (s≤s {.n} {o} q) = s≤s (≤-trans {m} {n} {o} p q) 

≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {.0} {.0} z≤n z≤n = refl
≤-antisym {.(suc _)} {.(suc _)} (s≤s p) (s≤s q) =  cong suc (≤-antisym p q)

≤-total : {x y : ℕ} → ¬ x ≤ y → y ≤ x
≤-total {zero} {y} p with p z≤n 
... | () 
≤-total {suc x} {zero} p = z≤n
≤-total {suc x} {suc y} p = s≤s (≤-total {x} {y} (λ q → p (s≤s q)))   

≤-pred : {m n : ℕ} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s p) = p

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes (z≤n {n})
suc m ≤? zero = no (λ ()) 
suc m ≤? suc n with m ≤? n
... | yes p = yes (s≤s p)
... | no ¬p = no (λ q → ¬p (≤-pred q))   



data _≤'_ (m : ℕ) : ℕ → Set where
  ≤'-refl : m ≤' m
  ≤'-step : {n : ℕ} → m ≤' n → m ≤' suc n

infix 4 _≤'_


1≤'4 : 1 ≤' 4
1≤'4 = ≤'-step (≤'-step (≤'-step ≤'-refl))


data _≤''_ (m n : ℕ) : Set where
  diff : {k : ℕ} → k + m ≡ n → m ≤'' n

1≤''4 : 1 ≤'' 4
1≤''4 = diff {_} {_} {3} refl


z≤'n : {n : ℕ} → zero ≤' n
z≤'n {zero} = ≤'-refl
z≤'n {suc n} =  ≤'-step (z≤'n {n}) 

s≤'s : {m n : ℕ} → m ≤' n → suc m ≤' suc n
s≤'s {m} {.m} ≤'-refl = ≤'-refl
s≤'s {m} {.(suc _)} (≤'-step p) = ≤'-step (s≤'s {m} {_} p) 

≤-≤' : {m n : ℕ} → m ≤ n → m ≤' n
≤-≤' {.0} {n} z≤n = z≤'n {n}
≤-≤' {.(suc _)} {.(suc _)} (s≤s {m} {n} p) = s≤'s {m} {n} (≤-≤' {m} {n} p) 


 
postulate x : ℕ
postulate y : ℕ

module Vec where

open import PropositionalEquality
open import Nat
open import Fin


infixr 5 _∷_

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)


head : {n : ℕ} → {A : Set} → Vec A (suc n) → A
head (x ∷ xs) = x 

tail : {n : ℕ} → {A : Set} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs 

infixr 5 _++_

_++_ : {m n : ℕ} → {A : Set} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys =  x ∷ xs ++ ys  


cast : {m n : ℕ} → {A : Set} → m ≡ n → Vec A m → Vec A n
cast refl xs = xs


concat : {m n : ℕ} → {A : Set} → Vec (Vec A n) m → Vec A (m * n) 
concat [] =  []
concat (xs ∷ xss) =  xs ++ concat xss 


lookup : {n : ℕ} → {A : Set} → Vec A n → Fin n → A 
--lookup [] () 
lookup (x ∷ _) zero = x
lookup (_ ∷ xs) (suc i) = lookup xs i


removeAt : {n : ℕ} → {A : Set} → Vec A (suc n) → Fin (suc n) → Vec A n 
removeAt (_ ∷ xs) zero = xs
removeAt (x ∷ xs@(_ ∷ _)) (suc i) =  x ∷ removeAt xs i 


insertAt : {n : ℕ} → {A : Set} → Vec A n → Fin (suc n) → A → Vec A (suc n)
insertAt xs zero x =  x ∷ xs
insertAt (x ∷ xs) (suc i) x' =  x ∷ insertAt xs i x' 

insert-remove-lookupAt : {n : ℕ} → {A : Set} → (xs : Vec A (suc n)) → (i : Fin (suc n)) →
          insertAt (removeAt xs i) i (lookup xs i) ≡ xs
insert-remove-lookupAt (x ∷ xs) zero = refl
insert-remove-lookupAt (x ∷ xs@(_ ∷ _)) (suc i) = cong (_∷_ x) (insert-remove-lookupAt xs i)



reverse : {n : ℕ} → {A : Set} → Vec A n → Vec A n
reverse [] = [] -- []
reverse {suc n} (x ∷ xs) = cast (+-comm n _) (reverse xs ++ (x ∷ [])) 


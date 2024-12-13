-- Intro to computer-assisted proof

-- Lists 


module List where

open import PropositionalEquality
open import Bool
open import Nat
open import Logic


{-
∷ is entered as \::
-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_


[_] : {A : Set} → A → List A
[ x ] = x ∷ []


[_,_] : {A : Set} → A → A → List A
[ x , y ] = x ∷ y ∷ []



_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

++-identityˡ : {A : Set} → (xs : List A) → [] ++ xs ≡ xs
++-identityˡ _ = refl

++-identityʳ : {A : Set} → (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
{-
   [] ++ []
 = []
-}
++-identityʳ (x ∷ xs) = cong (_∷_ x) (++-identityʳ xs)
{-
   (x ∷ xs) ++ []
 = x ∷ (xs ++ [])
 ≡ x ∷ xs
-}

++-assoc : {A : Set} → (xs ys zs : List A) →
                             (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
{-
   ([] ++ ys) ++ zs
 = ys ++ xz
 = [] ++ (ys ++ zs)   
-}
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs) 
{-
   ((x ∷ xs) ++ ys) ++ zs)
 = x ∷ ((xs ++ ys) ++ zs)
 ≡ x ∷ (xs ++ (ys ++ zs))
 = (x ∷ xs) ++ (ys ++ zs)
-}

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ] 



reverse-++ : {A : Set} → (xs ys : List A) →
                         reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] ys = proof
   reverse ([] ++ ys) 
 =⟨⟩
   reverse ys
 ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
   reverse ys ++ []
 =⟨⟩
   reverse ys ++ reverse []
 ∎
{- 
reverse-++ [] ys = sym (++-identityʳ (reverse ys))
-}
{-
   reverse ([] ++ ys) 
 = reverse ys
 ≡ reverse ys ++ []
 = reverse ys ++ reverse []
-}
reverse-++ (x ∷ xs) ys = proof
   reverse ((x ∷ xs) ++ ys) 
 =⟨⟩
   reverse (xs ++ ys) ++ [ x ]
 ≡⟨ cong (λ zs → zs ++ _) (reverse-++ xs ys) ⟩
   (reverse ys ++ reverse xs) ++ [ x ]
 ≡⟨ (++-assoc (reverse ys) _ _) ⟩
   reverse ys ++ (reverse xs ++ [ x ])
 =⟨⟩
   reverse ys ++ reverse (x ∷ xs)
 ∎
{- 
reverse-++ (x ∷ xs) ys = trans
     (cong (λ zs → zs ++ [ x ]) (reverse-++ xs ys))
     (++-assoc (reverse ys) (reverse xs) [ x ])  
-}
{-
   reverse ((x ∷ xs) ++ ys) 
 = reverse (xs ++ ys) ++ [ x ]
 ≡ (reverse ys ++ reverse xs) ++ [ x ]
 ≡ reverse ys ++ (reverse xs ++ [ x ])
 = reverse ys ++ reverse (x ∷ xs)
-}

reverse-invol : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-invol [] = refl
{-
   reverse (reverse []) 
 = []
-}
reverse-invol (x ∷ xs) = trans
     (reverse-++ (reverse xs) [ x ])
     (cong (_∷_ x) (reverse-invol xs)) 
{-
   reverse (reverse (x ∷ xs)) 
 = reverse (reverse xs ++ [ x ])
 ≡ reverse [x] ++ reverse (reverse xs)
 = x ∷ reverse (reverse xs)
 ≡ x ∷ xs
-}



reverseAcc : {A : Set} → List A → List A → List A
reverseAcc acc [] = acc
reverseAcc acc (x ∷ xs) = reverseAcc (x ∷ acc) xs

reverse' : {A : Set} → List A → List A
reverse' xs = reverseAcc [] xs


reverseAcc-reverse : {A : Set} → (acc xs : List A) →
       reverseAcc acc xs ≡ reverse xs ++ acc
reverseAcc-reverse acc [] = refl
{-
    reverseAcc acc []
  = acc
  = [] ++ acc
    reverse [] ++ acc   
-}
reverseAcc-reverse acc (x ∷ xs) = trans
      (reverseAcc-reverse (x ∷ acc) xs)
      (sym (++-assoc (reverse xs) [ x ] acc) ) 
{-
    reverseAcc acc (x ∷ xs)
  = reverseAcc (x ∷ acc) xs 
  ≡ reverse xs ++ (x ∷ acc)
  = reverse xs ++ ([ x ] ++ acc)
  ≡ (reverse xs ++ [ x ]) ++ acc
  = reverse (x ∷ xs) ++ acc
-}

reverse'-reverse : {A : Set} → (xs : List A) → reverse' xs ≡ reverse xs
reverse'-reverse xs = trans (reverseAcc-reverse [] xs) (++-identityʳ (reverse xs)) 
{-
    reverse' xs
 =  reverseAcc [] xs
 ≡  reverse xs ++ []
 ≡  reverse xs
-}


length : {A : Set} → List A → ℕ
length [] = zero
length (_ ∷ xs) = suc (length xs)


++-length : {A : Set} → (xs ys : List A) →
                 length (xs ++ ys) ≡ length xs + length ys
++-length [] _ = refl
++-length (x ∷ xs) ys = cong suc (++-length xs ys) 




map : {A B : Set} → (A → B) → List A → List B
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs


map-++ : {A B : Set} → (f : A → B) → (xs ys : List A) →
                     map f (xs ++ ys) ≡  map f xs ++ map f ys
map-++ f [] ys = refl
{-
    map f ([] ++ ys)
  = map f ys
  = [] ++ map f ys
    map f [] ++ map f ys
-}
map-++ f (x ∷ xs) ys = cong (_∷_ (f x)) (map-++ f xs ys) 
{-
    map f ((x ∷ xs) ++ ys)
  = map f (x ∷ (xs ++ ys))
  = f x ∷ map f (xs ++ ys))
  ≡ f x ∷ (map f xs ++ map f ys)
  = (f x ∷ map f xs) ++ map f ys
    map f (x ∷ xs) ++ map f ys
-}

map-reverse : {A B : Set} → (f : A → B) → (xs : List A) →
                     map f (reverse xs) ≡ reverse (map f xs)
map-reverse f [] = refl
{-
    map f (reverse []) 
  = map f []
  = []
  = reverse [] 
    reverse (map f [])
-}
map-reverse f (x ∷ xs) = trans
      (map-++ f (reverse xs) [ x ])
      (cong (λ zs → zs ++ [ f x ]) (map-reverse f xs))  
{-
    map f (reverse (x ∷ xs))
  = map f (reverse xs ++ [ x ])
  ≡ map f (reverse xs) ++ map f [ x ]
  = map f (reverse xs) ++ [ f x ]
  ≡ reverse (map f xs) ++ [ f x ]
  = reverse (f x ∷ map f xs)
    reverse (map f (x ∷ xs))
-}


{-
ᵇ is entered as \^b
-}


{-
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)
-}

filterᵇ : {A : Set} → (A → Bool) → List A → List A
filterᵇ _ [] = []
filterᵇ p (x ∷ xs) =
      if p x then x ∷ filterᵇ p xs else filterᵇ p xs


if-kjartan : {A B : Set} → (f : A → B) → (b : Bool) → (x y : A) →
                       f (if b then x else y) ≡ (if b then f x else f y)   
if-kjartan f false x y = refl
if-kjartan f true x y = refl 

filterᵇ-++ :  {A : Set} → (p : A → Bool) → (xs ys : List A) →
                     filterᵇ p (xs ++ ys) ≡ filterᵇ p xs ++ filterᵇ p ys
filterᵇ-++ p [] ys = refl
{-
    filterᵇ p ([] ++ ys)
  = filterᵇ p ys
  = [] ++ filterᵇ p ys
    filterᵇ p [] ++ filterᵇ p ys
-}
filterᵇ-++ p (x ∷ xs) ys = trans
      (cong (λ zs → if p x then x ∷ zs else zs) (filterᵇ-++ p xs ys))
      (sym (if-kjartan (λ zs → zs ++ filterᵇ p ys) (p x) _ _))



map-filterᵇ : {A B : Set} → (f : A → B) → (p : B → Bool) →
      (xs : List A) →
      map f (filterᵇ (λ x → p (f x)) xs) ≡ filterᵇ p (map f xs)
map-filterᵇ f p [] = refl
map-filterᵇ f p (x ∷ xs) = trans
     (if-kjartan (map f) (p (f x)) (x ∷ filterᵇ (λ z → p (f z)) xs)
                                   (filterᵇ (λ z → p (f z)) xs))
     (cong (λ zs → if p (f x) then f x ∷ zs else zs) (map-filterᵇ f p xs)) 



filterᵇ-length : {A : Set} → (p : A → Bool) → (xs : List A) →
      length (filterᵇ p xs) ≤ length xs
filterᵇ-length p [] = z≤n {zero} 
filterᵇ-length p (x ∷ xs) with p x
... | false = ≤-trans ≤-suc (s≤s (filterᵇ-length p xs))
... | true  = s≤s (filterᵇ-length p xs) 




∈?ᵇ : {A : Set} → (A → A → Bool) → A → List A → Bool
∈?ᵇ _ x [] = false
∈?ᵇ _==_ x (y ∷ ys) with x == y
... | true  = true 
... | false = ∈?ᵇ _==_ x ys


_ℕ∈?ᵇ_ : ℕ → List ℕ → Bool
_ℕ∈?ᵇ_ = ∈?ᵇ (_==_)



-- List membership and deciding it


infix 3 _∈_

data _∈_ {A : Set} : A → List A → Set where
  h : {x : A} → {xs : List A} → x ∈ x ∷ xs
  þ : {x y : A} → {ys : List A} → x ∈ ys → x ∈ y ∷ ys

∈? : {A : Set} → Decidable (_≡_ {A}) → (x : A) → (ys : List A) → Dec (x ∈ ys) 
∈? _ x [] = no (λ ())
∈? (_≟_) x (y ∷ ys) with x ≟ y
∈? _     x (.x ∷ _) | yes refl = yes h   
... | no p with ∈? (_≟_) x ys
...    | yes q = yes (þ q)  
...    | no q  = no (λ { h → p refl ;
                         (þ r) → q r})


removeFirst : {A : Set} → Decidable (_≡_ {A}) → List A → A → List A
removeFirst _ [] y = []
removeFirst _≟_ (x ∷ xs) y with x ≟ y
... | yes _ = xs 
... | no _  = x ∷ removeFirst _≟_ xs y  

removeAll : {A : Set} → Decidable (_≡_ {A}) → List A → A → List A
removeAll _ [] y = []
removeAll _≟_ (x ∷ xs) y with x ≟ y
... | yes _ = removeAll _≟_ xs y
... | no _  = x ∷ removeAll _≟_ xs y  

removeGiven : {A : Set} → (xs : List A) → {y : A} → y ∈ xs → List A
removeGiven (_ ∷ xs) h = xs
removeGiven (x ∷ xs) (þ p) = x ∷ removeGiven xs p



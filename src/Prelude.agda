
open import Level

postulate
  undefined : ∀ {a : Set} -> a

const : {a b : Set} -> a -> b -> a
const x _ = x

id : {a : Set} -> a -> a
id x = x

_·_ : ∀ {l l' l''} {a : Set l} {b : Set l'} {c : Set l''} ->
      (b -> c) -> (a -> b) -> a -> c
f · g = λ x → f (g x)

data _==_ {l : Level} {a : Set l} (x : a) : a -> Set l where
  Refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL Refl #-}

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl p = p

infixr 2 _⟨_⟩_
_⟨_⟩_ : {a : Set} -> (x : a) -> { y z : a} -> x == y -> y == z -> x == z
_⟨_⟩_ x = trans

_■ : forall {a : Set} (x : a) -> x == x
_■ x = Refl

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ n + m = Succ (n + m)

_*_ : Nat -> Nat -> Nat
Zero * m = Zero
Succ n * m = m + (n * m)

_^_ : Nat -> Nat -> Nat
n ^ Zero = 1
n ^ Succ m = n * (n ^ m)

pred : Nat -> Nat
pred Zero = Zero
pred (Succ n) = n

--- Natural lemmas

zero-cancellative : (n : Nat) -> (n * Zero) == Zero
zero-cancellative Zero = Refl
zero-cancellative (Succ n) = zero-cancellative n


data Bool : Set where
  True : Bool
  False : Bool

if_then_else : {l : Level} {a : Set l} -> Bool -> a -> a -> a
if True then t else e = t
if False then t else e = e

boolElim : {l : Level} {P : Bool -> Set l} ->
  P True -> P False -> (b : Bool) -> P b
boolElim t f True = t
boolElim t f False = f

not : Bool -> Bool
not True = False
not False = True

record Pair {l l'} (a : Set l) (b : Set l') : Set (l ⊔ l') where
  constructor _,_
  field
    fst : a
    snd : b

curry : ∀ {l : Level} {a b c : Set l} -> (Pair a b -> c) -> a -> b -> c
curry f x y = f (x , y)

uncurry :  ∀ {l l' l'' : Level} {a : Set l} {b : Set l'} {c : Set l''} -> (a -> b -> c) -> Pair a b -> c
uncurry f (x , y) = f x y

data Either (a b : Set) : Set where
  Inl : a -> Either a b
  Inr : b -> Either a b

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

So : Bool -> Set
So True = ⊤
So False = ⊥

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

[_] : ∀ {a} -> a -> List a
[ x ] = Cons x Nil

_++_ :  ∀ {a} -> List a -> List a -> List a
Nil ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

filter : {a : Set} -> (a -> Bool) -> List a -> List a
filter p Nil = Nil
filter p (Cons x xs) =
  if p x then Cons x (filter p xs) else (filter p xs)

<=-dec : Nat -> Nat -> Bool
<=-dec Zero m = True
<=-dec (Succ n) Zero = False
<=-dec (Succ n) (Succ m) = <=-dec n m

>-dec : Nat -> Nat -> Bool
>-dec n m = not (<=-dec n m)

all : {a : Set} -> (P : a -> Bool) -> List a -> Set
all P Nil = ⊤
all P (Cons x xs) = Pair (So (P x)) (all P xs) 

data _<_ : Nat -> Nat -> Set where
  Base : ∀ {n} -> Zero < Succ n
  Step : ∀ {n m} -> n < m -> Succ n < Succ m

data Inspect {a} {A : Set a} (x : A) : Set a where
    _with-≡_ : (y : A) (eq : x == y) → Inspect x

inspect : ∀ {a} {A : Set a} (x : A) → Inspect x
inspect x = x with-≡ Refl

record Sigma {l l'} (a : Set l) (b : a -> Set l') : Set (l ⊔ l') where
  constructor _,_
  field
    fst : a
    snd : b fst

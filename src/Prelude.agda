

postulate
  undefined : ∀ {a : Set} -> a

_·_ : ∀ {l l' l''} {a : Set l} {b : Set l'} {c : Set l''} ->
      (b -> c) -> (a -> b) -> a -> c
f · g = λ x → f (g x)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

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

if_then_else : {a : Set} -> Bool -> a -> a -> a
if True then t else e = t
if False then t else e = e

record Pair (a b : Set) : Set where
  constructor _,_
  field
    fst : a
    snd : b

curry : ∀ {a b c : Set} -> (Pair a b -> c) -> a -> b -> c
curry f x y = f (x , y)

uncurry :  ∀ {a b c : Set} -> (a -> b -> c) -> Pair a b -> c
uncurry f (x , y) = f x y

data Either (a b : Set) : Set where
  Inl : a -> Either a b
  Inr : b -> Either a b

data ⊤ : Set where
  tt : ⊤

postulate
  U : Set
  elU : U -> Set

data P : Set where
  K : U -> P
  _=>_ : P -> P -> P

elP : P -> Set
elP (K u) = elU u
elP (p1 => p2) = elP p1 -> elP p2

data ⊥ : Set where

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

[_] : ∀ {a} -> a -> List a
[ x ] = Cons x Nil

_++_ :  ∀ {a} -> List a -> List a -> List a
Nil ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

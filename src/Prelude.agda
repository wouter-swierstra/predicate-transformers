
open import Level

postulate
  undefined : ∀ {a : Set} -> a

const : {l : Level} {a b : Set l} -> a -> b -> a
const x _ = x

id : {a : Set} -> a -> a
id x = x

flip : ∀ {l : Level} {a : Set l} {b : Set l} {c : Set l}
  -> (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

_·_ : ∀ {l l' l''} {a : Set l} {b : Set l'} {c : Set l''} ->
      (b -> c) -> (a -> b) -> a -> c
f · g = λ x → f (g x)

data _==_ {l : Level} {a : Set l} (x : a) : a -> Set l where
  Refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl p = p

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

cong2 : {a b c : Set} {x y : a} {z w : b} (f : a -> b -> c) -> x == y -> z == w -> f x z == f y w
cong2 f Refl Refl = Refl

coerce : {a b : Set} -> a == b -> a -> b
coerce Refl x = x

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

plus-zero : (n : Nat) -> n == (n + Zero)
plus-zero Zero = Refl
plus-zero (Succ n) = cong Succ (plus-zero n)


plus-succ : (x y : Nat) -> Succ (x + y) == (x + Succ y)
plus-succ Zero y = Refl
plus-succ (Succ x) y = cong Succ (plus-succ x y)


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

_×_ : ∀ {l l'} -> Set l -> Set l' -> Set (l ⊔ l')
_×_ A B  = Pair A B

infixr 20 _×_

record Triple {l l' l''} (a : Set l) (b : Set l') (c : Set l'') : Set (l ⊔ l' ⊔ l'') where
  constructor _,_,_
  field
    fst : a
    snd : b
    thd : c


curry : ∀ {l : Level} {a b c : Set l} -> (Pair a b -> c) -> a -> b -> c
curry f x y = f (x , y)

uncurry :  ∀ {l l' l'' : Level} {a : Set l} {b : Set l'} {c : Set l''} -> (a -> b -> c) -> Pair a b -> c
uncurry f (x , y) = f x y

data Either {l : Level} (a b : Set l) : Set l where
  Inl : a -> Either a b
  Inr : b -> Either a b

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

magic : ∀ {l} {a : Set l} -> ⊥ -> a
magic ()

So : Bool -> Set
So True = ⊤
So False = ⊥

¬ : ∀ {l} -> Set l -> Set l
¬ a = a -> ⊥

Decide : ∀ {l} (a : Set l) -> Set l
Decide a = Either a (¬ a)

decideFrom : (b : Bool) -> Decide (So b)
decideFrom True = Inl tt
decideFrom False = Inr λ z → z

data EqNat : (a b : Nat) -> Set where
  EqZero : EqNat 0 0
  EqSucc : {a b : Nat} -> EqNat a b -> EqNat (Succ a) (Succ b)

succ-inj-eq : {a b : Nat} -> EqNat (Succ a) (Succ b) -> EqNat a b
succ-inj-eq (EqSucc eq) = eq

decideEqNat : (a b : Nat) -> Decide (EqNat a b)
decideEqNat Zero Zero = Inl EqZero
decideEqNat Zero (Succ b) = Inr (λ ())
decideEqNat (Succ a) Zero = Inr (λ ())
decideEqNat (Succ a) (Succ b) with decideEqNat a b
... | Inl eq = Inl (EqSucc eq)
... | Inr absurd = Inr \eq' -> absurd (succ-inj-eq eq')

eqNat⇒== : {a b : Nat} -> EqNat a b -> a == b
eqNat⇒== EqZero = Refl
eqNat⇒== (EqSucc eq) with eqNat⇒== eq
... | Refl = Refl

succ-inj : {a b : Nat} -> Succ a == Succ b -> a == b
succ-inj {a} {b} Refl = Refl

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

-- [_] : ∀ {a} -> a -> List a
-- [ x ] = Cons x Nil

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

-- Constant function for Set
K : {a : Set} -> Set -> (a -> Set)
K b = \_ -> b

_⊆_ : {a : Set} -> (p q : a -> Set) -> Set
_⊆_ {a} p q = (x : a) -> p x -> q x

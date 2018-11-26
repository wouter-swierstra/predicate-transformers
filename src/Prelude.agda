
open import Level

postulate
  undefined : ∀ {a : Set} -> a

const : {l : Level} {a b : Set l} -> a -> b -> a
const x _ = x

id : {l : Level} {a : Set l} -> a -> a
id x = x

flip : ∀ {l : Level} {a : Set l} {b : Set l} {c : Set l}
  -> (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

_·_ : ∀ {l l' l''} {a : Set l} {b : Set l'} {c : Set l''} ->
      (b -> c) -> (a -> b) -> a -> c
f · g = λ x → f (g x)
_∘_ = _·_

open import Relation.Binary.PropositionalEquality public
infix 1 _==_
_==_ = _≡_

cong2 : {a b c : Set} {x y : a} {z w : b} (f : a -> b -> c) -> x == y -> z == w -> f x z == f y w
cong2 f refl refl = refl

liftPath : {a : Set} {b : a -> Set} {x x' : a} ->
  x == x' -> b x == b x'
liftPath refl = refl

coerce : {l : Level} {a b : Set l} -> a == b -> a -> b
coerce refl x = x

infixr 2 _⟨_⟩_
_⟨_⟩_ : {a : Set} -> (x : a) -> { y z : a} -> x == y -> y == z -> x == z
_⟨_⟩_ x = trans

_■ : forall {a : Set} (x : a) -> x == x
_■ x = refl

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

_||_ : Bool -> Bool -> Bool
True || _ = True
_ || True = True
False || False = False

record Pair {l l'} (a : Set l) (b : Set l') : Set (l ⊔ l') where
  constructor _,_
  field
    fst : a
    snd : b

¹_ : {a b : Set} -> Pair a b -> a
¹ (a , _) = a
²_ : {a b : Set} -> Pair a b -> b
² (_ , b) = b

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

intoSo : So True
intoSo = tt

¬ : ∀ {l} -> Set l -> Set l
¬ {l} a = a -> ⊥

Decide : ∀ {l} (a : Set l) -> Set l
Decide a = Either a (¬ a)

decideFrom : (b : Bool) -> Decide (So b)
decideFrom True = Inl tt
decideFrom False = Inr λ z → z

open import Data.Nat public
  using
    (
    )
  renaming
    ( ℕ to Nat
    ; zero to Zero
    ; suc to Succ
    )

module NaturalLemmas where
  open Data.Nat
  zero-cancellative : (n : Nat) -> (n * Zero) == Zero
  zero-cancellative Zero = refl
  zero-cancellative (Succ n) = zero-cancellative n

  plus-zero : (n : Nat) -> n == (n + Zero)
  plus-zero Zero = refl
  plus-zero (Succ n) = cong Succ (plus-zero n)

  plus-succ : (x y : Nat) -> Succ (x + y) == (x + Succ y)
  plus-succ Zero y = refl
  plus-succ (Succ x) y = cong Succ (plus-succ x y)

  plus-assoc : (x y z : Nat) → (x + y) + z == x + (y + z)
  plus-assoc Zero y z = refl
  plus-assoc (Succ x) y z = cong Succ (plus-assoc x y z)

open NaturalLemmas

open import Data.Integer public
  using
    (
    )
  renaming
    ( ℤ to Int
    )

data List {l : Level} (a : Set l) : Set l where
  Nil : List a
  Cons : a -> List a -> List a

-- [_] : ∀ {a} -> a -> List a
-- [ x ] = Cons x Nil

foldr : {a b : Set} -> (a -> b -> b) -> b -> List a -> b
foldr f e Nil = e
foldr f e (Cons x xs) = f x (foldr f e xs)

_++_ : {l : Level} {a : Set l} -> List a -> List a -> List a
Nil ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

++-nil : {l : Level} {a : Set l} (xs : List a) → xs == xs ++ Nil
++-nil Nil = refl
++-nil (Cons x xs) = cong (Cons x) (++-nil xs)

++-assoc : {l : Level} {a : Set l} (xs ys zs : List a) →
  (xs ++ (ys ++ zs)) == ((xs ++ ys) ++ zs)
++-assoc Nil ys zs = refl
++-assoc (Cons x xs) ys zs = cong (Cons x) (++-assoc xs ys zs)

map : {a b : Set} -> (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

filter : {a : Set} -> (a -> Bool) -> List a -> List a
filter p Nil = Nil
filter p (Cons x xs) =
  if p x then Cons x (filter p xs) else (filter p xs)

length : {a : Set} -> List a -> Nat
length Nil = Zero
length (Cons _ xs) = Succ (length xs)

<=-dec : Nat -> Nat -> Bool
<=-dec Zero m = True
<=-dec (Succ n) Zero = False
<=-dec (Succ n) (Succ m) = <=-dec n m

>-dec : Nat -> Nat -> Bool
>-dec n m = not (<=-dec n m)

all : {a : Set} -> (P : a -> Bool) -> List a -> Set
all P Nil = ⊤
all P (Cons x xs) = Pair (So (P x)) (all P xs) 

data _∈_ {a : Set} : a -> List a -> Set where
  ∈Head : ∀ {x xs} -> x ∈ Cons x xs
  ∈Tail : ∀ {x x' xs} -> x ∈ xs -> x ∈ Cons x' xs

delete : {a : Set} {x : a} (xs : List a) -> x ∈ xs -> List a
delete (Cons x ys) ∈Head = ys
delete (Cons y ys) (∈Tail i) = Cons y (delete ys i)

deleteHead : {a : Set} {x : a} {xs : List a} -> delete (Cons x xs) ∈Head == xs
deleteHead = refl

delete-length : {a : Set} {x : a} {xs : List a} (i : x ∈ xs) ->
  Succ (length (delete xs i)) == length xs
delete-length ∈Head = refl
delete-length (∈Tail i) = cong Succ (delete-length i)

data Inspect {a} {A : Set a} (x : A) : Set a where
    _with-≡_ : (y : A) (eq : x == y) → Inspect x

record Sigma {l l'} (a : Set l) (b : a -> Set l') : Set (l ⊔ l') where
  constructor _,_
  field
    fst : a
    snd : b fst

uncurryΣ : {a : Set} {b : a → Set} {c : (x : a) → b x → Set} → (f : (x : a) → (y : b x) → c x y) → (s : Sigma a b) → c (Sigma.fst s) (Sigma.snd s)
uncurryΣ f (fst , snd) = f fst snd

-- Constant function for Set
K : {a : Set} -> Set -> (a -> Set)
K b = \_ -> b

_⊆_ : {a : Set} -> (p q : a -> Set) -> Set
_⊆_ {a} p q = (x : a) -> p x -> q x


record _⇔_ {l l' : Level} (P : Set l) (Q : Set l') : Set (l ⊔ l') where
  constructor iff
  field
    if : Q -> P
    onlyIf : P -> Q

⇔-refl : {P : Set} → P ⇔ P
⇔-refl = iff id id
⇔-trans : {P Q R : Set} → P ⇔ Q → Q ⇔ R → P ⇔ R
⇔-trans (iff qp pq) (iff rq qr) = iff (qp ∘ rq) (qr ∘ pq)

⇔-pair : {P P' Q Q' : Set} → P ⇔ P' → Q ⇔ Q' → Pair P Q ⇔ Pair P' Q'
⇔-pair (iff p'p pp') (iff q'q qq') = iff (λ z → p'p (Pair.fst z) , q'q (Pair.snd z)) (λ z → pp' (Pair.fst z) , qq' (Pair.snd z))

independent : {a : Set} ->
  (P : (x : a) -> Set) ->
  Set
independent {a} P = (x : a) -> (x' : a) -> P x -> P x'

rebase : {a : Set} ->
  (P : a -> Set) -> independent P ->
  Sigma a P -> (x : a) -> P x
rebase P iP (fst , snd) x = iP fst x snd

all' : {l : Level} {a : Set l} → (a → Set) → List a → Set
all' P Nil = ⊤
all' P (Cons x xs) = Pair (P x) (all' P xs)

⇔-= : {l : Level} {P : Set l} {Q : P → Set} → {p p' : P} → p == p' → Q p ⇔ Q p'
⇔-= refl = ⇔-refl

⇔-pair-⊤ : {P Q : Set} → P ⇔ Q → (Pair ⊤ P) ⇔ Q
⇔-pair-⊤ (iff if onlyIf) = iff (λ z → tt , if z) (λ z → onlyIf (Pair.snd z))

⇔-pair-assoc : {P Q R : Set} → Pair (Pair P Q) R ⇔ Pair P (Pair Q R)
⇔-pair-assoc = iff (λ z → (Pair.fst z , Pair.fst (Pair.snd z)) , Pair.snd (Pair.snd z)) (λ z → Pair.fst (Pair.fst z) , (Pair.snd (Pair.fst z) , Pair.snd z))

all'-pair : {l : Level} {a : Set l} (P : a → Set) → (xs ys : List a) → Pair (all' P xs) (all' P ys) ⇔ all' P (xs ++ ys)
all'-pair P Nil ys = iff (_,_ tt) Pair.snd
all'-pair P (Cons x xs) ys = ⇔-trans ⇔-pair-assoc (⇔-pair ⇔-refl (all'-pair P xs ys))

record IsMonad (m : Set -> Set) : Set₁ where
  constructor isMonad
  field
    bind : {a b : Set} -> m a -> (a -> m b) -> m b
    pure : {a : Set} -> a -> m a
open IsMonad {{...}} public

infixr 20 _>>_ _>>=_
_>>=_ = bind
_>>_ : {m : Set → Set} {{M : IsMonad m}} {a b : Set} → m a → m b → m b
mx >> my = bind mx (const my)

data Id (a : Set) : Set where
  In : a -> Id a
out : {a : Set} -> Id a -> a
out (In x) = x

mmap : {m : Set -> Set} -> IsMonad m -> {a b : Set} -> (a -> b) -> m a -> m b
mmap (isMonad bind pure) f mx = bind mx (\x -> pure (f x))

instance
  IsMonad-Id : IsMonad Id
  IsMonad.bind IsMonad-Id (In x) f = f x
  IsMonad.pure IsMonad-Id x = In x

  IsMonad-List : IsMonad List
  IsMonad.bind IsMonad-List Nil f = Nil
  IsMonad.bind IsMonad-List (Cons x xs) f = f x ++ IsMonad.bind IsMonad-List xs f
  IsMonad.pure IsMonad-List x = Cons x Nil


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

infixr 90 _∘_
_∘_ : ∀ {l l' l''} {a : Set l} {b : Set l'} {c : Set l''} ->
      (b -> c) -> (a -> b) -> a -> c
f ∘ g = λ x → f (g x)

open import Relation.Binary.PropositionalEquality public
  hiding (preorder)
infix 1 _==_
_==_ = _≡_

postulate
  extensionality : {a : Set} {b : a → Set} {f g : (x : a) → b x} →
    ((x : a) → f x == g x) → f == g

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

open import Data.Empty public

magic : ∀ {l} {a : Set l} -> ⊥ -> a
magic ()

So : Bool -> Set
So True = ⊤
So False = ⊥

intoSo : So True
intoSo = tt

open import Relation.Nullary public using
    ( ¬_
    ; Dec
    ; yes
    ; no
    )

if'_then_else : ∀ {l k} {P : Set l} {a : Set k} → Dec P → (P → a) → (¬ P → a) → a
if' yes x then t else f = t x
if' no x then t else f = f x

decideFrom : (b : Bool) -> Dec (So b)
decideFrom True = yes tt
decideFrom False = no λ z → z

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
  succ-inj : (i j : Nat) → Succ i == Succ j → i == j
  succ-inj i .i refl = refl

  eq-Nat : (i j : Nat) → Dec (i == j)
  eq-Nat zero zero = yes refl
  eq-Nat zero (suc j) = no (λ ())
  eq-Nat (suc i) zero = no (λ ())
  eq-Nat (suc i) (suc j) with eq-Nat i j
  eq-Nat (suc i) (suc j) | yes x = yes (cong Succ x)
  eq-Nat (suc i) (suc j) | no x = no (λ z → x (succ-inj i j z))

  zero-cancellative : (n : Nat) -> (n * Zero) == Zero
  zero-cancellative Zero = refl
  zero-cancellative (Succ n) = zero-cancellative n

  plus-zero : (n : Nat) -> n == (n + Zero)
  plus-zero Zero = refl
  plus-zero (Succ n) = cong Succ (plus-zero n)

  plus-succ : (x y : Nat) -> Succ (x + y) == (x + Succ y)
  plus-succ Zero y = refl
  plus-succ (Succ x) y = cong Succ (plus-succ x y)

  +-assoc : ∀ a b c → a + (b + c) == (a + b) + c
  +-assoc zero b c = refl
  +-assoc (suc a) b c = cong Succ (+-assoc a b c)

  ≤-refl : ∀ {x} → x ≤ x
  ≤-refl {zero} = z≤n
  ≤-refl {suc x} = s≤s ≤-refl
  ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans z≤n x₂ = z≤n
  ≤-trans (s≤s x₁) (s≤s x₂) = s≤s (≤-trans x₁ x₂)

  ≤-succ : ∀ {i j} → i ≤ j → i ≤ Succ j
  ≤-succ z≤n = z≤n
  ≤-succ (s≤s x) = s≤s (≤-succ x)

  ≤-+ : ∀ {a b} c → a ≤ b → a + c ≤ b + c
  ≤-+ {zero} {zero} c x = ≤-refl
  ≤-+ {zero} {suc b} c x = ≤-succ (≤-+ {Zero} {b} c z≤n)
  ≤-+ {suc a} {zero} c ()
  ≤-+ {suc a} {suc b} c (s≤s x) = s≤s (≤-+ c x)

  _lt_ : (i j : Nat) → Dec (i < j)
  _ lt Zero = no (λ ())
  Zero lt Succ j = yes (s≤s z≤n)
  Succ i lt Succ j with i lt j
  suc i lt suc j | yes x = yes (s≤s x)
  suc i lt suc j | no x = no (λ z → x (≤-pred z))

  antisymm : ∀ x y → x < y → y < x → ⊥
  antisymm zero y x₁ ()
  antisymm (suc x) zero () x₂
  antisymm (suc x) (suc y) (s≤s x₁) (s≤s x₂) = antisymm x y x₁ x₂

  +-succ : ∀ a b → a + Succ b == Succ (a + b)
  +-succ zero b = refl
  +-succ (suc a) b = cong Succ (+-succ a b)

  =-≤-= : ∀ {i j k l} → i == j → j ≤ k → k == l → i ≤ l
  =-≤-= refl x refl = x

  +-inj-left : ∀ a b c → a + c == b + c → a == b
  +-inj-left a b Zero pf = trans (plus-zero a) (trans pf (sym (plus-zero b)))
  +-inj-left a b (Succ c) pf = succ-inj a b (+-inj-left (Succ a) (Succ b) c (trans (sym (+-succ a c)) (trans pf (+-succ b c))))
  +-inj-right : ∀ a b c → a + b == a + c → b == c
  +-inj-right Zero b c refl = refl
  +-inj-right (Succ a) b c pf = +-inj-right a b c (succ-inj (a + b) (a + c) pf)


module NumberTheory where
  even : Nat → Bool
  even 0 = True
  even 1 = False
  even (Succ (Succ n)) = even n

  half : Nat → Nat
  half 0 = 0
  half 1 = 1
  half (Succ (Succ n)) = Succ (half n)

  double : Nat → Nat
  double 0 = 0
  double (Succ n) = Succ (Succ (double n))

  open import Data.Nat.Divisibility

  _eq_ : Nat → Nat → Bool
  Zero eq Zero = True
  Zero eq Succ b = False
  Succ a eq Zero = False
  Succ a eq Succ b = a eq b


open import Data.Integer public
  using
    (
    )
  renaming
    ( ℤ to Int
    )

infixr 5 _::_
infixr 6 _++_
data List {l : Level} (a : Set l) : Set l where
  Nil : List a
  _::_ : a -> List a -> List a
Cons : {l : Level} {a : Set l} → a → List a → List a
Cons = _::_

-- [_] : ∀ {a} -> a -> List a
-- [ x ] = Cons x Nil


foldr : {a b : Set} -> (a -> b -> b) -> b -> List a -> b
foldr f e Nil = e
foldr f e (x :: xs) = f x (foldr f e xs)

_++_ : {l : Level} {a : Set l} -> List a -> List a -> List a
Nil ++ ys = ys
(x :: xs) ++ ys = Cons x (xs ++ ys)

++-nil : {l : Level} {a : Set l} (xs : List a) → xs == xs ++ Nil
++-nil Nil = refl
++-nil (x :: xs) = cong (Cons x) (++-nil xs)

when-++-is-nil : ∀ {l} {a : Set l} (ys zs : List a) → Nil == ys ++ zs → Pair (ys == Nil) (zs == Nil)
when-++-is-nil Nil Nil x = refl , refl
when-++-is-nil Nil (z :: zs) ()
when-++-is-nil (y :: ys) zs ()

++-assoc : {l : Level} {a : Set l} (xs ys zs : List a) →
  (xs ++ (ys ++ zs)) == ((xs ++ ys) ++ zs)
++-assoc Nil ys zs = refl
++-assoc (x :: xs) ys zs = cong (Cons x) (++-assoc xs ys zs)

map : {a b : Set} -> (a -> b) -> List a -> List b
map f Nil = Nil
map f (x :: xs) = Cons (f x) (map f xs)

filter : {a : Set} -> (a -> Bool) -> List a -> List a
filter p Nil = Nil
filter p (x :: xs) =
  if p x then Cons x (filter p xs) else (filter p xs)

length : {a : Set} -> List a -> Nat
length Nil = Zero
length (_ :: xs) = Succ (length xs)

<=-dec : Nat -> Nat -> Bool
<=-dec Zero m = True
<=-dec (Succ n) Zero = False
<=-dec (Succ n) (Succ m) = <=-dec n m

>-dec : Nat -> Nat -> Bool
>-dec n m = not (<=-dec n m)

all : {a : Set} -> (P : a -> Bool) -> List a -> Set
all P Nil = ⊤
all P (x :: xs) = Pair (So (P x)) (all P xs)

data _∈_ {a : Set} : a -> List a -> Set where
  ∈Head : ∀ {x xs} -> x ∈ Cons x xs
  ∈Tail : ∀ {x x' xs} -> x ∈ xs -> x ∈ Cons x' xs

delete : {a : Set} {x : a} (xs : List a) -> x ∈ xs -> List a
delete (x :: ys) ∈Head = ys
delete (y :: ys) (∈Tail i) = Cons y (delete ys i)

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

filter' : ∀ {l} {a : Set l} {P : a → Set} → ((x : a) → Dec (P x)) → List a → List (Sigma a P)
filter' p Nil = Nil
filter' p (x :: xs) with p x
filter' p (x :: xs) | yes px = (x , px) :: filter' p xs
filter' p (x :: xs) | no np = filter' p xs

filter-shortens : ∀ {a} {P : a → Set} (p : (x : a) → Dec (P x)) (xs : List a) → length xs Data.Nat.≥ length (filter' p xs)
filter-shortens p Nil = Data.Nat.z≤n
filter-shortens p (x :: xs) with p x
filter-shortens p (x :: xs) | yes x₁ = Data.Nat.s≤s (filter-shortens p xs)
filter-shortens p (x :: xs) | no x₁ = NaturalLemmas.≤-succ (filter-shortens p xs)

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
all' P (x :: xs) = Pair (P x) (all' P xs)

⇔-= : {l : Level} {P : Set l} {Q : P → Set} → {p p' : P} → p == p' → Q p ⇔ Q p'
⇔-= refl = ⇔-refl

⇔-pair-⊤ : {P Q : Set} → P ⇔ Q → (Pair ⊤ P) ⇔ Q
⇔-pair-⊤ (iff if onlyIf) = iff (λ z → tt , if z) (λ z → onlyIf (Pair.snd z))

⇔-pair-assoc : {P Q R : Set} → Pair (Pair P Q) R ⇔ Pair P (Pair Q R)
⇔-pair-assoc = iff (λ z → (Pair.fst z , Pair.fst (Pair.snd z)) , Pair.snd (Pair.snd z)) (λ z → Pair.fst (Pair.fst z) , (Pair.snd (Pair.fst z) , Pair.snd z))

all'-pair : {l : Level} {a : Set l} (P : a → Set) → (xs ys : List a) → Pair (all' P xs) (all' P ys) ⇔ all' P (xs ++ ys)
all'-pair P Nil ys = iff (_,_ tt) Pair.snd
all'-pair P (x :: xs) ys = ⇔-trans ⇔-pair-assoc (⇔-pair ⇔-refl (all'-pair P xs ys))

record IsMonad (m : Set -> Set) : Set₁ where
  constructor isMonad
  field
    bind : {a b : Set} -> m a -> (a -> m b) -> m b
    pure : {a : Set} -> a -> m a
    left-identity : ∀ {a b} {x : a} {f : a → m b} → bind (pure x) f == f x
    right-identity : ∀ {a} {mx : m a} → bind mx pure == mx
open IsMonad {{...}} public

infixr 20 _>>_ _>>=_
_>>=_ = bind
_>>_ : {m : Set → Set} {{M : IsMonad m}} {a b : Set} → m a → m b → m b
mx >> my = bind mx (const my)

data Id (a : Set) : Set where
  In : a -> Id a
out : {a : Set} -> Id a -> a
out (In x) = x

fmap : {m : Set -> Set} → {{M : IsMonad m}} -> {a b : Set} -> (a -> b) -> m a -> m b
fmap {{isMonad bind pure _ _}} f mx = bind mx (\x -> pure (f x))

instance
  IsMonad-Id : IsMonad Id
  IsMonad.bind IsMonad-Id (In x) f = f x
  IsMonad.pure IsMonad-Id x = In x
  IsMonad.left-identity IsMonad-Id = refl
  IsMonad.right-identity IsMonad-Id {mx = In x} = refl

  IsMonad-List : IsMonad List
  IsMonad-List = isMonad bind' (λ x → Cons x Nil) (sym (++-nil _)) r-id
    where
    bind' : {a b : Set} → List a → (a → List b) → List b
    bind' Nil f = Nil
    bind' (x :: xs) f = f x ++ bind' xs f
    r-id : ∀ {a} {mx : List a} → bind' mx (λ x → x :: Nil) ≡ mx
    r-id {mx = Nil} = refl
    r-id {mx = x :: mx} = cong (x ::_) r-id

fmap-preserves-length : ∀ {a b} (f : a → b) (xs : List a) → length xs == length (fmap f xs)
fmap-preserves-length f Nil = refl
fmap-preserves-length f (x :: xs) = cong Succ (fmap-preserves-length f xs)

sum : ∀ {l} {a : Set l} (f : a → Nat) (xs : List a) → Nat
sum f Nil = 0
sum f (x :: xs) = f x Data.Nat.+ sum f xs

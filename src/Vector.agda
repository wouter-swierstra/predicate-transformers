module Vector where

open import Prelude

infixr 5 _::_
data Vec : Nat -> Set -> Set where
  vNil : {a : Set} -> Vec 0 a
  _::_ : {n : Nat} {a : Set} -> a -> Vec n a -> Vec (Succ n) a

vCons : {n : Nat} {a : Set} -> a -> Vec n a -> Vec (Succ n) a
vCons = _::_

data Fin : Nat -> Set where
  F0 : {n : Nat} -> Fin (Succ n)
  FS : {n : Nat} -> Fin n -> Fin (Succ n)

deeper : {n : Nat} -> Fin n -> Fin (Succ n)
deeper F0 = F0
deeper (FS i) = FS (deeper i)

index : {n : Nat} {a : Set} -> Vec n a -> Fin n -> a
index (x :: v) F0 = x
index (x :: v) (FS i) = index v i

infix 30 _!!_
_!!_ = index

Vec->List : {n : Nat} {a : Set} -> Vec n a -> List a
Vec->List vNil = Nil
Vec->List (x :: v) = Cons x (Vec->List v)
List->Vec : {a : Set} -> (xs : List a) -> Vec (length xs) a
List->Vec Nil = vNil
List->Vec (x :: xs) = vCons x (List->Vec xs)

Vec->List-length : {n : Nat} {a : Set} -> (xs : Vec n a) ->
  length (Vec->List xs) == n -- xs == coerce (cong (\n -> Vec n a) p) (Sigma.snd (List->Vec (Vec->List xs)))
Vec->List-length vNil = refl
Vec->List-length (x :: xs) = cong Succ (Vec->List-length xs)

resize : {n n' : Nat} {a : Set} -> n == n' -> Vec n a -> Vec n' a
resize refl xs = xs
resize-Cons : {n n' : Nat} {a : Set} -> (p : n == n') -> (x : a) ->
  (xs : Vec n a) (xs' : Vec n' a) -> xs' == resize p xs ->
  vCons x xs' == resize (cong Succ p) (vCons x xs)
resize-Cons refl x xs .xs refl = refl

Vec->List->Vec-eq : {n : Nat} {a : Set} -> (xs : Vec n a) ->
  xs == resize (Vec->List-length xs) (List->Vec (Vec->List xs))
Vec->List->Vec-eq {.0} {a} vNil = refl
Vec->List->Vec-eq {.(Succ _)} {a} (x :: xs) =
  trans (cong (vCons x) (Vec->List->Vec-eq xs)) (resize-Cons (Vec->List-length xs) x (List->Vec (Vec->List xs)) (resize (Vec->List-length xs) (List->Vec (Vec->List xs))) refl)

resize-List->Vec : {n : Nat} {a : Set} -> {xs xs' : List a} ->
  (p : length xs == n) (q : length xs' == n) ->
  xs == xs' -> resize p (List->Vec xs) == resize q (List->Vec xs')
resize-List->Vec refl refl refl = refl

data _∈v_ {a : Set} : {n : Nat} -> a -> Vec n a -> Set where
  inHead : {n : Nat} {x : a} {v : Vec n a} -> x ∈v vCons x v
  inTail : {n : Nat} {x x' : a} {v : Vec n a} -> x ∈v v -> x ∈v vCons x' v

∈List->∈Vec : {a : Set} {n : Nat} -> {x : a} {xs : Vec n a} -> x ∈ Vec->List xs -> x ∈v xs
∈List->∈Vec {xs = vNil} ()
∈List->∈Vec {xs = x₁ :: xs} ∈Head = inHead
∈List->∈Vec {xs = x₁ :: xs} (∈Tail i) = inTail (∈List->∈Vec i)
∈Vec->∈List : {a : Set} {n : Nat} -> {x : a} {xs : Vec n a} -> x ∈v xs -> x ∈ Vec->List xs
∈Vec->∈List {xs = .(vCons _ _)} inHead = ∈Head
∈Vec->∈List {xs = .(vCons _ _)} (inTail i) = ∈Tail (∈Vec->∈List i)

data OneOf {a : Set} (P : a -> Set) : {n : Nat} -> Vec n a -> Set where
  HoldsHead : {n : Nat} {x : a} {v : Vec n a} -> P x -> OneOf P (vCons x v)
  HoldsTail : {n : Nat} {x : a} {v : Vec n a} -> OneOf P v -> OneOf P (vCons x v)

deleteV : {a : Set} {n : Nat} {x : a} ->
  (xs : Vec (Succ n) a) -> (x ∈v xs) -> Vec n a
deleteV {x = x} (.x :: xs) inHead = xs
deleteV {n = Zero} {x} (x' :: xs) (inTail ())
deleteV {n = Succ n} {x} (x' :: xs) (inTail i) = vCons x' (deleteV xs i)

deleteList==deleteVec : {a : Set} {n : Nat} {x : a} ->
  (xs : Vec (Succ n) a) -> (i : x ∈v xs) ->
  Vec->List (deleteV xs i) == delete (Vec->List xs) (∈Vec->∈List i)
deleteList==deleteVec {x = x} (_ :: _) inHead = refl
deleteList==deleteVec {n = Zero} {x} (x' :: xs) (inTail ())
deleteList==deleteVec {n = Succ n} {x} (x' :: xs) (inTail i) = cong (Cons x') (deleteList==deleteVec xs i)

deleteList==deleteVec' : {a : Set} {n : Nat} {x : a} ->
  (xs : Vec (Succ n) a) -> (i : x ∈ Vec->List (xs)) ->
  Vec->List (deleteV xs (∈List->∈Vec i)) == delete (Vec->List xs) i
deleteList==deleteVec' {a} (x₁ :: xs) ∈Head = refl
deleteList==deleteVec' {a} {Zero} (x :: vNil) (∈Tail ())
deleteList==deleteVec' {a} {Succ n} (x :: xs) (∈Tail i) = cong (Cons x) (deleteList==deleteVec' xs i)

split-==-Cons : {a : Set} {n : Nat} {x x' : a} {xs xs' : Vec n a} ->
  vCons x xs == vCons x' xs' -> Pair (x == x') (xs == xs')
split-==-Cons refl = refl , refl

toIndex : {a : Set} {n : Nat} {x : a} {xs : Vec n a} ->
  x ∈v xs -> Fin n
toIndex inHead = F0
toIndex (inTail x₁) = FS (toIndex x₁)

fin-= : {n : Nat} -> Fin n -> Fin n -> Bool
fin-= F0 F0 = True
fin-= F0 (FS _) = False
fin-= (FS _) F0 = False
fin-= (FS i) (FS j) = fin-= i j

fin-≤ : {n : Nat} -> Fin n -> Fin n -> Bool
fin-≤ F0 _ = True
fin-≤ (FS i) F0 = False
fin-≤ (FS i) (FS j) = fin-≤ i j

vmap : {a b : Set} {n : Nat} → (a → b) → Vec n a → Vec n b
vmap f vNil = vNil
vmap f (x :: xs) = vCons (f x) (vmap f xs)

index-map : {a b : Set} {n : Nat} (i : Fin n) (f : a → b) (xs : Vec n a) →
  vmap f xs !! i == f (xs !! i)
index-map F0 f (x :: xs) = refl
index-map (FS i) f (x :: xs) = index-map i f xs

uncons : ∀ {a n} → Vec (Succ n) a → Pair a (Vec n a)
uncons (x :: xs) = x , xs

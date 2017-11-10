module Logic where

open import Prelude
open import Level

module Relations where

  _⊆_ : {l : Level} {a b : Set l} ->
    (R1 R2 : a -> b -> Set l) -> Set l
  _⊆_ {a = a} {b = b} R1 R2 =
    (x : a) -> (y : b) -> R1 x y -> R2 x y 

  wp : {l : Level} {a b : Set l} -> (R : a -> b -> Set l) -> (b -> Set l) -> (a -> Set l)
  wp {b = b} R Q = λ x → Sigma b (\y -> R x y)

  isExec : {l : Level} {a b : Set l} -> (R : a -> b -> Set l) -> Set l
  isExec {a = a} {b = b} R = (x : a) -> Sigma b (\y -> R x y)

  extract : {l : Level} {a b : Set l} -> (R : a -> b -> Set l) -> isExec R -> a -> b
  extract R p x = Sigma.fst (p x)

  _⊑_ : {l : Level} -> {a b : Set l} -> (R R' : a -> b -> Set l) -> Set (suc l)
  _⊑_ {l} {a = a} {b = b} R R' = (P : b -> Set l) -> (x : a) -> wp R P x -> wp R' P x
  
module Free where

  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a

  return : {C : Set} {R : C -> Set} {a : Set} -> a -> Free C R a
  return = Pure

  _>>=_ : ∀ {C R a b} -> Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x >>= f = f x
  Step c x >>= f = Step c (\r -> x r >>= f)

  _>>_ : ∀ {C R a b} -> Free C R a -> Free C R b -> Free C R b
  c1 >> c2 = c1 >>= (\_ -> c2)

  fmap : ∀ {C R a b} -> (a -> b) -> Free C R a -> Free C R b
  fmap f (Pure x) = Pure (f x)
  fmap f (Step c k) = Step c (\r -> fmap f (k r)) 

  fold : ∀ {C R a l} {b : Set l} -> ((c : C) -> (R c -> b) -> b) -> (a -> b) -> Free C R a -> b
  fold alg pure (Pure x) = pure x
  fold alg pure (Step c k) = alg c (\r -> fold alg pure (k r))

--  wp : ∀ {a : Set} {b C R} -> (((c : C) -> (R c -> Set) -> Set)) -> (a -> Free C R b) -> (a -> b -> Set) -> (a -> Set)
--  wp alg f pre x = fold alg (pre x) (f x)


module Maybe where

  -- Define our free monad
  open Free

  data C : Set where
    Nothing : C

  R : C -> Set
  R Nothing = ⊥

  Maybe : Set -> Set
  Maybe = Free C R

  -- Define smart constructors
  just : ∀ {a : Set} -> a -> Maybe a
  just = Pure

  nothing : ∀ {a : Set} -> Maybe a
  nothing = Step Nothing λ()

  -- Define a propositional handler 
  handle : ∀ {a} -> (P : a -> Set) -> Maybe a -> Set
  handle P (Pure x) = P x
  handle P (Step Nothing x) = ⊥

  handle' : ∀ {a} -> (P : a -> Set) -> Maybe a -> Set
  handle' P = fold (λ { Nothing x → ⊥ }) P

  -- Compute wp for kleisli arrows
  wpMaybe : ∀ {a b : Set} -> (a -> Maybe b) -> (a -> b -> Set) -> (a -> Set)
  wpMaybe f pre x = handle (pre x) (f x)

--  wpMaybe' : ∀ {a b : Set} -> (a -> Maybe b) -> (a -> b -> Set) -> (a -> Set)
--  wpMaybe' = wp ((λ { Nothing x → ⊥ }))

  -- Example
  divExample : Pair Nat Nat -> Maybe (Pair Nat Nat)
  divExample (Zero , y) = nothing 
  divExample (Succ x , y) = just (y , Succ x) 

  test = wpMaybe divExample (λ { (x , y) (x' , y') → Pair (x == y') (y == x') })
--                (( 0 , 2)) 
                  (1 , 3)
                  
  -- Another handler, paramtrized by the default value d
  default : ∀ {a} -> a -> Maybe a -> a
  default d (Pure x) = x
  default d (Step Nothing x) = d

  -- And its corresponding propositional lifting
  handleDefault : ∀ {a} -> (d : a) -> (P : a -> Set) -> Maybe a -> Set
  handleDefault d P (Pure x) = P x
  handleDefault d P (Step Nothing x) = P d

  soundness : ∀ {a} -> (d : a) (P : a -> Set) (m : Maybe a) ->
    handle P m -> P (default d m)
  soundness d P (Pure x) x₁ = x₁
  soundness d P (Step Nothing x) ()

  completeness : ∀ {a} -> (d : a) (P : a -> Set) (m : Maybe a) ->
    P (default d m) -> handle P m
  completeness d P (Pure x) x₁ = x₁
  completeness d P (Step Nothing x) x₁ = {!!}

  -- Rule of consequence
  >>-property : ∀ {a b} -> (c : Maybe a) -> (f : a -> Maybe b) ->
    (P : a -> Set) -> (Q : b -> Set) ->
      handle P c ->
      ((x : a) -> P x -> handle Q (f x)) ->
      handle Q (c >>= f)
  >>-property (Pure x) f P Q p q = q x p
  >>-property (Step Nothing x) f P Q () q

  >>-property' : ∀ {a b} -> (c : Maybe a) -> (f : a -> Maybe b) ->
    (P : a -> Set) -> (Q : a -> b -> Set) ->
      handle P c ->
      ((x : a) -> P x -> wpMaybe f Q x) ->
      handle {!!} (c >>= f)
  >>-property' c f P Q p q = {!!}

  -- wp(s1;s2,R) = wp(s1,wp(s2,R))
  >>-wp-left :  ∀ {a b} -> (c : Maybe a) -> (f : a -> Maybe b) ->
    (Q : b -> Set) ->
    handle Q (c >>= f) -> handle (\x -> handle Q (f x)) c
  >>-wp-left (Pure x) f Q H = H
  >>-wp-left (Step Nothing x) f Q H = H

  >>-wp-right :  ∀ {a b} -> (c : Maybe a) -> (f : a -> Maybe b) ->
    (Q : b -> Set) ->
    handle (\x -> handle Q (f x)) c -> handle Q (c >>= f)
  >>-wp-right (Pure x) f Q H = H
  >>-wp-right (Step Nothing x) f Q H = H

  -- Another example
  fastProduct : List Nat -> Maybe Nat
  fastProduct Nil = return 1
  fastProduct (Cons Zero xs) = nothing
  fastProduct (Cons (Succ k) xs) = fmap (\n -> Succ k * n) (fastProduct xs)

  listProduct : List Nat -> Nat
  listProduct Nil = 1
  listProduct (Cons x xs) = x * listProduct xs
  
  wpProduct : ∀ {a b : Set} ->
    (d : b) -> (a -> Maybe b) -> (a -> b -> Set) -> (a -> Set)
  wpProduct d c P x = handleDefault d (P x) (c x)

  fastSpec : List Nat -> Nat -> Set
  fastSpec xs n = listProduct xs == n

  correctness : (xs : List Nat) ->
    wpProduct Zero fastProduct fastSpec xs
  correctness Nil = Refl
  correctness (Cons Zero xs) = Refl
  correctness (Cons (Succ k) xs)
    with fastProduct xs | listProduct xs | correctness xs
  correctness (Cons (Succ k) xs) | Pure x | .x | Refl
    = Refl
  correctness (Cons (Succ k) xs) | Step Nothing x | .Zero | Refl
    = zero-cancellative k

  data Expr : Set where
    Val : Nat -> Expr
    Div : Expr -> Expr -> Expr

  div : Nat -> Nat -> Maybe (Nat)
  div n k = {!!}
  
  ⟦_⟧ : Expr -> Maybe Nat
  ⟦ Val x ⟧ = return x
  ⟦ Div e e' ⟧ =  ⟦ e ⟧ >>= \x ->
                 ⟦ e' ⟧ >>= \y ->
                 div x y

  mywp : (Nat -> Set) -> (Expr -> Set)
  mywp P e = handle P ⟦ e ⟧

  atLeast3 : (e : Expr) -> handle (\n -> 1 < n) ⟦ e ⟧
  atLeast3 (Val x) = {!!}
  atLeast3 (Div e e₁) = {!!}


module Nondeterminism where

  -- Define a free monad
  open Free

  data C : Set where
    Fail : C
    Choice : C

  R : C -> Set
  R Fail = ⊥
  R Choice = Bool

  ND : Set -> Set
  ND = Free C R

  -- Define smart constructors
  fail : ∀ {a} -> ND a
  fail = Step Fail λ()

  choice : ∀ {a} -> ND a -> ND a -> ND a
  choice c1 c2 = Step Choice (\b -> if b then c1 else c2)

  -- Define a handler
  handle : ∀ {a} -> ND a -> List a
  handle (Pure x) = [ x ]
  handle (Step Fail x) = Nil
  handle (Step Choice c) = handle (c True) ++ handle (c False) 

  -- Define a propositional handler
  All : ∀ {a} -> (P : a -> Set) -> ND a -> Set
  All P (Pure x) = P x
  All P (Step Fail _) = ⊤
  All P (Step Choice c) = Pair (All P (c True)) (All P (c False)) 

  All' :  ∀ {a} -> (P : a -> Set) -> ND a -> Set
  All' = fold (λ { Fail _ → ⊤ ; Choice k → Pair (k True) (k False) })

  Any : ∀ {a} -> (P : a -> Set) -> ND a -> Set
  Any P (Pure x) = P x
  Any P (Step Fail _) = ⊥
  Any P (Step Choice c) = Either (Any P (c True)) (Any P (c False)) 

  -- And assign wp semantics to kleisi arrows
  wpAll : ∀ {a b : Set} -> (a -> ND b) -> (a -> b -> Set) -> (a -> Set)
  wpAll f pre x = All (pre x) (f x)

  wpAny : ∀ {a b : Set} -> (a -> ND b) -> (a -> b -> Set) -> (a -> Set)
  wpAny f pre x = Any (pre x) (f x)

--  wpAll' :  ∀ {a b : Set} -> (a -> ND b) -> (a -> b -> Set) -> (a -> Set)
--  wpAll' = wp ((λ { Fail _ → ⊤ ; Choice k → Pair (k True) (k False) }))
  
  -- Example

module State (s : Set) where

  -- Define a free monad
  open Free

  data C : Set where
    Get : C
    Put : s -> C

  R : C -> Set
  R Get = s
  R (Put _) = ⊤

  State : Set -> Set
  State = Free C R

  -- Define smart constructors
  get : State s
  get = Step Get return

  put : s -> State ⊤
  put s = Step (Put s) (\_ -> return tt)

  -- Define a handler
  handle : ∀ {a} -> State a -> s -> Pair a s
  handle (Pure x) s = x , s
  handle (Step Get k) s = handle (k s) s
  handle (Step (Put x) k) s = handle (k tt) x 

  -- Folding the definitions together
  wp : {a : Set} -> (P : Pair a s -> Set) -> State a -> (s -> Set)
  wp P (Pure x) s = P (x , s)
  wp P (Step Get k) s = wp P (k s) s
  wp P (Step (Put s') k) s = wp P (k tt) s'

  sound :  {a : Set} -> (P : Pair a s -> Set) -> (c : State a) ->
             (i : s) -> wp P c i ->
             P (handle c i)
  sound P (Pure x) i p = p
  sound P (Step Get x) i wp = sound P (x i) i wp
  sound P (Step (Put x) k) i wp with sound P (k tt)
  ... | ih = ih x wp             

  -- The relational variation
  wpR : {a : Set} -> (P : s -> a -> s -> Set) -> State a -> (s -> Set)
  wpR P c s = wp (uncurry (P s)) c s
  
  soundR :  {a : Set} -> (P : s -> a -> s -> Set) -> (c : State a) ->
             (i : s) -> wpR P c i ->
             uncurry (P i) (handle c i)
  soundR P c i p = sound (uncurry (P i)) c i p

module Trees where

  open Free
  open State(Nat)

  data Tree (a : Set) : Set where
    Leaf : a -> Tree a
    Node : (l : Tree a) -> (r : Tree a) -> Tree a

  size : ∀ {a} -> Tree a -> Nat
  size (Leaf x) = 1
  size (Node l r) = size l + size r

  seq : Nat -> Nat -> List Nat
  seq Zero k = Nil
  seq (Succ n) k = Cons k (seq n (Succ k))

  flatten : ∀ {a} -> Tree a -> List a
  flatten (Leaf x) = [ x ]
  flatten (Node l r) = flatten l ++ flatten r

  relabel : ∀ {a} -> Tree a -> State (Tree Nat)
  relabel (Leaf x) =
    get >>= \s ->
    put (Succ s) >>
    return (Leaf s) 
  relabel (Node l r) =
    relabel l >>= \l' ->
    relabel r >>= \r' ->
    return (Node l' r')

  relabelSpec : Nat -> Tree Nat -> Nat -> Set
  relabelSpec i t f = f == (i + size t)

  correctness : ∀ {a} -> Tree a -> Nat -> Set
  correctness t i = wpR relabelSpec (relabel t) i

  correctnessHolds : ∀ {a} -> (t : Tree a) -> wpR relabelSpec (relabel t) Zero
  correctnessHolds (Leaf x) = Refl
  correctnessHolds (Node l r) with correctnessHolds l | correctnessHolds r
  ... | p | q = {!!}

module Totally (I : Set) (O : Set) where

  open Free

  data C : Set where
    Call : I -> C

  R : C -> Set
  R (Call x) = O -- could be made dependent

  Rec : Set -> Set
  Rec = Free C R

  call : I -> Rec O
  call i = Step (Call i) Pure

  handle : (Inv : I -> O -> Set) (P : O -> Set) -> Rec O -> Set
  handle Inv P (Pure x) = P x
  handle Inv P (Step (Call x) k) =
    (o : O) -> Inv x o -> handle Inv P (k o)

module QS where
  open Free
  open Totally (Pair (Nat -> Bool) (List Nat)) (List Nat)

  myfilter : {a : Set} (p : a -> Bool) (xs : List a) -> Sigma (List a) (all p)
  myfilter p Nil = Nil , tt
  myfilter p (Cons x xs) with inspect (p x) | myfilter p xs
  myfilter p (Cons x xs) | True with-≡ eq | ys , yps =
    Cons x ys , (lemma (p x) eq , yps)
    where
      lemma : (b : Bool) -> b == True -> So b
      lemma True p = tt
      lemma False ()
  myfilter p (Cons x xs) | False with-≡ eq | ys , yps =
    ys , yps

  qs : List Nat -> Rec (List Nat)
  qs Nil = return Nil
  qs (Cons x xs) =
     call (<=-dec x , filter (<=-dec x) xs) >>= \lts ->
     call (>-dec x , filter (>-dec x) xs) >>= \gts ->
     return (lts ++ ([ x ] ++ gts))

  data IsSorted : List Nat -> Set where
    Base : IsSorted Nil
    Single : ∀ {x} -> IsSorted ([ x ])
    Step : ∀ {x y ys} -> So (<=-dec x y) -> IsSorted (Cons y ys) ->
      IsSorted (Cons x (Cons y ys))

  correct : (xs : List Nat) ->
    handle (\ { (p , is) o → Pair (IsSorted o) (all p o) }) IsSorted (qs xs)
  correct Nil = Base
  correct (Cons x xs) sxs (fst , snd) sys (fst₁ , snd₁) = {!!}
{-

* Can we give (propositional) semantics independently of a particular
handler? Eg define semantics of get/put without defining the state
monad or equations between them?

* How can we use this technology to reason about combinations of
  effects? Eg mixing state and exceptions.

* What about other effects? General recursion? Async/await?
  Probablistic computations?  Shift/reset? Yield/fork?
  
* How can we reason about compound computations built with >>= and >>?
  There must be some 'law of consequence' that we can derive for
  specific handlers/effects -- is there a more general form?

* What is a specification of a program with effects? Can we define
  generalized refinement rules?

* What about the equations that we expect our handlers/algebraic
  effects to satisfy?

-}

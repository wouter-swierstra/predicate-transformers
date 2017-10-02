module Logic where

open import Prelude
open import Level

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

  wp : ∀ {a : Set} {b C R} -> (((c : C) -> (R c -> Set) -> Set)) -> (a -> Free C R b) -> (a -> b -> Set) -> (a -> Set)
  wp alg f pre x = fold alg (pre x) (f x)


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

  wpMaybe' : ∀ {a b : Set} -> (a -> Maybe b) -> (a -> b -> Set) -> (a -> Set)
  wpMaybe' = wp ((λ { Nothing x → ⊥ }))

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

  Q = Pair Nat Nat

  toQ : Nat -> Q
  toQ n = (n , 1)

  div : Q -> Q -> Maybe (Q)
  div (fst , snd) (Zero , snd') = nothing
  div (fst , snd) (Succ fst' , snd') =
    return ((fst * snd') , (snd * (Succ fst')))
  
  ⟦_⟧ : Expr -> Maybe Q
  ⟦ Val x ⟧ = return (x , (Succ Zero))
  ⟦ Div e e' ⟧ =  ⟦ e ⟧ >>= \x ->
                 ⟦ e' ⟧ >>= \y ->
                 div x y

  mywp : (Q -> Set) -> (Expr -> Set)
  mywp P e = handle P ⟦ e ⟧

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

  wpAll' :  ∀ {a b : Set} -> (a -> ND b) -> (a -> b -> Set) -> (a -> Set)
  wpAll' = wp ((λ { Fail _ → ⊤ ; Choice k → Pair (k True) (k False) }))
  
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

  handleAlg : ∀ {a} -> (c : C) -> (R c -> s -> Pair a s) -> s -> Pair a s
  handleAlg Get alg = \s -> alg s s
  handleAlg (Put x) alg = \_ -> alg tt x

  -- Define a propositional handler using handle
  wp0 : {a : Set} -> State a -> (s -> a -> s -> Set) -> (s -> Set)
  wp0 c P s = let x , s' = handle c s in P s x s'

  -- Define a propositional handler directly. This is harder to use:
  --  we want a relational spec between result & input-output states.
  wp' : {a : Set} -> (P : a -> Set) -> State a -> (s -> Set)
  wp' P (Pure x) s = P x
  wp' P (Step Get k) s = wp' P (k s) s
  wp' P (Step (Put s') k) s = wp' P (k tt) s'

  -- Folding the definitions together
  wp'' : {a : Set} -> (P : s -> a -> s -> Set) -> State a -> (s -> Set)
  wp'' P (Pure x) s = P s x s
  wp'' P (Step Get k) s = wp'' P (k s) s
  wp'' P (Step (Put s') k) s = wp'' P (k tt) s'

  wpFold : {a : Set} -> (P : s -> a -> s -> Set) -> State a -> (s -> Set)
  wpFold P c s =
    fold (\ { Get r → r s
          ; (Put x) r → r tt })
          (λ x → P s x {!!})
          c

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

-}

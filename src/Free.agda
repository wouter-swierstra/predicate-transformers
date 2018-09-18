module Free where
open import Prelude
open import Level hiding (lift)

data Free (C : Set) (R : C -> Set) (a : Set) : Set where
  Pure : a -> Free C R a
  Step : (c : C) -> (R c -> Free C R a) -> Free C R a

fmap : forall {  C R a b } ->  (a -> b) -> Free C R a -> Free C R b
fmap f (Pure x)    = Pure (f x)
fmap f (Step c k)  = Step c (\ r -> fmap f (k r))

return : forall {  C R a } ->  a -> Free C R a
return = Pure

_>>=_ : forall {  C R a b } ->  Free C R a -> (a -> Free C R b) -> Free C R b
Pure x   >>= f  = f x
Step c x >>= f  = Step c (\ r -> x r >>= f)

_⊆_ : {l : Level} {a : Set l} -> (R1 R2 : a -> Set l) -> Set l
_⊆_ {a = a} R1 R2 = (x : a) -> R1 x -> R2 x 

wp : {a : Set} {b : a -> Set} -> ((x : a) -> b x -> Set) -> ((f : (x : a) -> b x) -> a -> Set)
wp P f = \ a -> P a (f a)

_⊑_ : {a : Set} {b : a -> Set} (f g : (x : a) -> b x) -> Set1
_⊑_ {a} {b} f g = ((P : (x : a) -> b x -> Set) (x : a) -> wp P f x -> wp P f x)

-- The type of handlers for operations in C.
Handler : (C : Set) -> (R : C -> Set) -> Set1
Handler C R = {a : Set} (c : C) -> (R c -> Free C R a) -> Free C R a

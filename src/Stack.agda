open import Prelude
open import Free hiding (_⊑_)
open import MaybeEval
open import Spec

module Stack where
Stack = List

pop : ∀ {a} -> Stack a -> Partial (Pair a (Stack a))
pop Nil = abort
pop (Cons x xs) = return (x , xs)

PopSpec : Stack Nat -> (Pair Nat (Stack Nat)) -> Set
PopSpec xs (y , ys) = xs == Cons y ys

K : {a : Set} -> Set -> (a -> Set)
K A _ = A

popSpec : (xs : Stack Nat) -> M {Stack Nat} (\_ -> Pair Nat (Stack Nat))
popSpec xs = spec (\q -> q == Nil -> ⊥) PopSpec

fromCode : ∀ {a b : Set} -> (Partial a) -> M {b} (\_ -> a)
fromCode (Pure y) = Pure (Done y)
fromCode (Step Abort x) = Step Abort \()

popCorrect : popSpec ⊑ \xs -> fromCode {Pair Nat (Stack Nat)} (pop xs)
popCorrect = refinement λ { P Nil (fst , snd) → magic (fst Refl)
                          ; P (Cons x xs) (fst , snd) → snd _ Refl}

data AddSpec : Stack Nat -> Stack Nat -> Set where
  AddThem : ∀ {x1 x2 : Nat} {xs : Stack Nat} -> AddSpec (Cons x1 (Cons x2 xs)) (Cons (x1 + x2) xs)

null? : Stack Nat -> Set
null? Nil = ⊤
null? _ = ⊥

single? : Stack Nat -> Set
single? Nil = ⊥
single? (Cons x xs) = null? xs

addSpec : Stack Nat -> M {Stack Nat} (\_ -> Stack Nat)
addSpec (xs) = spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) AddSpec

add : Stack Nat -> M {Stack Nat} (\_ -> Stack Nat)
add xs =
  pop xs >>= \{ (x1 , xs) -> 
  pop xs >>= \{ (x2 , xs) ->
  return (Done (Cons (x1 + x2) xs))}}

addCorrect : addSpec ⊑ add
addCorrect = refinement prf
  where
  prf : (P : Stack Nat -> Stack Nat -> Set) -> wpM P addSpec ⊆ wpM P add
  prf P Nil ((fst , _) , _) = fst _
  prf P (Cons x Nil) ((_ , snd) , _) = snd _
  prf P (Cons x (Cons x₁ xs)) H = Pair.snd H _ AddThem

-- Can we do calculation in this style?

explicitDerivation : addSpec ⊑ add
explicitDerivation =
  addSpec
    ⟨ step1 ⟩
  (\xs -> pop xs >>= \ { (x1 , xs) -> spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) (AddSpec)})
    ⟨ step2 ⟩
  (\xs -> pop xs >>= \ { (x1 , xs) ->
          pop xs >>= \ { (x2 , xs) ->
          spec (\xs -> ⊤) (AddSpec)}})
    ⟨ step3 ⟩
  add ■
    where
      step1 : addSpec ⊑ (\xs -> pop xs >>= \ { (x1 , xs) -> spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) ((\as bs -> AddSpec as bs))})
      step1 = refinement λ { P Nil ((fst , _) , snd) → magic (fst _)
                            ; P (Cons x Nil) ((_ , fst) , snd) → magic (fst _)
                            ; P (Cons x (Cons x₁ xs)) (H , snd) → H , snd}
      step2 : (\xs -> pop xs >>= \ { (x1 , xs) -> spec (\xs -> Pair (null? xs -> ⊥) (single? xs -> ⊥)) AddSpec})
              ⊑
              (\xs -> pop xs >>= \ { (x1 , xs) ->
                      pop xs >>= \ { (x2 , xs) ->
                      spec (\xs -> ⊤) AddSpec}})
      step2 = refinement λ { P Nil ()
                            ; P (Cons x Nil) ((_ , fst) , snd) → magic (fst _)
                            ; P (Cons x (Cons x₁ i)) (fst , snd) → tt , snd}
      step3 : (\xs -> pop xs >>= \ { (x1 , xs) ->
                      pop xs >>= \ { (x2 , xs) ->
                      spec (\xs -> ⊤) AddSpec}})
              ⊑ add
      step3 = refinement λ { P Nil ()
                            ; P (Cons x Nil) ()
                            ; P (Cons x1 (Cons x2 xs)) (fst , snd) → snd (Cons (x1 + x2) xs) AddThem}

--  -- Rephrasing things a bit...

--  Σ : (a : Set) -> (b : a -> Set) -> Set
--  Σ = Sigma

--  popM : Stack Nat -> M (Pair Nat (Stack Nat))
--  popM xs = pop xs >>= λ x → Pure (Done x)

--  _>=>_ : ∀ {a b c} -> (I a -> M b) -> (I b -> M c) -> (I a -> M c)
--  _>=>_ c1 c2 = \x ->  c1 x >>= c2

--  popIt : (S : Stack Nat -> Stack Nat -> Set) ->
--          Σ (Pair Nat (Stack Nat) -> M (Stack Nat))
--            (\g -> 
--              (P : Stack Nat -> Stack Nat -> Set) ->
--              wpM (spec · S) P ⊆ wpM (\xs -> pop xs >>= g) P) ->
--          Σ (Stack Nat -> M (Stack Nat)) (\f -> (spec · S) ⊑ f)
--  popIt S (g , H) = (\xs -> pop xs >>= g) , refinement H


--  returnStep : ∀ {P : Stack Nat -> Stack Nat -> Set} ->
--    ((xs : Stack Nat) -> P xs xs) ->
--    Σ (Stack Nat -> M (Stack Nat)) (\f -> (\x -> spec (P x)) ⊑ f)    
--  returnStep H = (\xs -> Pure (Done xs)) , refinement λ { P ys (fst , snd) → snd ys (H ys)}

--  popStep : (S : Stack Nat -> Stack Nat -> Set) ->
--          (S' : Pair Nat (Stack Nat) -> Stack Nat -> Set) ->
--          ((x : Nat) (xs : Stack Nat) -> S (Cons x xs) ⊆ S' (x , xs)) ->
--          ((x : Nat) (xs : Stack Nat) -> S' (x , xs) ⊆ S (Cons x xs)) ->          
--          Σ (Pair Nat (Stack Nat) -> M (Stack Nat))
--            (\g -> (spec · S') ⊑ g) ->
--          Σ (Stack Nat -> M (Stack Nat)) (\f -> (spec · S) ⊑ f)
--  popStep S S' H1 H2 (g , proof) =
--    (\xs -> pop xs >>= g) , {!!}


--  derivation : Σ (Stack Nat -> M (Stack Nat)) (\f -> addSpec ⊑ f)
--  derivation =  {!!}

--  feasible : {a : Set} -> {b : a -> Set} ->
--    (f : (x : a) -> M (b x)) -> Set
--  feasible {a} f = (x : a) -> wp f (\_ _ -> ⊥) x == ⊥

--  infeasible : {a : Set} -> {b : a -> Set} ->
--    (f : (x : a) -> M (b x)) -> Set
--  infeasible f = feasible f -> ⊥

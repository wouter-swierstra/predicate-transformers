\documentclass[sigplan,10pt,acmlarge]{acmart}%

%include polycode.fmt
%include agda.fmt

%include preamble.tex

%if style == poly
%format (Forall (a)) = "\!"
%format (implicit(a)) = "\!"
%format N = "\mathbb{N}"
%format Q = "\mathbb{Q}"
%format e1 = e "_1"
%format e2 = e "_2"
%format v1 = v "_1"
%format v2 = v "_2"
%format top = "\top"
%else
%format (Forall (a)) = "forall { " a " } -> "
%format (implicit(a)) = "{" a "} ->"
%format N = "Nat"
%format Q = "Rat"
%format top = "⊤"
%endif

\begin{document}
\title{Specifications and free monads}

\author{Wouter Swierstra}
\affiliation{
\institution{Utrecht University}
}
\email{w.s.swierstra@@uu.nl}

\begin{abstract}
  This unpublished note explores how to specify the behaviour of
  programs written using effects, described by a free monad. The key
  end insight is the definition of \emph{handlers} that compute
  specifications.
\end{abstract}

\maketitle

\section{Warm-up}
\label{sec:intro}
%if style == newcode
\begin{code}
module Check where

open import Prelude
open import Level

module Free where
\end{code}
%endif

We begin by defining a data type for free monads in Agda in the style
of Hancock and Setzer:

\begin{code}
  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
\end{code}

You may want to think of |C| as being the type of \emph{commands}; for
each |c : C|, there is a set of responses |R c|. It is straightforward
to show that the |Free| data type is indeed a monad:
\begin{code}
  fmap : (Forall (C R a b)) (a -> b) -> Free C R a -> Free C R b
  return : (Forall (C R a)) a -> Free C R a
  _>>=_ : (Forall (C R a b)) Free C R a -> (a -> Free C R b) -> Free C R b
\end{code}
%if style == newcode
\begin{code}
  return = Pure

  Pure x >>= f = f x
  Step c x >>= f = Step c (\r -> x r >>= f)

  fmap f (Pure x) = Pure (f x)
  fmap f (Step c k) = Step c (\r -> fmap f (k r)) 
\end{code}
%endif
Finally, we will sometimes \emph{fold} over elements of |Free C R a|
using the principle:
\begin{code}
  fold : (Forall(C R a l)) (implicit(b : Set l)) ((c : C) -> (R c -> b) -> b) -> (a -> b) -> Free C R a -> b
  fold alg pure (Pure x) = pure x
  fold alg pure (Step c k) = alg c (\ r -> fold alg pure (k r))
\end{code}

\section{Maybe}
\label{sec:maybe}
%if style == newcode
\begin{code}
module Maybe where

  open Free
\end{code}
%endif

We can define the familiar |Maybe| monad by making the following
choice for |C| and |R|:
\begin{code}
  data C : Set where
    Nothing : C

  R : C -> Set
  R Nothing = ⊥

  Maybe : Set -> Set
  Maybe = Free C R
\end{code}
It is sometimes convenient to define the familiar constructors of the
|Maybe| type
\begin{code}
  just     : (Forall(a)) a -> Maybe a
  just     = Pure

  nothing  : (Forall(a)) Maybe a
  nothing  = Step Nothing (\ ())
\end{code}
A computation of type |Maybe a| will either return a value of type |a|
or fail (and return |nothing|).  One way to define a specification for
such computations, is by \emph{lifting} a predicate on |a| over
computations of type |Maybe a|:
\begin{code}
  spec : (Forall(a)) (P : a -> Set) -> Maybe a -> Set
  spec P (Pure x)          = P x
  spec P (Step Nothing _)  = ⊥
\end{code}
Alternatively, we could have defined |spec| using our |fold| function,
mapping |Nothing| to bottom:
\begin{spec}
  spec = fold (\ { Nothing x → ⊥ })
\end{spec}
For any predicate |P : a -> Set|, the statement |spec P| specifies
when a computation of type |Maybe a| will successfully return a value
of type |a| satisfying |P|.

\subsection*{Example: evaluation}
\label{sec:evaluation}

We can define a small expression language consisting of natural
numbers and division:

\begin{code}
  data Expr : Set where
    Val : N -> Expr
    Div : Expr -> Expr -> Expr
\end{code}

When evaluating these expressions, we may encounter division by zero
errors. Our evaluator therefore returns a value of |Maybe Q| (where
|Q| is some suitable representation of rational numbers in Agda):
\begin{code}
  ⟦_⟧ : Expr -> Maybe Q
  ⟦ Val x ⟧      =  return (x , (Succ Zero))
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    div v1 v2
\end{code}

How can we reason about our evaluator? Or specify its intended
behaviour?

\paragraph{Predicate transformers}
To specify a property of values of type |a| amounts to defining a
predicate |a -> Set|. To specify the intended behaviour of our
semantics |⟦_⟧|, we could give a predicate |(Expr -> Maybe Q) ->
Set|. Instead, we'll take a slightly different approach and specify
functions by means of a \emph{predicate transformer}. The
specification of a function of type |a -> b| amounts to a predicate
transformer |(b -> Set) -> (a -> Set)|, computing the weakest
precondition on the input of type |a| necessary to guarantee that the
output of the function satisfies the argument predicate of type |b ->
Set|.
\todo{Remarks about contravariant hom-functors}

Concretely, in our example, we can map the Kleisli arrow |Expr ->
Maybe Q| to a predicate of the form |(Maybe Q -> Set) -> (Expr ->
Set)|. Using the |spec| function, we can lift a predicate on |Q| to a
predicate on |Maybe Q| using our |spec| function. Putting these pieces
together we can define:

\begin{code}
  wp : (Q -> Set) -> (Expr -> Set)
  wp P e = spec P ⟦ e ⟧
\end{code}

For example, we specify the domain of our semantics |⟦_⟧| by
instantiating |P| to be the trivial predicate:

\begin{code}
  dom : Expr -> Set
  dom = wp (\ _ -> top)
\end{code}


\section{Nondeterminism}
\label{sec:non-det}

\begin{code}
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
  fail = Step Fail \()

  choice : ∀ {a} -> ND a -> ND a -> ND a
  choice c1 c2 = Step Choice (\b -> if b then c1 else c2)

  -- Define a propositional handler
  All : ∀ {a} -> (P : a -> Set) -> ND a -> Set
  All P (Pure x) = P x
  All P (Step Fail _) = ⊤
  All P (Step Choice c) = Pair (All P (c True)) (All P (c False)) 

  All' :  ∀ {a} -> (P : a -> Set) -> ND a -> Set
  All' = fold (\ { Fail _ → ⊤ ; Choice k → Pair (k True) (k False) })

  Any : ∀ {a} -> (P : a -> Set) -> ND a -> Set
  Any P (Pure x) = P x
  Any P (Step Fail _) = ⊥
  Any P (Step Choice c) = Either (Any P (c True)) (Any P (c False)) 

  -- And assign wp semantics to kleisi arrows
  wpAll : ∀ {a b : Set} -> (a -> ND b) -> (a -> b -> Set) -> (a -> Set)
  wpAll f pre x = All (pre x) (f x)

  wpAny : ∀ {a b : Set} -> (a -> ND b) -> (a -> b -> Set) -> (a -> Set)
  wpAny f pre x = Any (pre x) (f x)

  -- Note these are easy enough to define using the fold function
  --  They form a suitable homomorphism lifting predicates on a to
  --  predicates on ND a
\end{code}


\section{State}
\label{sec:state}

\begin{code}
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

  -- The usual semantics
  handle : ∀ {a} -> State a -> s -> Pair a s
  handle (Pure x) s = x , s
  handle (Step Get k) s = handle (k s) s
  handle (Step (Put x) k) s = handle (k tt) x 

  -- Define a propositional handler using handle
  wp0 : {a : Set} -> State a -> (s -> a -> s -> Set) -> (s -> Set)
  wp0 c P s = let x , s' = handle c s in P s x s'

  -- Define a propositional handler directly. This is harder to use:
  --  we want a relational spec between result and input-output states.
  wp1 : {a : Set} -> (P : a -> Set) -> State a -> (s -> Set)
  wp1 P (Pure x) s = P x
  wp1 P (Step Get k) s = wp' P (k s) s
  wp1 P (Step (Put s') k) s = wp' P (k tt) s'

  -- Showing how to lift the P relation/postcondition to a
  -- precondition (s -> Set)
  wp2 : {a : Set} -> (P : s -> a -> s -> Set) -> State a -> (s -> Set)
  wp2 P (Pure x) s = P s x s
  wp2 P (Step Get k) s = wp'' P (k s) s
  wp2 P (Step (Put s') k) s = wp'' P (k tt) s'
\end{code}

\section{Open questions}
\label{sec:questions}


\begin{itemize}
\item How can we use this technology to reason about combinations of
  effects? Eg mixing state and exceptions.

\item  What about other effects? General recursion? Async/await?
  Probablistic computations?  Shift/reset? Yield/fork?
  
\item How can we reason about compound computations built with |>>=|
  and |>>|?  There must be some 'law of consequence' that we can
  derive for specific handlers/effects -- is there a more general
  form?

\item  What is a specification of a program with effects? Can we define
  generalized refinement rules?

\end{itemize}




\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 



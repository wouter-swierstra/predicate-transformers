\documentclass[acmsmall, nonacm]{acmart}
\settopmatter{printfolios=false,printccs=false,printacmref=false}

%include polycode.fmt
%include agda.fmt
%include handlers.fmt

%include preamble.tex

\begin{document}
\title{Algebraic effects: specification and refinement}

\author{Wouter Swierstra}

\affiliation{
\institution{Universiteit Utrecht}
}
\email{w.s.swierstra@@uu.nl}

\begin{abstract}
  Pure functions are relatively easy to verify, yet it is much harder
  to reason about programs using effects. In this paper, we present a
  general framework, based on predicate transformer semantics, for
  specifying and calculating effectful programs from their
  specification.
\end{abstract}

%include ccs.tex

\maketitle

\section{Introduction}
\label{sec:intro}

One of the key advantages of pure functional programming is
\emph{compositionality}. Pure programs may be tested in isolation;
referential transparency---the ability to freely substitute equals for
equals---enables us to employ equational reasoning to prove two
expressions equal~\cite{wadler-critique}. This has resulted in a rich
field of program calculation in the Bird-Meertens
style~\citep*{algebra-of-programming, pearls}.

Many programs, however, are \emph{not} pure, but instead rely on a
variety of effects, such as mutable state, exceptions,
non-termination, or non-determinism. Unfortunately, it is less clear
how to reason about impure programs in a compositional fashion, as we can
no longer exploit referential transparency to reason about
subexpressions regardless of their context.

% \todo{Maybe focus more on program derivation?}

In recent years, \emph{algebraic effects} have emerged as a technique
to incorporate effectful operations in a purely functional
language.
%\todo{Citations}
Algebraic effects clearly separate the
syntax of effectful operations and their semantics, described by
\emph{effect handlers}. In contrast to existing approaches such as
monad transformers, different effects may be processed in any given
order using a series of handlers.

This paper explores how to reason about programs written using
algebraic effects using predicate transformers. It presents a general
framework for deriving a verified effectful program from its
specification. We will sketch the key techniques developed herein,
before illustrating them with numerous examples:

% What is the specification of a program written using algebraic
% effects?  How can we show that a program satisfies a specification? Or
% indeed derive a program from its specification?


\begin{itemize}
\item We show how the syntax of effects may be given by a free monad
  in type theory. The semantics of these effects are given by a
  \emph{handler}, that assigns meaning to the syntactic operations
  provided by the free monad. Such handlers typically execute the
  effects to produce some \emph{result value}. We show how we can also
  describe the behaviour of a program more abstractly by writing
  handlers that compute a \emph{proposition}, capturing the expected
  behaviour without having to execute the corresponding effects. These
  \emph{propositional handlers} may then be used to transform
  predicates on the result values of an effectful computation to a
  predicate on the entire computation.
\item Next we show how to assign \emph{predicate transformer
    semantics} to computations arising from Kleisli arrows on such
  free monads. Together with a propositional handler, this gives us
  the machinery to specify the desired outcome of an effectful
  computation and assign it a weakest precondition semantics.
\item Using these weakest precondition semantics, we can define a
  notion of \emph{refinement} on computations using algebraic
  effects. By further extending our free monad with
  \emph{propositions}, mixing specifications and programs, we can use
  this refinement relation to derive a correct effectful program from
  its specification.
\end{itemize}

We have applied these techniques to a range of example effects and
used the corresponding refinement relation to \todo{do something
  interesting}.

The examples, theorems and proofs have all been formally verified in
the dependently typed programming language Agda~\cite{agda}, but they
techniques translate readily to other proof assistants based no
dependent types such as Idris~\cite{brady} or Coq~\cite{coq}. The sources
associated with our our development are available
online.\footnote{\url{https://github.com/wouter-swierstra/handlers}}

% \item Using such predicate transformer semantics, we can define a
%   generic notion of \emph{program refinement}, allowing the
%   calculation of (effectful) programs from their specification. The
%   notion of refinement we end up with depends on the semantics
%   (handler) du jour:
%   \begin{itemize}
%   \item for pure functions, |f refines g| corresponds to extensional
%     equality between functions |f| and |g|;
%   \item for partial functions (Maybe), |f refines g| holds when |dom
%     (f) subset dom(g)| and |f| and |g| agreeing on |dom(f)|.
    
%   \item for nondeterministic computations and the |All| handler, |f
%     refines g| for all inputs |x|, |f x subset g x|. (hypothesis)
%   \item for nondeterministic computations and the |Any| handler, |f
%     refines g| for all inputs |x|, |f x subset g x|. (hypothesis)
%   \item for stateful computations, the refinement relation corresponds
%     closely to the traditional refinement relation on Dijkstra's
%     guarded command language.
    
%   \end{itemize}
% \end{itemize}

\section{Warm-up}
\label{sec:intro}
%if style == newcode
\begin{code}
module Check where

open import Prelude
open import Level hiding (lift)

module Free where
\end{code}
%endif

We begin by defining a data type for free monads in Agda in the style
of Hancock and Setzer~\citeyear{hancock-setzer-I,
  hancock-setzer-II}:
\begin{code}
  data Free (C : Set) (R : C -> Set) (a : Set) : Set where
    Pure : a -> Free C R a
    Step : (c : C) -> (R c -> Free C R a) -> Free C R a
\end{code}

You may want to think of |C| as being the type of \emph{commands}. A
computation described by the free monad |Free C R| either returns a
result of type |a| or issues a command |c : C|. For each |c : C|,
there is a set of responses |R c|. The second argument of the |Step|
constructor corresponds to the continuation, describing how to proceed
after receiving a response of type |R c|. It is straightforward to
show that the |Free| data type is indeed a monad:
\begin{code}
  fmap : (Forall (C R a b)) (a -> b) -> Free C R a -> Free C R b
  fmap f (Pure x)    = Pure (f x)
  fmap f (Step c k)  = Step c (\ r -> fmap f (k r)) 

  return : (Forall (C R a)) a -> Free C R a
  return = Pure
  _>>=_ : (Forall (C R a b)) Free C R a -> (a -> Free C R b) -> Free C R b
  Pure x   >>= f  = f x
  Step c x >>= f  = Step c (\ r -> x r >>= f)
\end{code}
Finally, we will sometimes \emph{fold} over elements of |Free C R a|
using the following recursion principle:
\begin{code}
  fold : (Forall(C R a l)) (implicit(b : Set l)) ((c : C) -> (R c -> b) -> b) -> (a -> b) -> Free C R a -> b
  fold alg pure (Pure x) = pure x
  fold alg pure (Step c k) = alg c (\ r -> fold alg pure (k r))
\end{code}

\section{Partiality}
\label{sec:maybe}
%if style == newcode
\begin{code}
module Maybe where

  open Free
\end{code}
%endif

We can define the data type for |Partial| computations, corresponding
to |Maybe| monad, by making the following choice for |C| and |R|:
\begin{code}
  data C : Set where
    Abort : C

  R : C -> Set
  R Abort = ⊥

  Partial : Set -> Set
  Partial = Free C R
\end{code}
There is a single command, |Abort|; there is no continuation after
issuing this command, hence the type of valid responses is empty. It is
sometimes convenient to define a smart constructor for failure:
\begin{code}
  abort  : (Forall(a)) Partial a
  abort  = Step Abort (\ ())
\end{code}
A computation of type |Partial a| will either return a value of type |a|
or fail, issuing the |abort| command.

\subsection*{Example: fast multiplication}

Suppose have a function that computes the product of the numbers
stored in a list:

\begin{code}
  product : List Nat -> Nat
  product = foldr 1 _*_
\end{code}

If this list contains a zero, however, we can short circuit the
computation and return zero immediately. To do so, we define the
following computation:

\begin{code}
  fastProduct : List Nat -> Partial Nat
  fastProduct Nil                 = return 1
  fastProduct (Cons Zero xs)      = abort
  fastProduct (Cons (Succ k) xs)  = fmap (\ n -> Succ k * n) (fastProduct xs)
\end{code}
To run this computation, we provide a handler that maps |abort| to
the default value |0|:
\begin{code}
  zeroHandler : Partial Nat -> Nat
  zeroHandler (Pure x)          = x
  zeroHandler (Step Abort _)    = 0
\end{code}

We would like to validate that the |product| and composition of
|zeroHandler| |fastproduct| always compute the same result. We can
do so directly by proving the following statement:

\begin{spec}
  correctness : ∀ xs -> handle Zero (fastProduct xs) == product xs
\end{spec}
To illustrate the approach we will take in this paper, however, we
will explore a slightly more roundabout route. To begin, we can define
the following predicate transformer, that, given a predicate |P : Nat ->
Set|, maps this to a predicate on |Partial Nat|:
\begin{code}
  zeroPT : (P : Nat -> Set) -> Partial Nat -> Set
  zeroPT d P (Pure x)          = P x
  zeroPT d P (Step Abort _)    = P 0
\end{code}
This handler is slightly different from typical handlers that aim to
run a computation written using algebraic effects, as it
returns returns a \emph{proposition} rather than a \emph{value}. We can now
reformulate our correctness property in terms of this handler as follows:
\begin{code}
  spec : List Nat -> Nat -> Set
  spec xs n = product xs == n

  correctness : ∀ xs -> zeroPT (spec xs) (fastProduct xs)
\end{code}
Given the specification of our computation, expressed as a relation
between inputs and outputs, proving this correctness statement shows
|fastProduct| satisfies its specification.

At this point, however, there is no guarantee that the
\emph{proposition} computed by the propositional handler
|zeroPT| is related in any way to the result returned by our
|zeroHandler| function. To ensure that |zeroHandler . fastproduct| does indeed
behave as we expect, we should additionally prove that our
propositional handler is sound with respect to the |zeroHandler|:

\begin{spec}
  soundness : (c : Partial Nat) (P : Nat -> Set) -> zeroPT P c -> P (zeroHandler c) 
\end{spec}

This example illustrates some of the key techniques used throughout
this paper: the |zeroHandler| handles effectful computations; the
|zeroPT| handler assigns meaning to these computations without
executing them; the a |soundness| guarantees that it suffices to work
with the propositions computed by the |zeroPT| handler, rather than
reason about |zeroHandler| directly.

Unlike many effectful programs, however, this example is \emph{total}
and only uses the short-circuiting behaviour of |Partial| for
efficiency. Let us now consider another example, where we truly want
to reason about partial functions.

\subsection*{Example: division}

We begin by defining a small expression language, closed under
division and natural numbers:

\begin{code}
  data Expr : Set where
    Val : Nat -> Expr
    Div : Expr -> Expr -> Expr
\end{code}

To evaluate these expressions, we can define a \emph{monadic}
interpreter, using the |Partialg| monad to handle division-by-zero
errors:

\begin{code}
  ⟦_⟧ : Expr -> Partial Nat
  ⟦ Val x ⟧      =  return x
  ⟦ Div e1 e2 ⟧  =  ⟦ e1 ⟧ >>= \ v1 ->
                    ⟦ e2 ⟧ >>= \ v2 ->
                    div v1 v2
                      where
                      div : Nat -> Nat -> Partial Nat
                      div n Zero      = Abort
                      div n (Succ k)  = n ÷ (Succ k)
\end{code}
The division operator (|_÷_|) requires an (implicit) proof that the
divisor is non-zero.

Alternatively, we can specify the semantics of our language using a
\emph{relation}:

\begin{code}
  data _⇓_ : Expr -> Nat -> Set where
    Base : (Forall(x)) Val x ⇓ x
    Step : (Forall(l r x y)) l ⇓ v1 -> r ⇓ (Succ v2) -> Div l r ⇓ (v1 ÷ (Succ v2))
\end{code}
In this definition, we rule out erroneous results by asserting that
the divisor always evaluates to a non-zero value.

How can we relate these two definitions? We start by defining a
propositional handler, \emph{transforming} a predicate |P : a -> Set| to
computations of type |Partial a|:
\begin{code}
  mustPT : (Forall(a)) (P : a -> Set) -> Partial a -> Set
  mustPT P (Pure x)          = P x
  mustPT P (Step Abort _)  = ⊥
\end{code}
For any predicate |P : a -> Set|, the statement |mustPT P c| holds
when a computation |c| of type |Partial a| successfully returns a value
of type |a| that satisfies |P|.

We can define the following predicate characterizing when evaluating
an expression will produce a result:
\begin{code}
  SafeDiv : Expr -> Set
  SafeDiv (Val x)       = (Val x ⇓ Zero) -> ⊥
  SafeDiv (Div e1 e2)   = (e2 ⇓ Zero -> ⊥) × SafeDiv e1 × SafeDiv e2
\end{code}
We can use this predicate to prove the following correctness result:
\begin{code}
  correct : (e : Expr) -> SafeDiv e -> mustPT (e ⇓_) ⟦ e ⟧    
\end{code}
This pattern of transforming a predicate over partial computation, as we do
in the expression |mustPT (e ⇓_) ⟦ e ⟧|, invites the following definition:
\begin{code}
  wp : (Forall(a b)) (a -> Partial b) -> (b -> Set) -> (a -> Set)
  wp f P = mustPT P . f
\end{code}
That is, we can \emph{compute} the weakest precondition |wp f P x|
that guarantees that a partial computation, |f x|, returns a result
satisfying |P|. This |wp| function assigns a \emph{predicate
  transformer semantics} to Kleisli arrows.
We can use this definition to reformulate our correctness proof as
follows:
\begin{code}
  correct : (e : Expr) -> SafeDiv e -> wp ⟦_⟧ (e ⇓_) e
\end{code}



\subsection*{Refinement}
\label{sec:refinement-maybe}

We now consider how we can relate functions, specifications (given by
a relation between input and output), and predicate transformers. We
begin by defining the following notion of refinement (|_⊑_|):

\begin{code}
  _⊆_ : (a -> Set) -> (a -> Set) -> a -> Set
  P ⊆ Q = \ x -> P x -> Q x
  
  _⊑_ : (PT1 PT2 : (b -> Set) -> (a -> Set)) -> Set
  PT1 ⊑ PT2 = (P : b -> Set) -> PT1 P ⊆ PT2 P
\end{code}
This is straight from the literature on refinement calculus.

Using our |wp| function, we can now use this to compare two partial
functions:
\begin{code}
  refineFun : (f g : a -> Partial b) -> Set
  refineFun = wp f ⊑ wp g
\end{code}
We can furthermore show that this notion of refinement on functions is
familiar: |f ⊑ g| holds if and only if |f x == g x| for all points |x
elem dom(f)|. 

We can also use these weakest precondition semantics to assign meaning
to \emph{specifications}, given by a relation |R : a -> b -> Set|:
\begin{code}
  wpR : (R : a -> b -> Set) -> (b -> Set) -> (a -> Set)
  wpR R P x = R x ⊆ P 
\end{code}

We can now succinctly formulate the desired soundness property:
\begin{code}
  soundness : wp ⟦_⟧ ⊑  wpR (_⇓_)
\end{code}
In other words, the function |⟦_⟧ : Expr -> Partial Val| is a sound
implementation of the semantics given by the relation |_⇓_ : Expr ->
Val -> Set|. We can do so \emph{without} explicitly introducing any
further constraints on the expressions -- such as the |SafeDiv|
predicate we saw previously.

These definitions let us prove useful properties, such as:

\begin{code}
  ruleOfConsequence : (c : Partial a) (f : a -> Partial b) ->
    (P : b -> Set) -> mustPT (wp f P) c -> mustPT P (c >>= f)
\end{code}

All in all, this shows how we can relate predicate transformers (|(b
-> Set) -> (a -> Set)|), specifications (|a -> b -> Set|),
implementations (|a -> b|) -- in a single framework.



% \paragraph{Soundness}

% The |lift| function computes a predicate on computations of type
% |Partial a|. Yet how can we know that this predicate is meaningful in
% any way? The type of the |lift| function alone does not guarantee
% anything about its behaviour. To relate the predicate being computed,
% we therefore need to show that the our propositional handler is
% \emph{sound}. 

% Consider the usual `handler' for |Partial| that returns a default
% value when encountering a failure:

% \begin{code}
%   run : (Forall (a)) a -> Partial a -> a
%   run d (Pure x)          = x
%   run d (Step Abort _)  = d
% \end{code}
% To prove the soundness of our |lift| function with respect to this
% handler amounts to proving:
% \begin{spec}
%   soundness : (Forall(a)) (d : a) (P : a -> Set) (m : Partial a) -> lift P m -> P (run d m)
% \end{spec}
% The proof of this result follows trivially after pattern matching on
% the monadic computation |m|. Of course, there may be alternative
% definitions of |lift| that are sound with respect to some other
% handler---but this depends on the intended semantics of the algebraic
% effects involved. The crucial observation, however, is that soundness
% of propositional handlers are always relative to another semantics.


% \subsection*{Intermezzo: types and predicate transformers}

% Before studying other effects, it is worth making the construction of
% specifications more explicit.
% \begin{itemize}
% \item A specification on a value of type |A| is a predicate |A ->
%   Set|;
% \item A specification of a function of type |A -> B| is a
%   \emph{predicate transformer} of type |(B -> Set) -> (A -> Set)|.
% \end{itemize}
% You may recognise this construction as the contravariant Hom functor
% on |Set|, i.e., |Hom(_,Set)|. In our example evaluator, we wanted to
% specify the behaviour of a function of type |Expr -> Partial Nat|. By
% using the |lift| function, this amounts to a predicate transformer of
% the form |(Nat -> Set) -> (Expr -> Set)|.

% This pattern can be extended to many other effects, as we shall
% explore now.

\section{State}
\label{sec:state}

We can do something similar for mutable state. We will define a module
parametrized by a type |s|, representing the type of our mutable
state:

\begin{code}
module State (s : Set) where
\end{code}

%if style == newcode
\begin{code}
  open Free  
\end{code}
%endif

As before, we assemble our free monad from the commands |C| and
responses |R|:

\begin{code}
  data C : Set where
    Get : C
    Put : s -> C

  R : C -> Set
  R Get      = s
  R (Put _)  = ⊤

  State : Set -> Set
  State = Free C R
\end{code}

Once again, we can define a pair of smart constructors to make it
easier to write stateful computations:
\begin{code}
  get : State s
  get = Step Get return

  put : s -> State ⊤
  put s = Step (Put s) (\_ -> return tt)
\end{code}

The usual handler for stateful computations maps our free monad,
|State s|, to the state monad:
\begin{code}
  run : (Forall(a)) State a -> s -> Pair a s
  run (Pure x) s          = (x , s)
  run (Step Get k) s      = run (k s) s
  run (Step (Put x) k) s  = run (k tt) x 
\end{code}
Inspired by the previous sections, we can define the following
predicate transformer semantics:
\begin{code}
  lift : (Forall(a)) (P : Pair a s -> Set) -> State a -> (s -> Set)
  lift P (Pure x) s           = P (x , s)
  lift P (Step Get k) s       = lift P (k s) s
  lift P (Step (Put s') k) s  = lift P (k tt) s'
\end{code}
Given any predicate |P| on the final state and result, it
computes the weakest precondition required of the initial state to
ensure |P| holds upon completing the computation.

Once again, we can prove soundness of this predicate transformer with
respect to the |run| above:

\begin{code}
  soundness : (Forall(a)) (P : Pair a s -> Set) -> (c : State a) -> (i : s) -> lift P c i -> P (run c i)
\end{code}
%if style == newcode           
\begin{code}           
  soundness P (Pure x) i p = p
  soundness P (Step Get x) i lift = soundness P (x i) i lift
  soundness P (Step (Put x) k) i lift with soundness P (k tt)
  ... | ih = ih x lift             
\end{code}
%endif

We oftentimes want to write a specification as a \emph{relation}
between input and output states. To do so, we can partially apply the
predicate |P| before calling |lift|:
\begin{code}
  liftR : {a : Set} -> (P : s -> a -> s -> Set) -> State a -> (s -> Set)
  liftR P c s = lift (uncurry (P s)) c s
\end{code}
Reusing our previous soundness result, we can show that the |liftR|
is sound with respect to the |run| semantics defined above.

\subsection*{Example: tree labelling}
\label{sec:trees}

\todo{Do example}

\subsection*{Rule of consequence}
\label{sec:consequence}





\section{Nondeterminism}
\label{sec:non-det}

Can we repeat this construction of predicate transformer semantics for
other effects? In this section, we will show how we can lift a
predicate |a -> Set| over non-deterministic computations returning
values of type |a|. Once again, we begin by defining a free monad
describing the effects that can be used to describe non-deterministic
computations:

%if style == newcode
\begin{code}
module Nondeterminism where

  -- Define a free monad
  open Free
\end{code}
%endif

\begin{code}
  data C : Set where
    Fail : C
    Choice : C

  R : C -> Set
  R Fail = ⊥
  R Choice = Bool
\end{code}

Here we have chosen to define two possible commands: |Fail| and
|Choice|. The |Fail| constructor corresponds to a non-deterministic
computation that will not return any results; conceptually, the
|Choice| constructor takes two arguments and non-deterministically
chooses between them. To model this, the response used in the
continuation of the free monad, |R Choice|, is a |Bool|, indicating
which argument to choose. We can make this more clear by defining the
following shorthands for non-deterministic computations, |ND|, and
its constructors:
\begin{code}
  ND : Set -> Set
  ND = Free C R

  fail : (Forall(a)) ND a
  fail = Step Fail (\ ())

  choice : (Forall(a)) ND a -> ND a -> ND a
  choice c1 c2 = Step Choice (\ b -> if b then c1 else c2)
\end{code}

Next, we turn our attention to lifting a predicate of type |a -> Set|
to computations of type |ND a -> Set|. There are two canonical ways to
do so:

> All : (Forall(a)) (P : a -> Set) -> ND a -> Set
> All P (Pure x) = P x
> All P (Step Fail _) = ⊤
> All P (Step Choice c) = Pair (All P (c True)) (All P (c False)) 
> 
> Any : (Forall(a)) (P : a -> Set) -> ND a -> Set
> Any P (Pure x) = P x
> Any P (Step Fail _) = ⊥
> Any P (Step Choice c) = Either (Any P (c True)) (Any P (c False))

The statement |All P nd| holds when |P| holds for \emph{all} possible
values returned by the non-deterministic computation |nd|; the
statement |Any P nd| holds when |P| holds for \emph{any} possible
value returned by the non-deterministic computation |nd|. Both these
functions could also be defined using |fold|, for instance:

> All' :  (Forall(a)) (P : a -> Set) -> ND a -> Set
> All' = fold (\ { Fail _ → ⊤ ; Choice k → Pair (k True) (k False) })

We can relate both these predicates to the usual `list handler' for
non-determinism and prove appropriate soundness results.

\subsection*{Example}
\label{example-non-det}

Using these handlers, we can reason about non-deterministic
computations. The |guard| function, for example, can be used to prune
computations to satisfy a given predicate:

\begin{code}
  guard : (Forall(a))  (p : a -> Bool) -> a -> ND a
  guard p x = if p x then return x else fail
\end{code}
Subsequently, we can prove that guard will always return results
satisfying |P|:
\begin{code}
  guardCorrect : (Forall(a)) (p : a -> Bool) -> (x : a) -> All (\ x -> So (p x)) (guard p x)
\end{code}
%if style == newcode
\begin{code}
  guardCorrect p x with inspect (p x)
  guardCorrect p x | True with-≡ eq rewrite eq = lemma (p x) eq
    where
      lemma : (b : Bool) -> b == True -> So b
      lemma True p = tt
      lemma False ()
  guardCorrect p x | False with-≡ eq rewrite eq = tt
\end{code}
%endif

\todo{Bigger example? n-queens?}

\section{General recursion, totally free}

Besides these well-known effects, we can handle \emph{general
  recursion} in a similar fashion. To do so, we introduce a module
|General|. The module is parametrized by parametrized by two types |I|
and |O| and will be used to capture recursive calls to a function of
type | I -> O|:\footnote{This can be readily generalized to
  \emph{dependent functions} of type |(i : I) -> O i|, but we will not
    need this in the examples covered here.}

\begin{code}
module General (I : Set) (O : Set) where  
\end{code}


%if style == newcode
\begin{code}
  open Free  
\end{code}
%endif

To represent such calls, we define a single command, corresponding to
making a recursive call on an argument |i : I| and receiving a
response of type |O i|:

> data C : Set where
>   Call : I -> C
>
> R : C -> Set
> R (Call x) = O
>
> Rec : Set -> Set
> Rec = Free C R

Once again, we can define a smart constructor to make it a bit easier
to define recursive functions.

> call : I -> Rec O
> call i = Step (Call i) Pure

There are many different handlers that we can use: generating a
coinductive trace, unfolding a fixed number of calls, calculating
Bove-Capretta predicates, or providing a proof of
well-foundedness. Here, we will take a slightly different approach,
requiring that all recursive calls satisfy an \emph{invariant} to
ensure that a given property of the output holds:

> handle : (Inv : I -> O -> Set) (P : O -> Set) -> Rec O -> Set
> handle Inv P (Pure x)           = P x
> handle Inv P (Step (Call x) k)  = (o : O) -> Inv x o -> handle Inv P (k o)

\todo{Soundness?}

\subsection*{Example: quickSort}
\label{quicksort}

%if style == newcode
\begin{code}
module QS where  
  open Free
\end{code}
%endif

To illustrate how to reason with these invariants, we will show how to
reason about a function that is not structurally recursive, namely
|quickSort|. To do so, we import the |General| module, fixing the type
of our |quickSort| function


> open General (Pair (Nat -> Bool) (List Nat)) (List Nat)

\begin{code}  
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
  
\end{code}


\section{Open questions}
\label{sec:questions}


\begin{itemize}
\item How can we use this technology to reason about combinations of
  effects? Eg mixing state and exceptions.

  
\item How can we reason about compound computations built with |>>=|
  and |>>|?  There must be some 'law of consequence' that we can
  derive for specific handlers/effects -- is there a more general
  form? What about loops/if?

\item  What is a specification of a program with effects? Can we define
  generalized refinement rules?

\item Relation with equations/equational part of algebraic effects?

\item Connection with relational specifications

\item wp (s,q) or wp (s,p) implies wp(s,q or p) -- but not the other
  way around. The implication in the other direction only holds when
  the program is deterministic.

  
\end{itemize}

\section{Discussion}
\label{sec:discussion}

\subsection{Related work}
\label{sec:related-work}

Just do it

Examples:
- Dutch National Flag (with recursion)
- Goat/Wolf/Bridge crossing

\begin{acks}
I would like to thank my fans.  
\end{acks}

\nocite{*}
\DeclareRobustCommand{\tussenvoegsel}[2]{#2}
\bibliography{handlers}


\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End: 



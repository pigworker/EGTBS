\section{Type Theorists Worry About Equality}

%if False
\begin{code}
module Worry where

open import Agda.Primitive renaming (_⊔_ to _\-/_)

open import Slime
\end{code}
%endif

An ingenue (or very sophisticated troll) once wrote to some mathematical mailing list
asking whether category theory and type theory were the same. Some category theorists
answered vaguely in the positive, at which point the type theorists accused them of
insufficiently interrogating the meaning of `the same'. The title of this section is
tantamount to a definition of the discipline, especially if you come from the school
which takes the classification of a thing to be the diagonal of the classified
partial equivalence relation which says when two things are the same.

Informally, a category is given by
\begin{enumerate}
\item some notion of \emph{objects};
\item for every pair of objects, \emph{source} and \emph{target},
  some notion of \emph{arrows} from source to target;
\item for each object, an \emph{identity} arrow from that object to itself;
\item for each pair of arrows which meet in the middle, a \emph{composite} arrow from
  the source of the first to the target of the second;
\item ensuring that composition absorbs identity and associates, i.e., that some
  equations between arrows hold.
\end{enumerate}

For thinnings, our objects are scopes and |<=| tells us what the arrows are. We have
candidates for identity and composition. We can take the same view of types and
functions: |Set| gives our objects, |->| our arrows, and we have the identity function
and function composition.

But any type theorist will ask, or rather will \emph{be asked} by their equipment,
`What is the status of equations between arrows?'. For thinnings, which are first
order inductive data structures (indeed, bit vectors), the intensional |~| should
suffice; for functions, |~| is dangerously restrictive, identifying only functions
with the same \emph{implementation}, up to definitional equality. Any workable
notion of category within type theory has to negotiate this distinction, which is
waved away in everyday mathematical practice.

We have three options:

\begin{enumerate}
\item \emph{Worry About Equality.}~ Work to replace intensional |~| by something which
  better reflects mathematical intuition. That is the work of many lifetimes,
  mine included, and it is beginning to pay off. Observational Type Theory gave
  a good answer to when values are equal, but not such a good answer to when types are
  equal. (It was never the basis of a usable implementation, a fact for which I
  bear some blame.) Homotopy Type Theory gives a better answer, and in its Cubical
  variant, is beginning to materialise. This is the best option, if you have
  patience.
\item \emph{Tell Lies.}~ Postulate that |~| has the properties we wish it had, e.g.
  that pointwise equal functions are equal. Get on with exploring the important ideas.
  Unfortunately, the computational properties of postulates frustrate the execution of
  actual, if sophisticated, programs when proofs of equations are used to transport
  actual values between merely provably equal types. None the less, this is the best
  option, if you have undergraduates.
\item \emph{Tell Weaker Truths.}~ Arrange to work up to |~| when you
  can (e.g., with thinnings) and to weaker notions (e.g., pointwise equality for
  functions) when you cannot. This is the best option, if you are in a hurry.
\end{enumerate}

My head is with option 1, my heart is with option 2, but my entire digestive system is
with option 3, so that is how I shall proceed in this paper.

The plan, which is far from original, is to work with setoids of arrows,
carefully managing the appropriate notion of equivalence on a case-by-case basis.
A \emph{setoid} is a set equipped with an \emph{arbitrary} equivalence relation.

%format Setoid = "\D{Setoid}"
%format El = "\F{El}"
%format Eq = "\F{Eq}"
%format Rf = "\F{Rf}"
%format Sy = "\F{Sy}"
%format Tr = "\F{Tr}"
%format lsuc = "\D{1+}"
\begin{definition}[Setoid]
Every level of the hierarchy is equipped with a notion of |Setoid|.
\begin{code}
record Setoid l : Set (lsuc l) where
  field  El  :  Set l                                         -- |El|ements
         Eq  :  El -> El -> Set l                             -- |Eq|uivalence
         Rf  :  (x : El)      -> Eq x x                       -- \F{R}e\F{f}lexivity
         Sy  :  (x y : El)    -> Eq x y -> Eq y x             -- |Sy|mmetry
         Tr  :  (x y z : El)  -> Eq x y -> Eq y z -> Eq x z   -- |Tr|ansitivity
open Setoid public
\end{code}
\end{definition}

Let us now build some tools to enable the construction of some |Setoid|s that we
can use to specify arrows in categories and what we expect to be able to prove
about them.

\begin{definition}[Intensional |Setoid|s]
Every |Set| gives rise to a |Setoid| whose equivalence is given by |~|.
%format IN = "\F{\mathrm{IN}}"
\begin{code}
IN : {-<-} forall {l} -> {->-} Set l -> Setoid l
El  (IN X) =   X
Eq  (IN X) =   _~_
Rf  (IN X) x               = r~
Sy  (IN X) x  y    r~      = r~
Tr  (IN X) x  y z  r~  r~  = r~
\end{code}
\end{definition}

\begin{definition}[Comprehension |Setoid|s]
Fix levels |k| and |l|.
\begin{code}
module _ {k l : Level} where
\end{code}
From any |Setoid k|, we can construct a further |Setoid| by \emph{proof irrelevant}
comprehension on its elements with respect to a predicate in |l|.
%format || = "\F{\parallel}"
%format _||_ = "\F{" _ "}\!" || "\!\F{" _ "}"
%format PI = "\F{\mathrm{PI}}"
%format IM = "\F{\mathrm{IM}}"
%format SG = "\F{\mathrm{SG}}"
%format s0 = s sb0
%format s1 = s sb1
%format t0 = t sb0
%format t1 = t sb1
%format t2 = t sb2
%format t01 = t sb01
%format t12 = t sb12
\begin{code}
  _||_ : (T : Setoid k)(P : El T -> Set l) -> Setoid (k \-/ l)
  El  (T || P) = [* x :: El T ]* P x
  Eq  (T || P) (t0 , _) (t1 , _) = Eq T t0 t1 * One {l}
  Rf  (T || P) (t , _)                                           = Rf T t , <>
  Sy  (T || P) (t0 , _) (t1 , _) (t01 , <>)                      = Sy T t0 t1 t01 , <>
  Tr  (T || P) (t0 , _) (t1 , _) (t2 , _) (t01 , <>) (t12 , <>)  = Tr T t0 t1 t2 t01 t12 , <> 
\end{code}
\end{definition}

The |Eq| for comprehensions demands an element of the unit type instead
of a proof that the proofs of |P| are equal: this is both a vestigial
marker of some information that has been thrown away, and the means to
bully Agda into accepting that the |Eq| type is at level |k \-/ l| rather
than level |k|.

\begin{definition}[Pointwise |Setoid|s]
Fix a |Set| |S| and a family of |Setoid|s |T|.
\begin{code}
module _ {k l}(S : Set k)(T : S -> Setoid l) where
\end{code}
We may then construct |Setoid|s which lift |T| pointwise by quantification
(universal or existential over |S|.
\begin{code}
  PI : Setoid (k \-/ l)
  El  PI     = (s : S) -> El (T s)             -- explicit universal quantification
  Eq  PI f g = (s : S) -> Eq (T s) (f s) (g s)
  Rf  PI f s          = Rf (T s) (f s)
  Sy  PI f g q s      = Sy (T s) (f s) (g s) (q s)
  Tr  PI f g h p q s  = Tr (T s) (f s) (g s) (h s) (p s) (q s)

  IM : Setoid (k \-/ l)
  El  IM     = {s : S} -> El (T s)             -- implicit universal quantification
  Eq  IM f g = (s : S) -> Eq (T s) (f {s}) (g {s})
  Rf  IM f s          = Rf (T s) f
  Sy  IM f g q s      = Sy (T s) f g (q s)
  Tr  IM f g h p q s  = Tr (T s) f g h (p s) (q s)

  SG : Setoid (k \-/ l)
  El  SG = [* s :: S ]* El (T s)               -- existential quantification
  Eq  SG (s0 , t0) (s1 , t1) = Sg (s0 ~ s1) \ { r~ -> Eq (T s0) t0 t1 }
  Rf  SG (s , t)                                               = r~ , Rf (T s) t
  Sy  SG (s , t0) (.s , t1) (r~ , t01)                         = r~ , Sy (T s) t0 t1 t01
  Tr  SG (s , t0) (.s , t1) (.s , t2)   (r~ , t01) (r~ , t12)  = r~ , Tr (T s) t0 t1 t2 t01 t12
\end{code}
\end{definition}

\begin{definition}[Projection |Setoid|s]
Fix a |Set| |X|.
\begin{code}
module _ {l}{X : Set l} where
\end{code}
If we have a projection from |X| to the carrier of a |Setoid|, we can
treat |X| as a quotient, working up to setoid equivalence of projections.
%format \\ = "\F{\fatbslash}"
%format _\\_ = "\F{" _ "\!}" \\ "\F{\!" _ "}"
\begin{code}
  _\\_ : (S : Setoid l)(p : X -> El S) -> Setoid l
  El  (S \\ p)        = X
  Eq  (S \\ p) x y    = Eq S (p x) (p y)
  Rf  (S \\ p) x      = Rf S (p x)
  Sy  (S \\ p) x y    = Sy S (p x) (p y)
  Tr  (S \\ p) x y z  = Tr S (p x) (p y) (p z)
\end{code}
The notation necessarily identifies the target of the projection, but leaves
the source implicit.
\end{definition}

\begin{craft}[Green Things in Blue Packaging]
I anticipate that we shall need to construct explanations which look like
equational proofs, but are constructed within the equivalence of a known
|Setoid|. I therefore introduce a type constructor whose entire purpose is
to fix the |Setoid| at work. There is no general way to infer the setoid
|X| from a type which is known to be |Eq X x y|, so the craft lies in ensuring
that we never forget which |Setoid| we work in.
%
%format :> = "\mathrel{\D{\ni}}"
%format ~~ = "\mathrel{\D{\approx}}"
%format _:>_~~_ = "\D{" _ "}\!" :> "\!\D{" _ "}\!" ~~ "\!\D{" _ "}"
%format eq = "\C{eq}"
%format qe = "\F{qe}"
%format ~[ = "\F{\approx\!\!\![}"
%format >~ = "\F{\rangle\!\!\!\approx}"
%format ~< = "\F{\approx\!\!\!\langle}"
%format ]~ = "\F{]\!\!\!\approx}"
%format ~[SQED] = "\F{\square}"
%format RfX = "\F{RfX}"
%format SyX = "\F{SyX}"
%format TrX = "\F{TrX}"
%format _~[_>~_ = _ ~[ _ >~ _
%format _~<_]~_ = _ ~< _ ]~ _
%format _~[SQED] = _ ~[SQED]
%format rS = "\F{r\!\!\approx}"
%format qprf = "\F{qprf}"
%
\begin{code}
record _:>_~~_ {l}(X : Setoid l)(x y : El X) : Set l where
  constructor  eq
  field        qe : Eq X x y
open _:>_~~_ public
\end{code}
When we formulate categorical laws, we shall use this wrapped version.
\end{craft}

At last, we are ready to say what a category might be.


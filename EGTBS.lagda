\documentclass[submission,copyright,creativecommons]{eptcs}
\providecommand{\event}{MSFP 2018} % Name of the event you are submitting to
\usepackage{breakurl}              % Not needed if you use pdflatex only.
%\usepackage{underscore}            % Only needed if you use pdflatex.
\usepackage{pig}
\usepackage{stmaryrd}
\usepackage{upgreek}
\usepackage[all]{xy}

\ColourEpigram
\newcommand{\D}[1]{\blue{\ensuremath{\mathsf{#1}}}}
\newcommand{\C}[1]{\red{\ensuremath{\mathsf{#1}}}}
\newcommand{\F}[1]{\green{\ensuremath{\mathsf{#1}}}}
\newcommand{\V}[1]{\purple{\ensuremath{\mathit{#1}}}}

\newcommand{\OPE}{\Updelta}

\title{Everybody's Got To Be Somewhere}
\author{
  Conor McBride
  \institute{Mathematically Structured Programming Group\\
             Department of Computer and Information Sciences\\
             University of Strathclyde, Glasgow}
  \email{conor.mcbride@@strath.ac.uk}
}
\def\titlerunning{Everybody's Got To Be Somewhere}
\def\authorrunning{C.T. McBride}
%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%format inductive = "\mathkw{inductive}"
%format constructor = "\mathkw{constructor}"
%format pattern = "\mathkw{pattern}"
%format rewrite = "\mathkw{rewrite}"
%format forall = "\forall"
%format . = "."

%format combK = "\F{\mathbb{K}}"
%format combS = "\F{\mathbb{S}}"

%if False
\begin{code}
module EGTBS where
\end{code}
%endif

\begin{document}
\maketitle

\begin{abstract}
The key to any nameless representation of syntax is how it indicates the variables we choose
to use and thus, implicitly, those we discard. Standard de Bruijn representations delay 
discarding \emph{maximally} till the \emph{leaves} of terms where
one is chosen from the variables in scope at the expense of the rest. Consequently, introducing new but unused
variables requires term traversal. This paper introduces a
nameless `\emph{co}-de-Bruijn' representation which makes the opposite canonical choice, delaying
discarding \emph{minimally}, as near as possible to the \emph{root}.  It is literate Agda: dependent types
make it a practical joy to express and be driven by strong intrinsic invariants
which ensure that scope is aggressively whittled down to just the \emph{support} of each subterm, in which every
remaining variable occurs somewhere. The construction is generic, delivering a
\emph{universe} of syntaxes with higher-order \emph{meta}variables, for which the appropriate notion of
substitution is \emph{hereditary}. The implementation of simultaneous substitution exploits tight scope control
to avoid busywork and shift terms without traversal. Surprisingly, it is
also intrinsically terminating, by structural recursion alone.
\end{abstract}


%\section{Introduction}

When I was sixteen and too clever by half, I wrote a text editor which cached
a plethora of useful but redundant pointers into the buffer, just to shave a handful
of nanoseconds off redisplay. Accurately updating these pointers at each
keystroke was a challenge which taught me the hard way about the value of simplicity.
Now, I am a dependently typed programmer. I do not keep invariants: invariants keep me.

This paper is about scope invariants in nameless representations of syntax. One motivation
for such is eliminating redundant name choice to make $\alpha$-equivalence trivial. Classic de Bruijn
syntaxes~\cite{deBruijn:dummies} replace name by number:
variable uses count either out to the binding (\emph{indices}), or
in from root to binding (\emph{levels}). Uses are found at the
leaves of syntax trees, so any operation which modifies the sequence of variables
in scope requires traversal. E.g., consider this
$\beta$-reduction (under $\lambda x$) in untyped $\lambda$-calculus.
\newcommand{\fb}[1]{\framebox{\ensuremath{#1}}}
\[\begin{array}{rrcl}
\mbox{name}    & \lambda x.\: (\lambda y.\:\, y\:x\:(\lambda z.\: z\:(y\:z)))\:\underline{(x\:(\lambda v.\:v))}
               & \leadsto_\beta
               & \lambda x.\: \underline{(x\:(\lambda v.\:v))}\:x\:(\lambda z.\: z\:(\underline{(x\:(\lambda v.\:v))}\:z)\\
\mbox{index}   & \lambda \;\,.\: (\lambda \;\,.\: 0\:1\:(\lambda \;.\: 0\:(1\:0)))\:\underline{(0\:(\lambda \;.\:0))}
               & \leadsto_\beta
               & \lambda \;\,.\: \underline{(0\:(\lambda \;.\:0))}\:0\:(\lambda \;\,.\: 0\:(\underline{(1\:(\lambda \;\,.\:0))}\:0)\\
\mbox{level}   & \lambda \;\,.\: (\lambda \;\,.\: 1\:0\:(\lambda \;.\: 2\:(1\:2)))\:\underline{(0\:(\lambda \;.\:1))}
               & \leadsto_\beta
               & \lambda \;\,.\: \underline{(0\:(\lambda \;.\:1))}\:0\:(\lambda \;\,.\: 1\:(\underline{(0\:(\lambda \;\,.\:2))}\:1)\\
\end{array}\]
Underlining shows the movement of the substituted term. In the \emph{index} representation,
the free $x$ must be shifted when it goes under the $\lambda z$. With \emph{levels},
the free $x$ stays $0$, but the bound $v$ must be shifted under $\lambda z$,
and the substitution context must be shifted to account for the eliminated $\lambda y$.
Shift happens.

The objective of this paper is not to eliminate shifts altogether, but to ensure that they
do not require traversal. The approach is to track exactly which variables are \emph{relevant}
at all nodes in the tree and aggressively expel those unused in any given subtree. As we do
so, we need and obtain much richer accountancy of variable usage, with much more intricate
invariants. Category theory guides the design of these invariants and Agda's dependent
types~\cite{DBLP:conf/afp/Norell08} drive their correct implementation.

\newcommand\bs{\char`\\}
My explorations follow Sato, Pollack, Schwichtenberg and
Sakurai, whose $\lambda$-terms make
binding sites carry \emph{maps} of use sites~\cite{spss:lambda.maps}. E.g.,
the |combK| and |combS| combinators become (respectively)
\[\begin{array}{r@@{\qquad}r@@{\:}r@@{\:}l@@{\qquad}r@@{\:}r@@{\:}r@@{\:}c@@{\:}c}
\mbox{names} & \lambda c.&\lambda e.&c & \lambda f.&\lambda s.&\lambda e.&(f\:e)&(s\:e)\\
\mbox{maps} & \texttt{1\bs}&\texttt{0\bs}&\square & \texttt{((10) (00))\bs}&\texttt{((00) (10))\bs}&\texttt{((01) (01))\bs}&(\square\:\square)&(\square\:\square)\\
\end{array}\]
where each abstraction shows with $\texttt{1}$s where in the subsequent tree of applications
its variable occurs: leaves, $\square$, are relieved of choice.
Of course, the tree under each binder determines which maps are well formed
in a highly nonlocal way: these invariants are formalised \emph{extrinsically} both in
Isabelle/HOL and in Minlog, over a context-free datatype enforcing neither scope nor shape.

In this paper, we shall obtain an \emph{intrinsically} valid
representation, where the map information is localized. Binding sites
tell only if the variable is used; the crucial choice points where a
term comprises more than one subterm say which variables go where. Not
all are used in all subterms, but (as Eccles says to Seagoon) \emph{everybody's got to be somewhere}~\cite{eccles}:
variables used nowhere have been discarded already.
This property is delivered by a coproduct construction in the slices of the category
of order-preserving embeddings, but fear not: we shall revisit all of the category
theory required to develop the definition, especially as it strays beyond the
familiar (e.g., to Haskellers) territory of types-and-functions.

Intrinsically well scoped de Bruijn terms date back to Bellegarde and
Hook~\cite{bellegarde.hook:substitution.monad}, using {\tt option} types to grow
a type of free variables, but hampered by lack of
polymorphic recursion in ML. Substitution (i.e., \emph{monadic} structure)
was developed for untyped terms by Bird and Paterson~\cite{bird.paterson:debruijn.nested}
and for simple types by Altenkirch and Reus~\cite{altenkirch.reus:monads.lambda}, both
dependent either on a \emph{prior} implementation of renumbering shifts (i.e., functorial
structure) or a non-structural recursion. My thesis~\cite{DBLP:phd/ethos/McBride00} follows McKinna
and Goguen~\cite{goguenmckinna} in restoring a single
structural operation abstracting `action' on variables, instantiated to
renumbering then to substitution, an approach subsequently adopted by Benton, Kennedy and
Hur~\cite{DBLP:journals/jar/BentonHKM12} and generalised to semantic actions by Allais et al.~\cite{DBLP:conf/cpp/Allais0MM17}.
Here, we go directly to substitution: \emph{shifts need no traversal}.

I present not only $\lambda$-calculus but a \emph{universe} of syntaxes inspired
by Harper, Honsell and Plotkin's
Logical Framework~\cite{DBLP:journals/jacm/HarperHP93}. I lift the \emph{sorts} of a syntax to higher
\emph{kinds}, acquiring both binding (via subterms at higher kind) and
\emph{meta}variables (at higher kind). However,
substituting a higher-kinded variable demands substitution of its parameters
\emph{hereditarily}~\cite{DBLP:conf/types/WatkinsCPW03} and \emph{simultaneously}. Thereby hangs a tale.
Abel showed how \emph{sized types} justify this process's apparently non-structural
recursion in MSFP 2006~\cite{DBLP:conf/mpc/000106}. As editor, I anonymised a discussion with a referee
which yielded a structural recursion for hereditary substitution of a \emph{single} variable,
instigating Keller and Altenkirch's formalization at MSFP
2010~\cite{DBLP:conf/icfp/KellerA10}. Here, at last, simultaneous hereditary substitution
becomes structurally recursive.




\section{Basic Equipment in Agda}

%format Set = "\D{Set}"
%format Zero = "\D{Zero}"
%format One = "\D{One}"
%format Two = "\D{Two}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
%format Tt = "\F{T\!t}"
%format <> = "\C{\langle\rangle}"
%format Sg = "\D{\Upsigma}"
%format * = "\F{\times}"
%format _*_ = _ * _
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format , = "\C{,}"
%format _,_ = _ , _
%format ! = "\C{!}"
%format !_ = ! _
We shall need finite types |Zero|, |One|, and |Two|, named for their cardinality,
and the reflection of |Two| as a set of evidence for `being |tt|'.
Dependent pairing is by means of the |Sg| type, abbreviated by |*| when non-dependent.
The \emph{pattern synonym} |!_| allows the first component to be determined by
the second: making it a right-associative prefix operator lets us write |! ! expression|
rather than |! (! (expression))|.
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.7in}{
\begin{code}
data    Zero  : Set where
record  One   : Set where constructor <>
data    Two   : Set where tt ff : Two

Tt : Two -> Set
Tt tt  = One
Tt ff  = Zero
\end{code}}
\parbox[t]{3in}{
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field fst : S; snd : T fst
  
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
pattern !_ t = _ , t
\end{code}}
%if False
\begin{code}
infixr 4 !_ _,_ _*_
open Sg
\end{code}
%endif

We shall also need to reason equationally. For all its imperfections in matters of
\emph{extensionality}, it will be convenient to define equality inductively, enabling the |rewrite| construct
in equational proofs.
%format == = "\D{=\!\!=}"
%format _==_ = _ == _
%format refl = "\C{refl}"
\begin{code}
data _==_ {X : Set}(x : X) : X -> Set where refl : x == x
\end{code}
%if False
\begin{code}
{-# BUILTIN EQUALITY _==_ #-}
infixr 6 _==_
\end{code}
%endif


\section{$\OPE_{|K|}$: The (Simplicial) Category of Order-Preserving Embeddings}

No category theorist would mistake me for one of their own. However, the key technology
in this paper can be helpfully conceptualised categorically. Category theory is just the
study of compositionality --- for everything, not just sets-and-functions. Here, we have an
opportunity to develop categorical structure away from the usual apparatus for
programming with functions. Let us therefore revisit the basics.

\paragraph{Category (I): Objects and Morphisms.~} A \emph{category} is given by a class of \emph{objects} and a family
of \emph{morphisms} (or \emph{arrows}) indexed by two objects: \emph{source} and
\emph{target}. Abstractly, we may write $\mathbb{C}$ for a given
category, $||\mathbb{C}||$ for its objects, and
$\mathbb{C}(S,T)$ for its morphisms with given source and target,
$S,T\in||\mathbb{C}||$.

The rest will follow, but let
us fix these notions for our example category, $\OPE_{|K|}$, of
\emph{order-preserving embeddings} between variable scopes, which I
learned about from Altenkirch, Hofmann and Streicher~\cite{DBLP:conf/ctcs/AltenkirchHS95}.
Objects are \emph{scopes}, given as backward (or `snoc') lists of the \emph{kinds}, |K|, of
variables. (I habitually suppress the |K| and just write
$\OPE$ for the category.)
Backward lists respect the tradition of writing contexts
left of judgements in rules and extending them on the
right. However, I write `scope' rather than `context' as
we track at least which variables we may refer to, but perhaps
not all contextual data.
%
%format where = "\mathkw{where}"
%format Bwd = "\D{Bwd}"
%format B0 = "\C{[]}"
%format - = "\C{\mbox{{}-}\!,}"
%format _-_ = _ - _
\newcommand{\apo}{\mbox{'}}
%format <= = "\D{\le}"
%format _<= = _ <=
%format _<=_ = _ <= _
%format oz = "\C{oz}"
%format os = "\C{os}"
%format o' = "\C{o\apo}"
%format _o' = _ o'
%format _os = _ os
%
\vspace*{ -0.2in} \\
\parbox[t]{2.5in}{
\begin{code}
data Bwd (K : Set) : Set where
  _-_  : Bwd K -> K -> Bwd K
  B0   : Bwd K
\end{code}}
%if False
\begin{code}
infixl 7 _-_
\end{code}
%endif
\parbox[t]{3in}{
\begin{spec}
data _<=_ : Bwd K -> Bwd K -> Set where
  _o'  : iz <= jz ->     iz          <=  (jz  -   k)
  _os  : iz <= jz ->  (  iz  -   k)  <=  (jz  -   k)
  oz   :                     B0      <=       B0
\end{spec}}

The morphisms, |iz <= jz|, of $\OPE$ give an embedding from a source
to a target scope. Colloquially, we may call them
`thinnings', as they dilute the variables of the source scope with
more.  Dually, we may see such a morphism as
expelling variables from the target scope, leaving a particular
selection as the source.  I write the step constructors postfix,
so thinnings (like scopes) grow on the right. When |K = One|,
|Bwd K| represents natural numbers and |<=| generates Pascal's
Triangle; if, further, the empty scope is excluded, we obtain
the \emph{simplex} category, beloved of topologists.

%if False
\begin{code}
data _<=_ {K} : Bwd K -> Bwd K -> Set where
  _o'  : forall {iz jz k} ->  iz <= jz ->     iz          <=  (jz  -   k)
  _os  : forall {iz jz k} ->  iz <= jz ->  (  iz  -   k)  <=  (jz  -   k)
  oz   :                                          B0      <=       B0
\end{code}
\begin{code}
infixl 8 _o' _os
\end{code}
%endif

Now, where I give myself away as a type theorist is that I do not
consider the notion of `morphism' to make sense without prior source and
target objects. The type |iz <= jz| (which is a little more mnemonic than
$\OPE(|iz|,|jz|)$) is the type of `thinnings from |iz| to
|jz|': there is no type of `thinnings' \emph{per se}.
%if False
By making types explicit about source
and target objects, we can use the type system to ensure that thinnings
fit together properly. Programs, on the other hand, will often leave these
details to the typechecker. None the less, we can recover them whenever we
choose.
%format src = "\F{src}"
%format trg = "\F{trg}"
\begin{code}
src trg : forall {K}{iz jz : Bwd K} -> iz <= jz -> Bwd K
src {iz = iz} th = iz
trg {jz = jz} th = jz
\end{code}
%endif

Let us have an example thinning: here, we embed a scope with three variables
into a scope with five.
\[\begin{array}{r@@{\!\!}c@@{\!\!}lll}
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| & \quad\quad\quad\quad\quad|os| & |: B0 - k0 - k2 - k4 <= B0 - k0 - k1 - k2 - k3 - k4| \\
             &                  & \circ\;|k3| & \quad\quad\quad\quad|o'|\\
|k2|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k2| & \quad\quad\quad|os| \\
             &                  & \circ\;|k1| & \quad\quad|o'|\\
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|& \quad|os|\\
&&& |oz|
\end{array}\]

%format oi = "\F{oi}"
%format <&= = "\F{\fatsemi}"
%format _<&=_ = _ <&= _
%format th = "\V{\theta}"
%format ph = "\V{\phi}"
%format ps = "\V{\psi}"
%format th' = "\V{\theta^\prime}"
%format ph' = "\V{\phi^\prime}"
%format ps' = "\V{\psi^\prime}"
\paragraph{Category (II): Identity and Composition.~} In any category, certain morphisms
must exist. Each object $X\in||\mathbb{C}||$
has an \emph{identity} $\iota_X\in\mathbb{C}(X,X)$, and wherever the
target of one morphism meets the source of another, their \emph{composite}
makes a direct path:
if $f\in\mathbb{C}(R,S)$ and $g\in\mathbb{C}(S,T)$, then $(f;g)\in\mathbb{C}(R,T)$.

For example, every scope has the identity thinning, |oi|, and thinnings compose via |<&=|.
(For functions, it is usual to write $g\cdot f$ for `$g$ \emph{after} $f$' than $f;g$ for
`$f$ \emph{then} $g$', but for thinnings I retain spatial
intuition.)
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.8in}{
\begin{spec}
oi :  kz <= kz
oi {kz = iz - k}  = oi os -- |os| preserves |oi|
oi {kz = B0}      = oz
\end{spec}}
\hfill
\parbox[t]{3in}{
\begin{spec}
_<&=_ :  iz <= jz -> jz <= kz -> iz <= kz
th     <&= ph o'  = (th <&= ph) o'
th o'  <&= ph os  = (th <&= ph) o'
th os  <&= ph os  = (th <&= ph) os -- |os| preserves |<&=|
oz     <&= oz     = oz
\end{spec}}
%if False
\begin{code}
oi :  forall {K}{kz : Bwd K} ->
      kz <= kz
oi {kz = iz - k}  = oi os -- |os| preserves |oi|
oi {kz = B0}      = oz

_<&=_ :  forall {K}{iz jz kz : Bwd K} ->
         iz <= jz -> jz <= kz -> iz <= kz
th     <&= ph o'  = (th <&= ph) o'
th o'  <&= ph os  = (th <&= ph) o'
th os  <&= ph os  = (th <&= ph) os -- |os| preserves |<&=|
oz     <&= oz     = oz
\end{code}
%endif

By way of example, let us plot specific uses of identity and composition.
\[\begin{array}{r@@{\!\!}c@@{\!\!}l@@{\qquad\qquad}||@@{\qquad\qquad}r@@{\!\!}c@@{\!\!}l@@{\qquad}r@@{\!\!}c@@{\!\!}l@@{\qquad\qquad}r@@{\!\!}c@@{\!\!}l}
&|oi|&& &|th|&& &|ph|&& &|th <&= ph|& \\
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| &
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| &
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| &
|k4|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k4| \\
|k3|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k3| &
&&&          &                  & \circ\;|k3|&         &                  & \circ\;|k3| \\
|k2|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k2| &
&& \circ\;|k2| &          
|k2|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k2| &&& \circ\;|k2| \\
|k1|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k1| &
&&&          &                  & \circ\;|k1|&          &                  & \circ\;|k1| \\
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0| &
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|&
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|&
|k0|\;\bullet & -\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!-\!\!\!- & \bullet\;|k0|\\
\end{array}\]

\paragraph{Category (III): Laws.~} To complete the definition of a
category, we must say which laws are satisfied by identity and
composition. Composition \emph{absorbs} identity on the left and on
the right. Moreover, composition is \emph{associative}, meaning that
any sequence of morphisms which fit together target-to-source can be
composed without the specific pairwise grouping choices making a
difference. That is, we have three laws which are presented as
\emph{equations}, at which point any type theorist will want to know
what is meant by `equal': I shall always be careful to say.
Our thinnings are first-order, so |==| will serve.
%if False
\begin{code}
infixr 7 _<&=_
infixr 6 _<=_
\end{code}
%endif
With this definition in place, we may then state the laws. I
omit the proofs, which go by functional induction.
%format law-oi<&= = "\F{law-}" oi <&=
%format law-<&=oi = "\F{law-}" <&= oi
%format law-<&=<&= = "\F{law-}" <&= <&=
\[
|law-oi<&= : oi <&= th == th| \qquad
|law-<&=oi : th <&= oi == th| \qquad
|law-<&=<&= : th <&= (ph <&= ps) == (th <&= ph) <&= ps|
\]
%if False
\begin{code}
law-oi<&=   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  oi <&= th == th
law-<&=oi   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  th <&= oi == th
law-<&=<&=  :  forall {K}{iz jz kz lz : Bwd K}  (th : iz <= jz)(ph : jz <= kz)(ps : kz <= lz) ->
                                                                    th <&= (ph <&= ps) == (th <&= ph) <&= ps
law-oi<&= oz = refl
law-oi<&= (th os) rewrite law-oi<&= th = refl
law-oi<&= (th o') rewrite law-oi<&= th = refl

law-<&=oi oz = refl
law-<&=oi (th os) rewrite law-<&=oi th = refl
law-<&=oi (th o') rewrite law-<&=oi th = refl

law-<&=<&= th ph (ps o') rewrite law-<&=<&= th ph ps = refl
law-<&=<&= th (ph o') (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= (th o') (ph os) (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= (th os) (ph os) (ps os) rewrite law-<&=<&= th ph ps = refl
law-<&=<&= oz oz oz = refl
\end{code}
%endif

As one might expect, order-preserving embeddings have a strong
antisymmetry property that one cannot expect of categories in general.
The \emph{only} invertible arrows are the identities.
Note that we must match on the proof of |iz == jz| even to claim
that |th| and |ph| are the identity.
%format antisym = "\F{antisym}"
\begin{spec}
antisym :  (th : iz <= jz)(ph : jz <= iz) -> Sg (iz == jz) \ { refl -> th == oi * ph == oi }
\end{spec}
%if False
\begin{code}
antisym :  forall {K}{iz jz : Bwd K}(th : iz <= jz)(ph : jz <= iz) ->
           Sg (iz == jz) \ { refl -> th == oi * ph == oi }
antisym oz oz = refl , refl , refl
antisym (th os) (ph os) with antisym th ph
antisym (.oi os) (.oi os) | refl , refl , refl = refl , refl , refl
antisym (th os) (ph o') with antisym (th o') ph
antisym (th os) (ph o') | refl , () , c
antisym (th o') (ph os) with antisym th (ph o')
antisym (th o') (ph os) | refl , b , ()
antisym (th o') (ph o') with antisym (oi o' <&= th) (oi o' <&= ph)
antisym (th os o') (ph o') | refl , () , c
antisym (th o' o') (ph o') | refl , () , c
\end{code}
%endif


\paragraph{Example: de Bruijn Syntax via $\OPE_{|One|}$.}~
%
%format (Cix (k)) = "\F{\overline{\black{" k "}}}"
%format Cix_ = "\F{\overline{\black{\_}}}"
%format Set1 = Set "_1"
%format <- = "\F{\leftarrow}"
%format _<-_ = _ <- _
%format <> = "\C{\langle\rangle}"
%format LamTm = "\D{Lam}"
%format var = "\C{\scriptstyle\#}"
%format $ = "\C{\scriptstyle\$}"
%format _$_ = _ $ _
%format lam = "\C{\uplambda}"
%format ^L = "\F{\uparrow}"
%format _^L_ = _ ^L _
De Bruijn indices are numbers~\cite{deBruijn:dummies}, perhaps
with some bound enforced by type~\cite{bellegarde.hook:substitution.monad,bird.paterson:debruijn.nested,altenkirch.reus:monads.lambda}.
We can use singleton thinning, |k <- kz = B0 - k <= kz|,
%if False
\begin{code}
Cix_ : Set -> Set1
Cix K = Bwd K -> Set

_<-_ : forall {K} -> K -> (Cix K)
\end{code}
\begin{code}
k <- kz = B0 - k <= kz
\end{code}
%endif
to give
de Bruijn $\lambda$-terms, readily admitting thinning:
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{3.5in}{
\begin{spec}
data LamTm (iz : Bwd One) : Set where
  var  : (x : <> <- iz)  ->         LamTm iz
  _$_  : (f s : LamTm iz) ->        LamTm iz
  lam  : (t : LamTm (iz - <>)) ->   LamTm iz
\end{spec}}
\parbox[t]{2.5in}{
\begin{spec}
_^L_ : LamTm iz -> iz <= jz -> LamTm jz
var i    ^L th = var (i <&= th)
(f $ s)  ^L th = (f ^L th) $ (s ^L th)
lam t    ^L th = lam (t ^L th os)
\end{spec}}
%if False
\begin{code}
data LamTm (iz : Bwd One) : Set where          -- |LamTm : (Cix One)|
  var  : (x : <> <- iz)  ->         LamTm iz   -- \emph{finds} a variable
  _$_  : (f s : LamTm iz) ->        LamTm iz   -- associates left
  lam  : (t : LamTm (iz - <>)) ->   LamTm iz   -- \emph{binds} a variable
infixl 5 _$_
\end{code}
%endif

Variables are represented by pointing, eliminating redundant choice of names,
but it is only when we point to one variable that we exclude
the others. Thus de Bruijn indexing
effectively uses thinnings to discard unwanted variables as
\emph{late} as possible, in the \emph{leaves} of syntax trees.

Note how the scope index |iz| is the
target of a thinning in |var| and weakened in |lam|.
Hence, thinnings act on terms ultimately
by postcomposition, but because terms keep their thinnings at their leaves,
we must hunt the entire tree to find them.
Now consider the other canonical placement of
thinnings, nearest the \emph{root}, discarding unused variables
as \emph{early} as possible.
%if False
\begin{code}
_^L_ : forall {iz jz} -> LamTm iz -> iz <= jz -> LamTm jz
var i    ^L th = var (i <&= th)
(f $ s)  ^L th = (f ^L th) $ (s ^L th)
lam t    ^L th = lam (t ^L th os)
infixl 7 _^L_
\end{code}
%endif


\section{Slices of Thinnings}

If we fix the target of thinnings, |(_<= kz)|, we obtain the notion of
\emph{subscopes} of a given |kz|. Fixing a target is a standard way
to construct a new category whose objects are given by
morphisms of the original.
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{4in}{
\paragraph{Slice Category.~} If
$\mathbb{C}$ is a category and $I$ one of its objects, the \emph{slice category}
$\mathbb{C}/I$ has as its objects pairs $(S, f)$, where $S$ is an object
of $\mathbb{C}$ and $f : S \to I$ is a morphism in $\mathbb{C}$. A morphism
in $(S, f) \to (T, g)$ is some $h : S \to T$ such that $f = h;g$.
(The dotted regions in the diagram show the objects in the slice.)
}
\parbox[t]{2in}{
\[\xymatrix{
  S \ar[rr]^h \ar[dr]_f &   & T \ar[dl]^g \\
    & I \ar@@{.}@@(ul,dl)[ul]\ar@@{.}@@(ul,ur)[ul]
        \ar@@{.}@@(ur,dr)[ur]\ar@@{.}@@(ur,ul)[ur]
        &
}\]}

~

That is, the morphisms are \emph{triangles}. A seasoned dependently typed
programmer will be nervous at a definition like the following
(where the |_| after |Sg| asks Agda to compute the type |iz <= jz| of |th|):
%format ->/ = "\F{\to_{\slash}}"
%format _->/_ = _ ->/ _
\begin{spec}
ps ->/ ph = Sg _ \ th -> (th <&= ph) == ps  -- beware of |<&=|!
\end{spec}
because the equation restricts us when it comes to manipulating
triangles. Dependent pattern matching relies on \emph{unification} of
indices, but defined function symbols like |<&=| make unification
difficult, obliging us to reason about the \emph{edges} of the triangles.
It helps at this point to define the \emph{graph} of |<&=| inductively.
%format Tri = "\D{Tri}"
%format t-'' = "\C{t\mbox{{}-}\apo\!\apo}"
%format t's' = "\C{t\apo\!s\apo}"
%format tsss = "\C{tsss}"
%format _t-'' = _ t-''
%format _t's' = _ t's'
%format _tsss = _ tsss
%format tzzz = "\C{tzzz}"
%format tri = "\F{tri}"
%format comp = "\F{comp}"
\vspace*{ -0.2in}\\
\parbox[t]{3.6in}{
\begin{spec}
data Tri : iz <= jz -> jz <= kz -> iz <= kz -> Set where
  _t-''  : Tri th ph ps ->  Tri    th       (ph o')   (ps  o')
  _t's'  : Tri th ph ps ->  Tri (  th  o')  (ph  os)  (ps  o')
  _tsss  : Tri th ph ps ->  Tri (  th  os)  (ph  os)  (ps  os)
  tzzz   :                  Tri        oz        oz        oz
\end{spec}}
\parbox[t]{2.2in}{
\begin{spec}
tri   :  (th : iz <= jz)(ph : jz <= kz) ->
         Tri th ph (th <&= ph)
         
comp  :  Tri th ph ps -> ps == (th <&= ph)
\end{spec}}
%if False
\begin{code}
data Tri {K} : {iz jz kz : Bwd K} -> iz <= jz -> jz <= kz -> iz <= kz -> Set where
  _t-''  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k}    th      (ph o')  (ps o')
  _t's'  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k} (  th o')  (ph os)  (ps o')
  _tsss  : forall {iz jz kz k}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
             Tri th ph ps -> Tri {kz = _ - k} (  th os)  (ph os)  (ps os)
  tzzz   : Tri oz oz oz
infixl 8 _t-'' _t's' _tsss
\end{code}
%endif

\noindent
The indexing is entirely in constructor form, which will allow
easy unification. Moreover, all the \emph{data} in a |Tri| structure
comes from its \emph{indices}.
Easy inductions show that |Tri| is precisely the graph of |<&=|.
%if False
\begin{code}
tri   :  forall {K}{iz jz kz : Bwd K}(th : iz <= jz)(ph : jz <= kz) -> Tri th ph (th <&= ph)
comp  :  forall {K}{iz jz kz : Bwd K}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
           Tri th ph ps -> ps == (th <&= ph)

tri    th       (ph  o')  = (tri th ph)  t-''
tri (  th  o')  (ph  os)  = (tri th ph)  t's'
tri (  th  os)  (ph  os)  = (tri th ph)  tsss
tri        oz        oz   =              tzzz

comp (t  t-'')  rewrite comp t  = refl
comp (t  t's')  rewrite comp t  = refl
comp (t  tsss)  rewrite comp t  = refl
comp     tzzz                   = refl
\end{code}
%endif

The example composition given above can be rendered a triangle, as follows:
%format egTri = "\F{egTri}"
\begin{spec}
egTri : Tri {kz = B0 - k0 - k1 - k2 - k3 - k4} (oz os o' os) (oz os o' os o' os) (oz os o' o' o' os)
egTri = tzzz tsss t-'' t's' t-'' tsss
\end{spec}
%if False
\begin{code}
egTri :  forall {K}{k0 k1 k2 k3 k4 : K} ->  Tri {kz = B0 - k0 - k1 - k2 - k3 - k4}
                                            (oz os o' os) (oz os o' os o' os) (oz os o' o' o' os)
egTri = tzzz tsss t-'' t's' t-'' tsss
\end{code}
%endif

Morphisms in the slice can now be triangles:~ |ps ->/ ph = Sg _ \ th -> Tri th ph ps|.
%if False
\begin{code}
_->/_ :  forall {K}{iz jz kz : Bwd K} -> (iz <= kz) -> (jz <= kz) -> Set
\end{code}
\begin{code}
ps ->/ ph = Sg _ \ th -> Tri th ph ps
\end{code}
%endif

%format triU = "\F{triU}"
A useful $\OPE$-specific property is that morphisms in $\OPE/|kz|$ are \emph{unique}.
It is easy to state this property in terms of triangles with common edges,
|triU : Tri th ph ps -> Tri th' ph ps -> th == th'|,
and then
prove it by induction on the triangles, not edges.
It is thus cheap to obtain \emph{universal properties} in the slices of
$\OPE$, asserting the existence of unique morphisms: uniqueness comes for free!
%if False
\begin{code}
triU :  forall {K}{iz jz kz : Bwd K}{th th' : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
        Tri th ph ps -> Tri th' ph ps -> th == th'
triU (t  t-'')  (t'  t-'')  rewrite triU t t'  = refl
triU (t  t's')  (t'  t's')  rewrite triU t t'  = refl
triU (t  tsss)  (t'  tsss)  rewrite triU t t'  = refl
triU     tzzz        tzzz                      = refl
\end{code}
%endif


\section{A Proliferation of Functors}

Haskell makes merry with \texttt{class Functor}
and its many subclasses: this scratches but the surface, giving only
\emph{endo}functors from types-and-functions to types-and-functions.
Once we adopt the general notion, functoriality sprouts everywhere, with
the same structures usefully functorial in many ways.

\newcommand{\Id}{\textbf{I}}
\paragraph{Functor.~} A \emph{functor} is a mapping from a source
category $\mathbb{C}$ to a target category $\mathbb{D}$ which
preserves categorical structure.  To specify a structure, we must give
a function $F_o : ||\mathbb{C}||\to||\mathbb{D}||$ from source objects
to target objects, together with a family of functions
$F_m : \mathbb{C}(S,T)\to \mathbb{D}(F_o(S),F_o(T))$. The preserved
structure amounts to identity and composition: we must have
that $F_m(\iota_X)=\iota_{F_o(X)}$ and that $F_m(f;g)=F_m(f);F_m(g)$.
Note that there is an identity functor $\Id$ (whose actions on objects
and morphisms are the identity) from $\mathbb{C}$ to itself
and that functors compose (componentwise).

E.g., every |k : K| induces a functor (\emph{weakening}) from $\OPE$ to itself
by scope extension, |(_ - k)| on objects and |os| on
morphisms. The very definitions of |oi| and |<&=| show that |os|
preserves |oi| and |<&=|.
%(I am sufficiently old-fashioned
%and pedantic to distinguish weakening --- adding new variables with
%most local scope --- from thinning --- adding new variables anywhere,
%but this is far from universal.)

To see more examples, we need more
categories. Let |Set|'s objects be types in
Agda's |Set| universe and $|Set|(S, T)$ exactly $S\to T$, with the usual identity and
composition. Morphism equality is \emph{pointwise}.
Exercises: make |Bwd : Set -> Set| a functor;
check $(|LamTm|,|^L|)$ is a functor from $\OPE$ to |Set|.

%format -:> = "\mathrel{\dot{\to}}"
%format _-:>_ = _ -:> _
Let us plough a different furrow, rich in dependent types, constructing
new categories by \emph{indexing}. If |I : Set|, we may then take |I -> Set| to be the
category whose objects are \emph{families} of objects in |Set|,
$|S|, |T| : |I -> Set|$ with morphisms (implicitly
indexed) families of functions:~ |S -:> T = forall {i} -> S i -> T i|.
%if False
\begin{code}
_-:>_ : {I : Set}(S T : I -> Set) -> Set
\end{code}
\begin{code}
S -:> T = forall {i} -> S i -> T i
\end{code}
%endif
%
Morphisms are equal if they map each index to pointwise equal functions.

We may define a functor from |K -> Set| to |Bwd K -> Set| as follows:
%
%format All = "\D{All}"
%format all = "\F{all}"
%if False
\begin{code}
data  All {K}     (P  : K      -> Set) : Bwd K  -> Set where
  B0   :                                      All P B0
  _-_  : forall {kz k} -> All P kz -> P k ->  All P (kz - k)

all  :   forall {K}{P Q : K -> Set} -> (P -:> Q) -> (All P -:> All Q)
all f B0        = B0
all f (pz - p)  = all f pz - f p
\end{code}
%endif
\vspace*{ -0.2in} \\
\parbox[t]{3.5in}{
\begin{spec}
data  All (P : K -> Set) : Bwd K -> Set where
  B0   :                     All P B0
  _-_  : All P kz -> P k ->  All P (kz - k)
\end{spec}}
\parbox[t]{2.3in}{
\begin{spec}
all : (P -:> Q) -> (All P -:> All Q)
all f B0        = B0
all f (pz - p)  = all f pz - f p
\end{spec}}

For a given |K|, |All| acts on objects, giving for each
|k| in a scope, some value in |P k|, thus giving us a notion of
\emph{environment}. The action on morphisms, |all|, lifts \emph{kind-respecting}
operations on values to \emph{scope-respecting} operations on
environments. Identity and composition are readily
preserved. In the sequel, it will be convenient to abbreviate
|Bwd K -> Set| as |(Cix K)|, for types indexed over scopes.

However, |All| gives more functorial structure.
Fixing |kz|, we obtain |\ P -> All P kz|, a functor
from |K -> Set| to |Set|, again with the instantiated |all| acting on
morphisms.
And still, there is more.

\newcommand{\op}[1]{{#1}^{\textrm{op}}}
\paragraph{Opposite Category.~} For a given category $\mathbb{C}$, its
\emph{opposite} category is denoted $\op{\mathbb{C}}$ and
defined thus:
\[
||\op{\mathbb{C}}|| = ||\mathbb{C}|| \qquad
\op{\mathbb{C}}(S,T) = \mathbb{C}(T,S) \qquad
\op{\iota}_X = \iota_X \qquad
f\op{;}g = g;f
\]
Note that a functor from $\op{\mathbb{C}}$ to $\mathbb{D}$ is sometimes
called a \emph{contravariant functor} from $\mathbb{C}$ to $\mathbb{D}$.
%Moreover, a functor from $\op{\mathbb{C}}$ to |Set| is sometimes called a
%\emph{presheaf} on $\mathbb{C}$. That is, |<?=| makes |All P| a presheaf on
%$\OPE$.

\noindent\parbox{3.5in}{\par
E.g., $\op{\OPE}(|jz|,|iz|) = |iz <= jz|$ views thinnings as
\emph{selections} of just |iz| from the |jz| on offer.
As shown, right, an environment for all the |jz| whittles down to
just the |iz|, making
|All P| a \emph{presheaf} on $\OPE$ --- a \emph{functor} from $\op\OPE$ to |Set|.}
%format <?= = "\F{\le\!?}"
%format _<?=_ = _ <?= _
%format <?=_ = <?= _
\parbox{2in}{\vspace*{ -0.1in}
\begin{spec}
_<?=_ : iz <= jz -> All P jz -> All P iz
oz       <?= B0        = B0
(th os)  <?= (pz - p)  = (th <?= pz) - p
(th o')  <?= (pz - p)  = th <?= pz
\end{spec}\vspace*{ -0.3in}}
%if False
\begin{code}
_<?=_ : forall {K P}{jz iz : Bwd K}  -> iz <= jz -> All P jz -> All P iz
oz       <?= B0        = B0
(th os)  <?= (pz - p)  = (th <?= pz) - p
(th o')  <?= (pz - p)  = th <?= pz
\end{code}
%endif
%It is not hard to check that the identity selection (selecting all
%elements) acts as the identity on environments, and that composition
%(making a subselection from a selection) is also respected.


\paragraph{Natural Transformation.~} Given functors $F$ and $G$ from
$\mathbb{C}$ to $\mathbb{D}$, a \emph{natural transformation} is a
family of $\mathbb{D}$-morphisms $k_X \in \mathbb{D}(F_o(X),G_o(X))$
indexed by $\mathbb{C}$-objects, $X\in||\mathbb{C}||$, satisfying the
\emph{naturality} condition, which is that for any $h\in\mathbb{C}(S,T)$, we have
$k_S;G_m(h) = F_m(h);k_T$,
amounting to a kind of \emph{uniformity}. It tells us that $k_X$
does not care what $X$ is, but only about the additional structure
imposed by $F$ and $G$.

Parametric polymorphism famously induces
naturality~\cite{Wadler:1989:TF:99370.99404}, in that ignorance of a
parameter imposes uniformity, and the same is true in our more nuanced
setting. We noted that |\ P -> All P kz| is a functor (with action |all|)
from |K -> Set| to |Set|. Accordingly, if |th : iz <= jz| then
|(th <?=_)|is a natural transformation from |\ P -> All P jz| to
|\ P -> All P iz|, which is as much as to say that the definition of
|<?=| is uniform in |P|, and hence that if |f : forall {k} -> P k -> Q k|, then
|all f (th <?= pz)| = |th <?= all f pz|.


Dependently typed programming thus offers us a richer seam of
categorical structure than we see in Haskell. This presents an opportunity
to make sense of the categorical taxonomy in terms of concrete
programming examples, and at the same time, organising those programs
and indicating \emph{what to prove}.

%if False
A simple consequence is that only the identity has the same source
and target.
%format law-oi = "\F{law-oi}"
\begin{code}
law-oi : forall {K}{kz : Bwd K}(th : kz <= kz) -> th == oi
law-oi th with antisym th th
law-oi .oi | refl , refl , refl = refl
\end{code}
%endif




\section{Things-with-Thinnings (a Monad)}

%format / = "\D{\Uparrow}"
%format /_ = / _
%format _/_ = _ / _
%format ^ = "\C{\uparrow}"
%format _^_ = _ ^ _
%format support = "\F{support}"
%format thing = "\F{thing}"
%format thinning = "\F{thinning}"
%format map/ = "\F{map\!\Uparrow}"
%format ; = ";\quad"

Let us develop the habit of packing terms with an
object in the slice category of thinnings,
selecting the
|support| of the term and discarding unused variables
at the root.
Note that |/| is a functor from |(Cix K)| to itself.
\begin{code}
record _/_ {K}(T : (Cix K))(scope : Bwd K) : Set where -- |(T /_) : (Cix K)|
  constructor _^_
  field {support} : Bwd K; thing : T support; thinning : support <= scope

map/ :  forall {K}{S T : (Cix K)} -> (S -:> T) -> ((S /_) -:> (T /_))
map/ f (s ^ th) = f s ^ th
\end{code}
%if False
\begin{code}
infixl 7 _^_
open _/_
\end{code}
%endif

In fact, the categorical structure of $\OPE$ makes |/| a \emph{monad}.
Let us recall the definition.

\paragraph{Monad.~} A functor $M$ from $\mathbb{C}$ to $\mathbb{C}$ gives
rise to a \emph{monad} $(M,\eta,\mu)$ if we can find a pair of natural
transformations, respectively `unit' (`add an $M$ layer') and `multiplication'
(`merge $M$ layers').
\[
\eta_X : \Id(X) \to M(X)
\qquad\qquad
\mu_X : M(M(X)) \to M(X)
\]
subject
to the conditions that merging an added layer yields the identity
(whether the layer added is `outer' or `inner'), and that
adjacent $M$ layers may be merged pairwise in any order.
\[
  \eta_{M(X)};\mu_X = \iota_{M(X)} \qquad\qquad
  M(\eta_X);\mu_X = \iota_{M(X)} \qquad\qquad
  \mu_{M(X)};\mu_X = M(\mu_X);\mu_X
\]

%format unit/ = "\F{unit\!\Uparrow}"
%format mult/ = "\F{mult\!\Uparrow}"
%format thin/ = "\F{thin\!\Uparrow}"
The categorical structure of thinnings makes |/| a monad. Here,
`adding a layer' amounts to `wrapping with a
thinning'. The proof obligations to make $(|/|,|unit/|,|mult/|)$ a monad are
exactly those required to make $\OPE$ a category in the first place.
In particular, things-with-thinnings are easy to thin further, indeed,
parametrically so. In other words, |(T /)| is uniformly a functor from
$\OPE$ to |Set|.
\\ \hspace*{-0.2in}
\parbox{1.5in}{
\begin{spec}
unit/ : T -:> (T /_)
unit/ t = t ^ oi
\end{spec}}
\parbox{2.3in}{
\begin{spec}
mult/ : ((T /_) /_) -:> (T /_)
mult/ ((t ^ th) ^ ph) = t ^ (th <&= ph)
\end{spec}}
\parbox{2.2in}{
\begin{spec}
thin/ : iz <= jz -> T / iz -> T / jz
thin/ th t = mult/ (t ^ th)
\end{spec}}
\\

%if False
\begin{code}
unit/ : forall {K}{T : (Cix K)} -> T -:> (T /_)
unit/ t = t ^ oi
mult/ : forall {K}{T : (Cix K)} -> ((T /_) /_) -:> (T /_)
mult/ ((t ^ th) ^ ph) = t ^ (th <&= ph)
thin/ : forall {K T}{iz jz : Bwd K} -> iz <= jz -> T / iz -> T / jz
thin/ th t = mult/ (t ^ th)
\end{code}
%endif

\newcommand{\Kleisli}[1]{\textbf{Kleisli}(#1)}
%\paragraph{Kleisli Category.~} Every monad $(M,\eta,\mu)$ on
%$\mathbb{C}$ induces a category $\Kleisli(M,\eta,\mu)$ with
%\[
%||\Kleisli{M,\eta,\mu}|| = ||\mathbb{C}|| \qquad
%\Kleisli{M,\eta,\mu}(S,T) = \mathbb{C}(S,M(T)) \qquad
%\iota^{\textbf{K}}_X = \eta_X \qquad
%f;^{\textbf{K}}g = f;M(g);\mu
%\]
%We sometimes call the morphisms in a Kleisli category \emph{Kleisli arrows}.
%
%The Kleisli arrows for |/| are operations with types such as |S -:> (T /_)|
%which \emph{discover dependency}: they turn an |S| over any scope |kz|
%into a |T| known to depend on at most some of the |kz|.

Shortly, we shall learn how to find the
variables on which a term syntactically depends. However,
merely \emph{allowing} a thinning at the root, |LamTm / iz|, yields a
redundant representation, as we may discard
variables at either root or leaves. Let us eliminate redundancy
by \emph{insisting} that a term's
|support| is \emph{relevant}: a variable retained by the
|thinning| \emph{must} be used in the |thing|. Everybody's got to be somewhere.


\section{The Curious Case of the Coproduct in  Slices of $\OPE$}

The |/| construction makes crucial use of objects
in the slice category $\OPE/|scope|$, which exhibit useful additional
structure: they are \emph{bit vectors},
with one bit per variable telling whether it has been selected.
Bit vectors inherit Boolean structure, via the
`Naperian' array structure of vectors~\cite{DBLP:conf/esop/Gibbons17}.

\paragraph{Initial object.~} A category $\mathbb{C}$ has initial object
$0$, if there is a unique morphism in $\mathbb{C}(0,X)$ for every $X$.

%format oe = "\F{oe}"
%format law-oe = "\F{law-}" oe
%format oe/ = oe "\F{\slash}"
The \emph{empty type} is famed for this r\^ole for
types-and-functions: empty case analysis gives
the vacuously unique morphism. In $\OPE$, the
empty \emph{scope} plays this r\^ole, with the
`constant 0' bit vector as unique morphism.
By return of post, we get $(|B0|,|oe|)$ as the initial object in the
slice category $\OPE/|kz|$. Hence, we can make \emph{constants} with empty support,
i.e., noting that no variable is ($\cdot_R$ for) \emph{relevant}.
%
\vspace*{ -0.2in} \\
\parbox[t]{2.9in}{
\begin{code}
oe : forall {K}{kz : Bwd K} -> B0 <= kz
oe {kz = iz - k}  = oe o'
oe {kz = B0}      = oz
\end{code}
\vspace*{ -0.4in}
\begin{spec}
law-oe :  (th : B0 <= kz) -> th == oe
\end{spec}}
\parbox[t]{2.8in}{
\begin{spec}
oe/ : (th : iz <= kz) -> oe ->/ th
oe/ th with tri oe th
... | t rewrite law-oe (oe <&= th) = oe , t
\end{spec}}
%if False
\begin{code}
law-oe :  forall {K}{kz : Bwd K}
          (th : B0 <= kz) -> th == oe
law-oe oz = refl
law-oe (th o') rewrite law-oe th = refl
\end{code}
\begin{code}
oe/ : forall {K}{iz kz : Bwd K}(th : iz <= kz) -> oe ->/ th
oe/ th with tri oe th
... | t rewrite law-oe (oe <&= th) = oe , t
\end{code}
%endif
%format OneR = One "_{R}"
%format <>R = "\F{\langle\rangle}_{R}"
\vspace*{ -0.2in} \\
\parbox[t]{2.9in}{
\begin{code}
data OneR {K} : (Cix K) where  <> : OneR B0
\end{code}}
\parbox[t]{2.8in}{
\begin{spec}
<>R : OneR / kz; <>R = <> ^ oe
\end{spec}}
%if False
\begin{code}
<>R : forall {K}{kz : Bwd K} -> OneR / kz; <>R = <> ^ oe
\end{code}
%endif

%In other words, we have found a \emph{terminal} object, namely
%|(OneR /_)|, in |Bwd K -> Set|.

%\paragraph{Terminal object.~} A category $\mathbb{C}$ has terminal object
%$1$, if there is a unique morphism in $\mathbb{C}(X,1)$ for every $X$.

%format *R = "\D{\times}_R"
%format _*R_ = _ *R _
%format ,R = "\F{,}_{R}"
%format _,R_ = _ ,R _
We should expect the constant to be the trivial case of some notion
of \emph{relevant pairing}, induced by \emph{coproducts} in the slice category.
If we have two objects in $\OPE/|kz|$ representing two subscopes, there should
be a smallest subscope which includes both: pairwise disjunction
of bit vectors.

\paragraph{Coproduct.~} Objects $S$ and $T$ of category $\mathbb{C}$ have
a coproduct object $S + T$ if there are morphisms $l\in \mathbb{C}(S, S + T)$ and
$r\in \mathbb{C}(T, S + T)$ such that every pair
$f\in \mathbb{C}(S, U)$ and $g\in \mathbb{C}(T, U)$ factors
through a unique $h\in \mathbb{C}(S + T, U)$ so that
$f = l;h$ and $g = r;h$. In |Set|, we may take $S + T$ to be
the \emph{disjoint union} of $S$ and $T$, with $l$ and $r$ its injections
and $h$ the \emph{case analysis} whose branches are $f$ and $g$.

However, we are not working in |Set|, but in a slice category.
Any category theorist will tell you that slice categories $\mathbb{C}/I$
inherit \emph{colimit} structure (characterized by universal out-arrows)
from $\mathbb{C}$, as indeed we just saw with the initial object. If $\OPE$
has coproducts, too, we are done!

Curiously, though, $\OPE$ does \emph{not} have coproducts. Taking |K = One|,
let us seek the coproduct of two singletons, $S = T = |B0 - <>|$.
Construct one diagram by taking $U = |B0 - <>|$ and $f = g = |oi|$,
ensuring that our only candidate for $S + T$ is again the
singleton |B0 - <>|, with $l = r = |oi|$, making $h = |oi|$.
Nothing else can sit between $S, T$ and $U$.
Now begin a different diagram, with $U' = |B0 - <> - <>|$,
allowing $f' = |oz os o'|$ and $g' = |oz o' os|$. No $h'$
post-composes $l$ and $r$ (both |oi|, making $h'$ itself)
to yield $f'$ and $g'$ respectively.

Fortunately, we get what we need: $\OPE$ may not have coproducts, but its
\emph{slices} do.
%It is not the case that colimit structure in $\mathbb{C}/I$
%arises \emph{only} via inheritance from $\mathbb{C}$.
%format Cover = "\D{Cover}"
%format c's = "\C{c\apo s}"
%format cs' = "\C{cs\apo}"
%format css = "\C{css}"
%format _c's = _ c's
%format _cs' = _ cs'
%format _css = _ css
%format czz = "\C{czz}"
Examine the data: two subscopes of some |kz|, |th : iz <= kz| and |ph : jz <= kz|. Their
coproduct must be some |ps : ijz <= kz|, where our $l$ and $r$ must be
triangles |Tri th' ps th| and |Tri ph' ps ph|, giving morphisms in
|th ->/ ps| and |ph ->/ ps|. Choose |ps|
to be pointwise disjunction of |th| and |ph|, minimizing |ijz|: |th'| and |ph'| will then \emph{cover} |ijz|.
\begin{spec}
data Cover {K}(ov : Two) : {iz jz ijz : Bwd K} -> iz <= ijz -> jz <= ijz -> Set where
  _c's  :                    Cover ov th ph ->  Cover ov (th  o')  (ph  os)
  _cs'  :                    Cover ov th ph ->  Cover ov (th  os)  (ph  o')
  _css  : {both : Tt ov} ->  Cover ov th ph ->  Cover ov (th  os)  (ph  os)
  czz   :                                       Cover ov      oz        oz
\end{spec}
The flag, |ov|,
determines whether \emph{overlap} is permitted:|tt| for
coproducts. |Cover ff| specifies \emph{partitions}.
No constructor allows both |th| and |ph| to
omit a target variable, so everybody's got to be somewhere.
%if False
\begin{code}
data Cover {K}(ov : Two) : {iz jz ijz : Bwd K} -> iz <= ijz -> jz <= ijz -> Set where
  _c's  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th o')  (ph os)
  _cs'  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th os)  (ph o')
  _css  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz}{both : Tt ov} ->
            Cover ov th ph -> Cover ov {ijz = _ - k}  (th os)  (ph os)
  czz   : Cover ov oz oz
infixl 8 _c's _cs' _css
\end{code}
%endif
Let us compute
the coproduct, |ps| then check that any other diagram for
some |ps'| yields a |ps ->/ ps'|.
%format cop = "\F{cop}"
%format copU = "\F{copU}"
\vspace*{ -0.2in} \\
%\noindent
\parbox{4in}{
\begin{spec}
cop   :  (th : iz <= kz)(ph : jz <= kz) ->
         Sg _ \ ijz -> Sg (ijz <= kz) \ ps ->
         Sg (iz <= ijz) \ th' -> Sg (jz <= ijz) \ ph' ->
         Tri th' ps th * Cover tt th' ph' * Tri ph' ps ph

copU  :  Tri th' ps th -> Cover tt th' ph' -> Tri ph' ps ph ->
         th ->/ ps' -> ph ->/ ps' -> ps ->/ ps'
\end{spec}}
\parbox{2in}{
\[\xymatrix{
 |iz| \ar[rrrd]^{|th|} \ar@@{.>}[rd]_{|th'|} &&& \\
 &  |ijz| \ar@@{.>}[rr]^{|ps|}  && |kz| \\ 
 |jz| \ar[rrru]_{|ph|} \ar@@{.>}[ru]^{|ph'|} &&& \\
}\]}
\vspace*{ -0.2in}
%if False
\begin{code}
cop   :  forall {K}{kz iz jz : Bwd K}
         (th : iz <= kz)(ph : jz <= kz) ->
         Sg _ \ ijz -> Sg (ijz <= kz) \ ps ->
         Sg (iz <= ijz) \ th' -> Sg (jz <= ijz) \ ph' ->
         Tri th' ps th * Cover tt th' ph' * Tri ph' ps ph
\end{code}
%endif
\newpage   %%%%%%%%% GRRRR
\begin{code}
cop (th  o') (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t-''  , c       , tr  t-''
cop (th  o') (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t's'  , c  c's  , tr  tsss
cop (th  os) (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  cs'  , tr  t's'
cop (th  os) (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  css  , tr  tsss
cop      oz       oz   =                                         ! ! ! !     tzzz  ,    czz  ,     tzzz
\end{code}
The |copU| proof goes by induction on the triangles which share |ps'|
and inversion of the coproduct.
%if False
\begin{code}
copU :  forall {K}{kz iz jz ijz : Bwd K}
        {th : iz <= kz}{ph : jz <= kz}{ps : ijz <= kz}{th' : iz <= ijz}{ph' : jz <= ijz}->
        Tri th' ps th -> Cover tt th' ph' -> Tri ph' ps ph ->
        forall {ijz'}{ps' : ijz' <= kz} -> th ->/ ps' -> ph ->/ ps' -> ps ->/ ps'
copU (tl t-'') c (tr t-'') (_ , ul t-'') (_ , ur t-'') with copU tl c tr (! ul) (! ur)
... | ! v = ! v t-''
copU (tl t's') () (tr t's') (! ul t-'') (! ur t-'')
copU (tl t-'') c (tr t-'') (! ul t's') (! ur t's') with copU tl c tr (! ul) (! ur)
... | ! v = ! v t's'
copU (tl t's') () (tr t's') (! ul t's') (! ur t's')
copU (tl t's') (c c's) (tr tsss) (! ul t's') (! ur tsss) with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU (tl tsss) (c cs') (tr t's') (! ul tsss) (! ur t's') with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU (tl tsss) (c css) (tr tsss) (! ul tsss) (! ur tsss) with copU tl c tr (! ul) (! ur)
... | ! v = ! v tsss
copU tzzz czz tzzz (_ , tzzz) (_ , tzzz) = ! tzzz
\end{code}
%endif
%
The payoff from the coproduct construction is the type of \emph{relevant pairs} ---
the co-de-Bruijn touchstone:
%format *R = "\D{\times}_R"
%format _*R_ = _ *R _
%format ,R = "\C{,}_R"
%format _,R_ = _ ,R _
%format pair = "\C{pair}"
%format outl = "\F{outl}"
%format outr = "\F{outr}"
%format cover = "\F{cover}"
\vspace*{ -0.2in} \\
\parbox[t]{3.4in}{
\begin{spec}
record _*R_ (S T : (Cix K))(ijz : Bwd K) : Set where
  constructor pair
  field  outl   : S / ijz; outr : T / ijz
         cover  : Cover tt (thinning outl) (thinning outr)
\end{spec}}
\parbox[t]{2in}{
\begin{spec}
_,R_ : S / kz -> T / kz -> (S *R T) / kz
(s ^ th) ,R (t ^ ph) =
  let  ! ps , th' , ph' , _ , c , _ = cop th ph
  in   pair (s ^ th') (t ^ ph') c ^ ps
\end{spec}}

%if False
\begin{code}
record _*R_ {K}(S T : (Cix K))(ijz : Bwd K) : Set where
  constructor pair
  field  outl : S / ijz ; outr   : T / ijz
         cover  : Cover tt (thinning outl) (thinning outr)

_,R_ : forall {K}{S T : (Cix K)}{kz} -> S / kz -> T / kz -> (S *R T) / kz
(s ^ th) ,R (t ^ ph) =
  let  ! ps , th' , ph' , _ , c , _ = cop th ph
  in   pair (s ^ th') (t ^ ph') c ^ ps
\end{code}
%endif

\section{Monoidal Structure of Order-Preserving Embeddings}

To talk about binding, we need scope extension.
We have seen single `snoc', but binding is simultaneous in general.
Concatenation induces monoidal structure on
objects of $\OPE$, extending to morphisms.
%format ++ = "\F{+\!\!+}"
%format _++_ = _ ++ _
%format <++= = ++ "_{" <= "}"
%format _<++=_ = _ <++= _
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.4in}{
\begin{spec}
_++_ : (iz jz : Bwd K) -> Bwd K
kz ++ B0        = kz
kz ++ (iz - j)  = (kz ++ iz) - j
\end{spec}}
%if False
\begin{code}
_++_ : forall {K}(kz jz : Bwd K) -> Bwd K
kz ++ B0        = kz
kz ++ (iz - j)  = (kz ++ iz) - j
infixl 7 _++_
_<++=_ :  forall {K}{iz jz iz' jz' : Bwd K} ->
  iz <= jz -> iz' <= jz' -> (iz ++ iz') <= (jz ++ jz')
th <++=      oz   =    th
th <++= (ph  os)  = (  th <++= ph) os
th <++= (ph  o')  = (  th <++= ph) o'
\end{code}
%endif
\parbox[t]{3in}{
\begin{spec}
_<++=_ :  iz <= jz -> iz' <= jz' -> (iz ++ iz') <= (jz ++ jz')
th <++=      oz   =    th
th <++= (ph  os)  = (  th <++= ph) os
th <++= (ph  o')  = (  th <++= ph) o'
\end{spec}}

Moreover, given a embedding into a concatenation, we can split it
into local and global parts.
%format -! = "\F{\dashv}"
%format _-!_ = _ -! _
\begin{spec}
_-!_ :  (jz : Bwd K)(ps : iz <= (kz ++ jz)) -> Sg (Bwd K) \ kz' -> Sg (Bwd K) \ jz' ->
  Sg (kz' <= kz) \ th -> Sg (jz' <= jz) \ ph -> Sg (iz == (kz' ++ jz')) \ { refl -> ps == (th <++= ph) }
B0        -! ps                                               = ! ! ps , oz , refl , refl
(kz - k)  -! (ps os)             with kz -! ps
(kz - k)  -! (.(th <++= ph) os)  | ! ! th , ph , refl , refl  = ! ! th , ph os , refl , refl
(kz - k)  -! (ps o')             with kz -! ps
(kz - k)  -! (.(th <++= ph) o')  | ! ! th , ph , refl , refl  = ! ! th , ph o' , refl , refl
\end{spec}
%if False
\begin{code}
_-!_ : forall {K}{iz kz}(jz : Bwd K)(ps : iz <= (kz ++ jz)) ->
       Sg _ \ kz' -> Sg _ \ jz' -> Sg (kz' <= kz) \ th -> Sg (jz' <= jz) \ ph ->
       Sg (iz == (kz' ++ jz')) \ { refl -> ps == (th <++= ph) }
B0        -! ps                                               = ! ! ps , oz , refl , refl
(kz - k)  -! (ps os)             with kz -! ps
(kz - k)  -! (.(th <++= ph) os)  | ! ! th , ph , refl , refl  = ! ! th , ph os , refl , refl
(kz - k)  -! (ps o')             with kz -! ps
(kz - k)  -! (.(th <++= ph) o')  | ! ! th , ph , refl , refl  = ! ! th , ph o' , refl , refl
\end{code}
%endif

Thus equipped, we can say how to bind some variables. The key is to say
at the binding site which of the bound variables will actually be used:
if they are not used, we should not even bring them into scope.

%format !- = "\D{\vdash}"
%format _!-_ = _ !- _
%format \\ = "\C{\fatbslash}"
%format _\\_ = _ \\ _
%format \\R = "\F{\fatbslash}_R"
%format _\\R_ = _ \\R _
\begin{code}
data _!-_ {K}(jz : Bwd K)(T : (Cix K))(kz : Bwd K) : Set where -- |jz !- T : (Cix K)|
  _\\_ : forall {iz} -> iz <= jz -> T (kz ++ iz) -> (jz !- T) kz

_\\R_ : forall {K T}{kz}(jz : Bwd K) -> T / (kz ++ jz) -> (jz !- T) / kz
jz \\R (t ^ ps) with jz -! ps
jz \\R (t ^ .(th <++= ph)) | ! ! th , ph , refl , refl = (ph \\ t) ^ th
\end{code}

%if False
\begin{code}
infixr 5 _!-_
infixr 6 _\\_
infixr 6 _\\R_
\end{code}
%endif

The monoid of scopes is generated from its singletons. By the time we \emph{use}
a variable, it should be the only thing in scope.
The associated smart constructor computes the thinned representation of variables.
%format VaR = "\D{Va}_R"
%format only = "\C{only}"
%format vaR = "\F{va}_R"
\vspace*{ -0.2in} \\
\parbox[t]{2.5in}{
\begin{spec}
data VaR (k : K) : (Cix K) where
  only : VaR k (B0 - k)
\end{spec}}
\parbox[t]{2.5in}{
\begin{spec}
vaR : k <- kz -> VaR k / kz
vaR x = only ^ x
\end{spec}}
%if False
\begin{code}
data VaR {K}(k : K) : (Cix K) where only : VaR k (B0 - k)

vaR : forall {K}{k}{kz : Bwd K} -> k <- kz -> VaR k / kz
vaR x = only ^ x
\end{code}
%endif

\vspace*{ -0.2in}
%format combK = "\F{\mathbb{K}}"
%format combS = "\F{\mathbb{S}}"
\paragraph{Untyped $\lambda$-calculus.~}
We can now give the $\lambda$-terms for which all \emph{free} variables are
relevant as follows.
Converting de Bruijn to co-de-Bruijn representation is easy with
smart constructors.
E.g., compare de Bruijn terms for the |combK| and |combS| combinators with their co-de-Bruijn form.
%format lamTmR = "\F{lam}_R"
%format LamTmR = LamTm "_R"
%format app = "\C{app}"
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.7in}{
\begin{code}
data LamTmR : (Cix One) where
  var  : VaR <>               -:>  LamTmR
  app  : (LamTmR *R LamTmR)   -:>  LamTmR
  lam  : (B0 - <> !- LamTmR)  -:>  LamTmR 
\end{code}}
\parbox[t]{3in}{
\begin{code}
lamTmR : LamTm -:> (LamTmR /_)
lamTmR (var x)  = map/ var  (vaR x)
lamTmR (f $ s)  = map/ app  (lamTmR f ,R lamTmR s)
lamTmR (lam t)  = map/ lam  (_ \\R lamTmR t) 
\end{code}}
\vspace*{ -0.2in}
\begin{spec}
combK         =  lam (lam (var (oe os o')))
lamTmR combK  =  lam (oz os \\ lam (oz o' \\ var only)) ^ oz

combS         =  lam (lam (lam (var (oe os o' o') $ var (oe os) $ (var (oe os o') $ var (oe os)))))
lamTmR combS  =  lam (oz os \\ lam (oz os \\ lam (oz os \\
  app (pair  (app  (pair (var only ^ oz os o') (var only ^ oz o' os) (czz cs' c's))  ^ oz os o' os)
             (app  (pair (var only ^ oz os o') (var only ^ oz o' os) (czz cs' c's))  ^ oz o' os os)
             (czz cs' c's css)) ))) ^ oz
\end{spec}
Stare bravely! |combK| returns a plainly constant function.
Meanwhile,
|combS| clearly uses all three inputs: the function goes
left, the argument goes right, and the environment is shared.


\section{A Universe of Metasyntaxes-with-Binding}

%format Kind = "\D{Kind}"
%format Scope = "\F{Scope}"
%format => = "\C{\Rightarrow}"
%format _=>_ = _ => _
%format scope = "\F{scope}"
%format sort = "\F{sort}"
There is nothing specific to the $\lambda$-calculus about de Bruijn
representation or its co-de-Bruijn counterpart. We may develop the
notions generically for multisorted syntaxes. If the sorts of our
syntax are drawn from set $I$, then we may characterize terms-with-binding
as inhabiting |Kind|s |kz => i|, which specify an extension of the scope
with new bindings |kz| and the sort |i| for the body of the binder.
\begin{code}
record Kind (I : Set) : Set where  inductive; constructor _=>_
                                   field scope : Bwd (Kind I); sort : I
\end{code}
%if False
\begin{code}
infix 6 _=>_
open Kind
\end{code}
%endif
|Kind|s offer higher-order abstraction: a bound variable itself
has a |Kind|, being an object sort parametrized by a scope,
where the latter is, as in previous  sections, a |Bwd| list, with |K| now
fixed as |Kind I|. Object variables have sorts; \emph{meta}-variables have |Kind|s.
E.g., in the $\beta$-rule, $t$ and $s$ are not object variables like $x$
\[
  (\lambda x.\,t[x])\:s \;\leadsto\; t[s]
\]
but
placeholders, $s$ for some term and $t[x]$ for some term
with a parameter which can be and is instantiated, by $x$
on the left and $s$ on the right. The kind of $t$ is |B0 - (B0 => <>) => <>|.

%format Desc = "\D{Desc}"
%format Set1 = Set "_1"
%format RecD = "\C{Rec}_D"
%format SgD = "\C{\Upsigma}_D"
%format OneD = "\C{One}_D"
%format *D = "\C{\times}_D"
%format _*D_ = _ *D _
%format Datoid = "\D{Datoid}"
%format Data = "\F{Data}"
%format decide = "\F{decide}"
%format Zero = "\D{Zero}"
%format Decide = "\D{Decide}"
%format yes = "\C{yes}"
%format no = "\C{no}"
We may give the syntax of each sort as a function mapping sorts to
|Desc|riptions
|D : I -> Desc I|.
\begin{spec}
data Desc (I : Set) : Set1 where
  RecD   : Kind I ->  Desc I;  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
  OneD   :            Desc I;  _*D_   : Desc I -> Desc I ->                    Desc I
  
\end{spec}
We may ask for a subterm with a given |Kind|, so it can bind
variables by listing their |Kind|s left of |=>|. Descriptions
are closed under unit and pairing.
We may also ask
for terms to be tagged by some sort of `constructor' inhabiting
some |Datoid|, i.e., a set with a decidable equality, given
as follows:
\vspace*{ -0.2in}\\
%\noindent
\parbox[t]{2.7in}{
\begin{code}
data Decide (X : Set) : Set where
  yes  : X ->            Decide X
  no   : (X -> Zero) ->  Decide X
\end{code}}
\parbox[t]{3in}{
\begin{code}
record Datoid : Set1 where
  field  Data    : Set
         decide  : (x y : Data) -> Decide (x == y)
\end{code}}
%if False
\begin{code}
open Datoid

data Desc (I : Set) : Set1 where
  RecD   : Kind I ->  Desc I ;  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
  OneD   :            Desc I ;  _*D_   : Desc I -> Desc I ->                    Desc I
\end{code}
%endif

\paragraph{Describing untyped $\lambda$-calculus.~} Define a tag enumeration, then a description.
%format LamTag = "\D{LamTag}"
%format LAMTAG = "\F{LAMTAG}"
%format LamD = "\F{Lam}_D"
\vspace*{ -0.2in} \\
\parbox[t]{3in}{
\begin{code}
data LamTag : Set where app lam : LamTag

LAMTAG : Datoid
Data    LAMTAG = LamTag
\end{code}}
\parbox[t]{2.5in}{
\begin{code}
decide  LAMTAG app  app  = yes refl
decide  LAMTAG app  lam  = no \ ()
decide  LAMTAG lam  app  = no \ ()
decide  LAMTAG lam  lam  = yes refl
\end{code}}
\vspace*{ -0.3in}
\begin{code}
LamD : One -> Desc One
LamD <> = SgD LAMTAG \  { app  -> RecD (B0 => <>) *D RecD (B0 => <>)
                        ; lam  -> RecD (B0 - (B0 => <>) => <>) }
\end{code}
Note that we do not and cannot include a tag or description for
the use sites of variables in terms: use of variables in scope
pertains not to the specific syntax, but to the general notion
of what it is to be a syntax.

%if False
\begin{code}
data Ty : Set where base : Ty ; _>>_ : Ty -> Ty -> Ty
infixr 4 _>>_
TY : Datoid
Data TY = Ty
decide TY base base = yes refl
decide TY base (_ >> _) = no \ ()
decide TY (_ >> _) base = no \ ()
decide TY (sx >> tx) (sy >> ty) with decide TY sx sy | decide TY tx ty
decide TY (sx >> tx) (.sx >> .tx) | yes refl | yes refl = yes refl
decide TY (sx >> tx) (sy >> ty) | yes _ | no p = no \ { refl -> p refl }
decide TY (sx >> tx) (sy >> ty) | no p | _ = no \ { refl -> p refl }

data TyLTag : Ty -> Set where
  app : forall {T} -> TyLTag T
  lam : forall {S T} -> TyLTag (S >> T)

TYLTAG : Ty -> Datoid
Data (TYLTAG T) = TyLTag T
decide (TYLTAG T) app app = yes refl
decide (TYLTAG .(_ >> _)) app lam = no \ ()
decide (TYLTAG .(_ >> _)) lam app = no \ ()
decide (TYLTAG .(_ >> _)) lam lam = yes refl

LTyD : Ty -> Desc Ty
LTyD T = SgD (TYLTAG T) \  { app -> SgD TY \ S -> RecD (B0 => (S >> T)) *D RecD (B0 => S)
                           ; (lam {S}{T}) -> RecD (B0 - (B0 => S) => T) }
\end{code}
%endif



\paragraph{Interpreting |Desc| as de Bruijn Syntax.~}
%format [! = "\F{\llbracket}"
%format !! = "\F{\mid}"
%format !] = "\F{\rrbracket}"
%format [!_!!_!] = [! _ !! _ !]
%format SpD = "\F{Sp}_D"
Let us give the de Bruijn interpretation of our syntax descriptions.
We give meaning to |Desc| in the traditional manner, interpreting
them as strictly positive operators in some |R| which gives the semantics
to |RecD|. In recursive positions, the scope grows by the bindings demanded by the given |Kind|.
At use sites, higher-kinded variables must be instantiated, just
like $t[x]$ in the $\beta$-rule example: |SpD| computes
the |Desc|ription of the
spine of actual parameters required.
\vspace*{ -0.2in} \\
\parbox[t]{3.7in}{
\begin{code}
[!_!!_!] : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD k   !! R !] kz = R (sort k) (kz ++ scope k)
[! SgD S T  !! R !] kz = Sg (Data S) \ s -> [! T s !! R !] kz
[! OneD     !! R !] kz = One
[! S *D T   !! R !] kz = [! S !! R !] kz * [! T !! R !] kz
\end{code}}
\parbox[t]{2in}{
\begin{spec}
SpD : Bwd (Kind I) -> Desc I
SpD      B0      =          OneD
SpD (kz  -   k)  = SpD kz   *D    RecD k
\end{spec}}
%Note that we work with scope-indexed sets and an index |kz| giving the
%kinds of the variables in scope. 

%if False
\begin{code}
SpD : forall {I} -> Bwd (Kind I) -> Desc I
SpD      B0      =          OneD
SpD (kz  -   k)  = SpD kz   *D    RecD k
\end{code}
%endif

Tying the knot, we find that a term is either a variable instantiated
with its spine of actual parameters, or it is a construct of the syntax
for the demanded sort, with subterms in recursive positions.
%format Tm = "\D{Tm}"
%format #$ = "\C{\scriptstyle \#\$}"
%format _#$_ = _ #$ _
%format [ = "\C{[}"
%format ] = "\C{]}"
%format [_] = [ _ ]
\begin{code}
data Tm {I}(D : I -> Desc I)(i : I) kz : Set where -- |Tm D i : (Cix (Kind I))|
  _#$_  : forall {jz} -> (jz => i) <- kz ->  [! SpD jz  !! Tm D !] kz ->  Tm D i kz
  [_]   :                                    [! D i     !! Tm D !] kz ->  Tm D i kz
\end{code}
%if False
\begin{code}
infixr 5 _#$_
\end{code}
%endif

%if False
In this setting, |combK| and |combS| become
%format combKD = combK "_D"
%format combSD = combS "_D"
\begin{spec}
combKD combSD : Tm LamD <> B0
combKD  =  [ lam ,  [ lam , oe os o' #$ <> ] ]
combSD  =  [ lam ,  [ lam ,  [ lam ,  [ app  , [ app , oe os o' o' #$ <> , oe os #$ <> ]
                                             , [ app , oe os o' #$ <> , oe os #$ <> ]
           ]        ]        ]        ]
\end{spec}
%endif

\vspace*{ -0.2in}
%format code = "\F{code}"
%format codes = "\F{codes}"
\paragraph{Interpreting |Desc| as co-de-Bruijn Syntax.~}
Now let us interpret |Desc|riptions in co-de-Bruijn style,
enforcing that all variables in scope are relevant, and that
binding sites expose vacuity.
%format !]R = "\F{\rrbracket}_R"
%format [!_!!_!]R = [! _ !! _ !]R
%format TmR = Tm "_R"
%format # = "\C{\scriptstyle \#}"
\begin{code}
[!_!!_!]R : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD k   !! R !]R = scope k !- R (sort k)
[! SgD S T  !! R !]R = \ kz -> Sg (Data S) \ s -> [! T s !! R !]R kz
[! OneD     !! R !]R = OneR
[! S *D T   !! R !]R = [! S !! R !]R *R [! T !! R !]R

data TmR {I}(D : I -> Desc I)(i : I) : (Cix (Kind I)) where
  #     : forall {jz} -> (VaR (jz => i) *R  [! SpD jz  !! TmR D !]R)  -:>  TmR D i
  [_]   :                                   [! D i     !! TmR D !]R   -:>  TmR D i
\end{code}

We can compute co-de-Bruijn terms from de Bruijn terms, generically.
\begin{code}
code   : forall {I}{D : I -> Desc I}{i}  ->  Tm D i           -:>  (TmR D i /_)
codes  : forall {I}{D : I -> Desc I} S   ->  [! S !! Tm D !]  -:>  ([! S !! TmR D !]R /_)
code                    (_#$_ {jz} x ts)  = map/ #    (vaR x ,R codes (SpD jz) ts)
code {D = D}{i = i}     [ ts ]            = map/ [_]  (codes (D i) ts)
codes (RecD k)          t                 = scope k \\R code t
codes (SgD S T)         (s , ts)          = map/ (s ,_) (codes (T s) ts)
codes OneD              <>                = <>R
codes (S *D T)          (ss , ts)         = codes S ss ,R codes T ts
\end{code}

%if False
\begin{code}
tyS : (A B C : Ty) -> Tm LTyD ((A >> B >> C) >> (A >> B) >> (A >> C)) B0
tyS A B C = [ lam , [ lam , [ lam , [ app , _ , [ app , _ , oz os o' o' #$ <> , oz o' o' os #$ <> ] , [ app , _ , oz o' os o' #$ <> , oz o' o' os #$ <> ] ] ] ] ]
\end{code}
%endif


\section{Hereditary Substitution for Co-de-Bruijn Metasyntax}

%format Im = "\F{Im}"
%format KB = "\F{KB}"
%format HSub = "\D{HSub}"
%format pass = "\F{pass}"
%format act = "\F{act}"
%format passive = "\F{passive}"
%format active = "\F{active}"
%format parti = "\F{parti}"
%format actBnd = "\F{actBnd}"
%format passTrg = "\F{passTrg}"
%format images = "\F{images}"

Let us develop the appropriate notion of substitution for our metasyntax, \emph{hereditary}
in the sense of Watkins et al.~\cite{DBLP:conf/types/WatkinsCPW03}. Substituting a higher-kinded
variable requires us further to substitute its parameters.

The construction of the type |HSub| of hereditary substitutions is subtle.
We may |parti|tion the source scope into |passive| variables, which embed into the target,
and |active| variables with an environment of |images| suited to their kinds.
The |HSub| type is indexed by a third scope, bounding the active kinds, by way of
ensuring \emph{termination} --- the oldest trick in my book~\cite{DBLP:journals/jfp/McBride03}.
\begin{code}
record HSub {I} D (src trg bnd : Bwd (Kind I)) : Set where
  field  pass act   : Bwd (Kind I);           passive  : pass  <= src;  active  : act <= src
         parti  : Cover ff passive active  ;  passTrg  : pass  <= trg;  actBnd  : act <= bnd
         images     : All (\ k -> (scope k !- TmR D (sort k)) / trg) act
\end{code}

%format ; = ";"
%if False
\begin{code}
open HSub
\end{code}
%endif

Before we see how to perform a substitution, let us think how to \emph{weaken} one: we
certainly push under binders, where some |ph : iz <= jz| says
which |iz| of the |jz| bound variables occur in the source term. Bound variables are not
substituted, so add them to the passive
side, keeping the active side bounded.
As with de Bruijn shifts, we must thin the images:
co-de-Bruijn representation lets us thin them
at the \emph{root}!
%format wkHSub = "\F{wkHSub}"
%format bindPassive = "\F{bindPassive}"
\begin{spec}
wkHSub :  HSub D src trg bnd -> iz <= jz -> HSub D (src ++ iz) (trg ++ jz) bnd
wkHSub {iz = iz}{jz = jz} h ph = record
  { parti = bindPassive iz ; actBnd = actBnd h ; passTrg = passTrg h <++= ph
  ; images = all (thin/ (oi <++= oe {kz = jz})) (images h) } where
  bindPassive : forall iz -> Cover ff (passive h <++= oi {kz = iz}) (active h <++= oe {kz = iz})
\end{spec}

%format selPart = "\F{selPart}"
%format selHSub = "\F{selHSub}"
%format ps0 = "\V{\psi_0}"
%format ps1 = "\V{\psi_1}"
A second handy function on |HSub|s whittles them down as
variables are expelled from scope by thinnings in relevant pairs.
We may select from an environment, but we must also refine the partition to cover just
those source variables which remain, hence the |selPart| operation, a
straightforward induction.
%if False
\begin{code}
wkHSub :  forall {I}{D : I -> Desc I}{src trg bnd iz jz} ->
          HSub D src trg bnd -> iz <= jz -> HSub D (src ++ iz) (trg ++ jz) bnd
wkHSub {iz = iz}{jz = jz} h ph = record
  { parti = bindPassive iz ; actBnd = actBnd h ; passTrg = passTrg h <++= ph
  ; images = all (thin/ (oi <++= oe {kz = jz})) (images h) } where
  bindPassive : forall iz -> Cover ff (passive h <++= oi {kz = iz}) (active h <++= oe {kz = iz})
  bindPassive B0       = parti h
  bindPassive (iz - _) = bindPassive iz cs'
\end{code}

\begin{code}
mutual
\end{code}
%endif
\begin{spec}
  selHSub :  src <= src' -> HSub D src' trg bnd -> HSub D src trg bnd
  selHSub ps (record { parti = c' ; actBnd = th' ; images = tz' ; passTrg = ph' }) =
    let ! ! ! ! ph , th , c = selPart ps c' in record
      { parti = c ; actBnd = th <&= th' ; images = th <?= tz' ; passTrg = ph <&= ph' }

  selPart :  (ps : kz <= kz') -> Cover ff th' ph' -> Sg _ \ iz -> Sg _ \ jz -> 
    Sg (iz <= kz) \ th -> Sg (jz <= kz) \ ph -> Sg (iz <= iz') \ ps0 -> Sg (jz <= jz') \ ps1 -> Cover ff th ph
\end{spec}
%if False
\begin{code}
  selHSub :  forall {I}{D : I -> Desc I}{src src' trg bnd} ->
             src <= src' -> HSub D src' trg bnd -> HSub D src trg bnd
  selHSub ps (record { parti = c' ; actBnd = th' ; images = tz' ; passTrg = ph' }) =
    let ! ! ! ! ph , th , c = selPart ps c' in record
      { parti = c ; actBnd = th <&= th' ; images = th <?= tz' ; passTrg = ph <&= ph' }

  selPart :  forall {K}{iz' jz' kz kz' : Bwd K}{th' : iz' <= kz'}{ph' : jz' <= kz'}
             (ps : kz <= kz') -> Cover ff th' ph' ->
             Sg _ \ iz -> Sg _ \ jz -> Sg (iz <= kz) \ th -> Sg (jz <= kz) \ ph ->
             Sg (iz <= iz') \ ps0 -> Sg (jz <= jz') \ ps1 -> Cover ff th ph

  selPart (ps o') (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0    , ps1 o' , c
  selPart (ps o') (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 o' , ps1 , c
  selPart (ps o') (c' css) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 o' , ps1 o' , c
  selPart (ps os) (c' c's) = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 , ps1 os , c c's
  selPart (ps os) (c' cs') = let ! ! ! ! ps0 , ps1 , c = selPart ps c' in ! ! ! ! ps0 os , ps1 , c cs'
  selPart (ps os) (_css {both = ()} _)
  selPart oz czz = ! ! ! ! oz , oz , czz
\end{code}
%endif

%format allLeft = "\F{allLeft}"
%if False
\begin{code}
allLeft : forall {K}{iz kz : Bwd K}{ov}{th : iz <= kz}{ph : B0 <= kz} -> Cover ov th ph -> iz == kz
allLeft (c cs') rewrite allLeft c = refl
allLeft czz = refl
\end{code}
%endif

%format hSub = "\F{hSub}"
%format hSubs = "\F{hSubs}"
%format hSubs/ = "\F{hSubs}_{\F{\slash}}"
%format hered = "\F{hered}"
%if False
\begin{code}
hSub    : forall {I D src trg bnd}{i : I} ->
  HSub D src trg bnd -> TmR D i src              -> TmR D i / trg
hSubs   : forall {I D src trg bnd}(S : Desc I) ->
  HSub D src trg bnd -> [! S !! TmR D !]R src    -> [! S !! TmR D !]R / trg
hSubs/  : forall {I D src trg bnd}(S : Desc I) ->
  HSub D src trg bnd -> [! S !! TmR D !]R / src  -> [! S !! TmR D !]R / trg
hered   : forall {I D jz trg bnd}{i : I} ->
  (jz !- TmR D i) / trg -> B0 - (jz => i) <= bnd -> [! SpD jz !! TmR D !]R / trg -> TmR D i / trg
\end{code}
%endif

The definition of hereditary substitution is a mutual recursion, terminating because the
active scope is always decreasing: |hSub| is the main operation on terms; |hSubs| and |hSubs/|
proceed structurally, in accordance with a syntax description; |hered| invokes |hSub| hereditarily.
\begin{spec}
hSub    :                  HSub D src trg bnd -> TmR D i src              -> TmR D i / trg
hSubs   : (S : Desc I) ->  HSub D src trg bnd -> [! S !! TmR D !]R src    -> [! S !! TmR D !]R / trg
hSubs/  : (S : Desc I) ->  HSub D src trg bnd -> [! S !! TmR D !]R / src  -> [! S !! TmR D !]R / trg
hered   : (jz !- TmR D i) / trg -> B0 - (jz => i) <= bnd -> [! SpD jz !! TmR D !]R / trg -> TmR D i / trg
\end{spec}
When |hSub| finds a variable, |selHSub| will reduce the |parti| to a single choice:
if the variable is passive, embed it in target scope and reattach its substituted spine;
if active, proceed |hered|itarily.
\begin{code}
hSub {D = D}{i = i} h [ ts ] = map/ [_] (hSubs (D i) h ts)
hSub h (# {jz} (pair (only ^ th) ts _)) with selHSub th h | hSubs/ (SpD jz) h ts
... | record { parti = _css {both = ()} _ }                         | ts'
... | record { parti = czz cs' ; passTrg = ph }                     | ts' = map/ # (vaR ph ,R ts')
... | record { parti = czz c's ; actBnd = th' ; images = B0 - im }  | ts' = hered im th' ts'
\end{code}

%format part = "\F{part}"
%format spAll = "\F{spAll}"
To substitute a variable |hered|itarily, find it in the bound: the scope of its
kind becomes the new, \emph{structurally smaller} bound. Helper function |part| partitions
passive free variables from active bound variables, while |spAll| converts the spine to an
environment of images.
\begin{code}
hered                     im                (th' o') ts' = hered im th' ts'
hered {D = D}{trg = trg}  ((ph \\ t) ^ ps)  (th' os) ts' = let ! ! c = part _ _ in 
  hSub (record { parti = c ; actBnd = ph ; images = ph <?= spAll ts' ; passTrg = ps }) t where
    spAll  :  forall {kz} -> [! SpD kz !! TmR D !]R / trg -> All _ kz
    part   :  forall kz iz -> Sg (kz <= (kz ++ iz)) \ th -> Sg (iz <= (kz ++ iz)) \ th' -> Cover ff th th'
\end{code}
%if False
\begin{code}
    spAll {B0}              _                    = B0
    spAll {kz - (jz => i)}  (pair ts' t _ ^ ps)  = spAll (thin/ ps ts') - thin/ ps t
    part kz (iz - _) = let ! ! c = part kz iz in ! ! c c's
    part (kz - _) B0 = let ! ! c = part kz B0 in ! ! c cs'
    part B0 B0 = ! ! czz
\end{code}
%endif

In the structural part of the algorithm, we may exploit our richer usage information
to stop as soon as the active variables have all left scope,
thinning the remaining passive variables with no further traversal. The lemma |allLeft| shows
that if the right of a partition is empty, the left must be full.
\begin{code}
hSubs (RecD k)   h (ph \\ t)     = scope k \\R hSub (wkHSub h ph) t
hSubs (SgD S T)  h (s , ts)      = map/ (s ,_) (hSubs (T s) h ts)
hSubs OneD       h <>            = <>R
hSubs (S *D T)   h (pair s t _)  = hSubs/ S h s ,R hSubs/ T h t 
hSubs/ S h' (ts ^ th) with selHSub th h'
hSubs/ S h' (ts ^ th) | record { parti = c ; images = B0 ; passTrg = ph } rewrite allLeft c = ts ^ ph
hSubs/ S h' (ts ^ th) | h = hSubs S h ts
\end{code}


\section{Discussion}

We have a universe of syntaxes with metavariables and binding, where the |Desc|ription of a
syntax is interpreted as the co-de-Bruijn terms, ensuring intrinsically that unused variables are
discarded not at the \emph{latest} opportunity (as in de Bruijn terms), nor at an \emph{arbitrary}
opportunity (as in one of Bird and Paterson's variants~\cite{bird.paterson:debruijn.nested}, or
with Hendriks and van Oostrom's `adbmal' operator~\cite{DBLP:conf/cade/HendriksO03}, both of
which reduce the labour of shifting at the cost of nontrivial $\alpha$-equivalence), but at the \emph{earliest}
opportunity. Hereditary substitution exploits usage information to stop when there is nothing to substitute,
shifts without traversal, and is, moreover, structurally recursive on the \emph{active scope}.

Recalling Atkey's Battlestar-Galactica-inspired quip about de Bruijn indices being a `Cylon detector',
co-de-Bruijn representation is even less suited to human comprehension, but its informative precision
makes it all the more useful for machines. Dependency checking is direct, so syntactic forms like
vacuous functions or $\eta$-redexes are easy to spot.

Co-de-Bruijn representation could lead to more efficient implementations of normalization and of
metavariable instantiation. The technique may be readily combined with representing terms as trees
whose top-level leaves are variable uses and top-level nodes are just those
(now easily detected) where paths to variables split: edges in the tree are \emph{closed}
one-hole contexts, jumped over in constant time~\cite{conor:tube}.

I see two high-level directions emerging from this work. Firstly, the generic treatment of
syntax with \emph{meta}variables opens the way to the generic treatment of \emph{metatheory}.
Even without moving from scope-safe to type-safe term representations, we can consider
the inductive relations we use to define notions such as reduction and type synthesis
as generated by descriptions for a universe, then seek to capture good properties
(e.g., stability under substitution, leading to type soundness) by construction. Co-de-Bruijn
representations make it easy to capture properties such as variable non-occurrence within the
syntax of the formulae used in rules, and might also serve as the target term representation
for algorithms extracted generically from the rules.

Secondly, more broadly, this work gives further evidence for a way of programming with strong
invariants and redundant but convenient information caches without fear of bugs arising
from inconsistency. We should put the programmer in charge! Dependent types should let
us take control of data representations and optimise them to support key operations,
but with the invariants clearly expressed in code and actively supporting program synthesis.

Only a fool would attempt to enforce the co-de-Bruijn invariants without support
from a typechecker, so naturally I have done so: using Haskell's {\tt
Integer} for bit vectors (making {\tt -1} the identity of the unscoped
thinning \emph{monoid}), I implemented a dependent type system, just for
fun. It was Hell's delight, even with the Agda version to follow. I was
sixteen again.

\paragraph{Acknowledgements.~} EPSRC project
EP/M016951/1 \emph{Homotopy Type Theory: Programming and Verification} funded
this work. My Mathematically Structured
Programming colleagues at Strathclyde made me get these ideas in shape:
Fredrik Nordvall Forsberg offered particularly useful advice about what
to omit. Philippa Cowderoy's \emph{information effects}
increased my sensitivity to the signposting of discards and duplications.
An EU TYPES Short Term Scientific Mission brought Andrea Vezzosi
to Strathclyde, provoking ideas and action for further work.
Invitations to present at \emph{Trends in Functional Programming 2017}
(Canterbury) and to my old Nottingham friends (notably Thorsten Altenkirch) helped
me find the words. James McKinna and Randy Pollack remain an inspiration.
And thanks, tweeps!

\bibliographystyle{eptcs}
\bibliography{EGTBS}
\end{document}

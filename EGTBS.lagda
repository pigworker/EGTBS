\documentclass[submission,copyright,creativecommons]{eptcs}
\providecommand{\event}{MSFP 2018} % Name of the event you are submitting to
\usepackage{breakurl}              % Not needed if you use pdflatex only.
\usepackage{underscore}            % Only needed if you use pdflatex.
\usepackage{pig}
\usepackage{stmaryrd}
\usepackage{upgreek}
\usepackage[all]{xy}

\ColourEpigram
\newcommand{\D}[1]{\blue{\ensuremath{\mathsf{#1}}}}
\newcommand{\C}[1]{\red{\ensuremath{\mathsf{#1}}}}
\newcommand{\F}[1]{\green{\ensuremath{\mathsf{#1}}}}
\newcommand{\V}[1]{\purple{\ensuremath{\mathit{#1}}}}

\newcommand{\OPE}{\textbf{OPE}}

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
%format constructor = "\mathkw{constructor}"
%format pattern = "\mathkw{pattern}"
%format rewrite = "\mathkw{rewrite}"
%format forall = "\forall"
%format . = "."

%if False
\begin{code}
module EGTBS where
\end{code}
%endif

%if False
\begin{code}

data Zero : Set where

\end{code}
%endif

\begin{document}
\maketitle

This paper gives a nameless \emph{co}-de-Bruijn representation of syntax with
binding. It owes a great deal to the work of Sato, Pollack, Schwichtengberg and Sakurai~\cite{spss:lambda.maps}
on canonical representation of
variable binding by mapping the use sites of each variable.

The key to any nameless representation of syntax is how it manages the way, at
a variable usage site, we choose to use \emph{one} variable and thus, implicitly
not any of the others in scope. The business of selecting from variables in
scope may, in general, be treated by considering how to embed the selection into
the whole scope.


\section{Basic Equipment}

We shall need the means to construct tuples. The empty tuple is given by
the \emph{record} type with no fields, which Agda recognizes as uniquely inhabited.
Dependent pairing is by means of the |Sg| type, abbreviated by |*| in its non-dependent special case.
%format Set = "\D{Set}"
%format One = "\D{One}"
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
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.7in}{
\begin{code}
record One : Set where constructor <>
\end{code}}
\parbox[t]{3in}{
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field fst : S; snd : T fst
open Sg public
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
pattern !_ t = _ , t
\end{code}}
%if False
\begin{code}
infixr 4 !_ _,_ _*_
\end{code}
%endif

\noindent
The \emph{pattern synonym} |!_| allows the first component to be determined by
the second: making it a right-associative prefix operator lets us write |! ! expression|
rather than |! (! (expression))|.

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


\section{$\OPE$: The Category of Order-Preserving Embeddings}

No category theorist would mistake me for one of their own. However, the key technology
in this paper can be helpfully conceptualised categorically. Category theory is the
study of compositionality for anything, not just sets-and-functions: here, we have an
opportunity to develop categorical structure with an example apart from the usual
functional programming apparatus, as emphasized particularly in the Haskell community. This strikes me as a good opportunity to revisit the basics.

\paragraph{Category (I): Objects and Morphisms.~} A \emph{category} is given by a class of \emph{objects} and a family
of \emph{morphisms} (or \emph{arrows}) indexed by two objects: \emph{source} and
\emph{target}. Abstractly, we may write $\mathbb{C}$ for a given
category, $||\mathbb{C}||$ for its class of objects, and
$\mathbb{C}(S,T)$ for its class of morphisms with source $S$ and
$T$, where $S,T\in||\mathbb{C}||$.
The rest of the definition will follow shortly, but let
us fix these notions for our example, the category, $\OPE_{|K|}$, of
\emph{order-preserving embeddings} between variable scopes.
The objects of $\OPE_{|K|}$ are \emph{scopes}, which we may represent
concretely backward (or `snoc') lists giving the \emph{kinds}, |K|, of
variables. (I shall habitually suppress the kind subscript and just write
$\OPE$ for the category.)

%format where = "\mathkw{where}"
%format Bwd = "\D{Bwd}"
%format B0 = "\C{[]}"
%format - = "\C{\mbox{{}-}\!,}"
%format _-_ = _ - _

\begin{code}
data Bwd (K : Set) : Set where
  B0   : Bwd K
  _-_  : Bwd K -> K -> Bwd K
\end{code}
%if False
\begin{code}
infixl 7 _-_
\end{code}
%endif

I use backward lists, because it is traditional to write contexts to
the left of judgements in typing rules and extend them on the
right. However, I use the word `scope' rather than `context' to suggest that
we are characterizing at least which variables we may refer to, but perhaps
not the full type information that one would find in a context.

The morphisms of $\OPE$ give an embedding from a source
scope to a target scope. Colloquially, we may call such embeddings
`thinnings', as they dilute with variables of the source scope with
more variables.  Equally, and usefully, we may see such a morphism as
expelling variables from the target scope, leaving a particular
selection as the source scope.  I write the step constructors postfix,
as thinnings (like contexts) grow on the right.

\newcommand{\apo}{\mbox{'}}
%format <= = "\D{\le}"
%format _<= = _ <=
%format _<=_ = _ <= _
%format oz = "\C{oz}"
%format os = "\C{os}"
%format o' = "\C{o\apo}"
%format _o' = _ o'
%format _os = _ os
\begin{code}
data _<=_ {K} : Bwd K -> Bwd K -> Set where
  _o'  : forall {iz jz k} ->  iz <= jz ->     iz          <=  (jz  -   k)
  _os  : forall {iz jz k} ->  iz <= jz ->  (  iz  -   k)  <=  (jz  -   k)
  oz   :                                          B0      <=       B0
\end{code}
%if False
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
\paragraph{Category (II): Identity and Composition.~} The definition of a category
insists on the existence of certain morphisms. Specifically, every object $X\in||\mathbb{C}||$
has an identity morphism $\iota_X\in\mathbb{C}(X,X)$ from that object to itself, and wherever the
target of one morphism coincides with the source of another, a composite
morphism must connect the source of the former to the target of the latter:
if $f\in\mathbb{C}(R,S)$ and $g\in\mathbb{C}(S,T)$, then $(f;g)\in\mathbb{C}(R,T)$.

For example, every scope has the identity thinning, |oi|, and thinnings compose via |<&=|.
(Presentations of composition vary: for functions, it is much more common
to write $g\cdot f$ for `$g$ \emph{after} $f$' than $f;g$ for
`$f$ \emph{then} $g$', but for thinnings, I prefer to retain a spatial
intuition.)
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{3in}{
\begin{code}
oi :  forall {K}{kz : Bwd K} ->
      kz <= kz
oi {kz = iz - k}  = oi os -- |os| preserves |oi|
oi {kz = B0}      = oz
\end{code}}
\hfill
\parbox[t]{3in}{
\begin{code}
_<&=_ :  forall {K}{iz jz kz : Bwd K} ->
         iz <= jz -> jz <= kz -> iz <= kz
th     <&= ph o'  = (th <&= ph) o'
th o'  <&= ph os  = (th <&= ph) o'
th os  <&= ph os  = (th <&= ph) os -- |os| preserves |<&=|
oz     <&= oz     = oz
\end{code}}

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

\paragraph{Category (III): Laws.~} to complete the definition of a
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
\begin{code}
law-oi<&=   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  oi <&= th == th
law-<&=oi   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->  th <&= oi == th
law-<&=<&=  :  forall {K}{iz jz kz lz : Bwd K}  (th : iz <= jz)(ph : jz <= kz)(ps : kz <= lz) ->
                                                                    th <&= (ph <&= ps) == (th <&= ph) <&= ps
\end{code}
%if False
\begin{code}
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
\begin{code}
antisym :  forall {K}{iz jz : Bwd K}(th : iz <= jz)(ph : jz <= iz) ->
           Sg (iz == jz) \ { refl -> th == oi * ph == oi }
\end{code}
%if False
\begin{code}
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
  S \ar[rr]^h \ar[dr]^f &   & T \ar[dl]^g \\
    & I \ar@@{.}@@(ul,dl)[ul]\ar@@{.}@@(ul,ur)[ul]
        \ar@@{.}@@(ur,dr)[ur]\ar@@{.}@@(ur,ul)[ur]
        &
}\]}

~

That is, the morphisms are \emph{triangles}. A seasoned dependently typed
programmer will be nervous at the sight of a definition like
%format ->/ = "\F{\to_{\slash}}"
%format _->/_ = _ ->/ _
\begin{spec}
_->/_ :  forall {K}{iz jz kz : Bwd K} -> (iz <= kz) -> (jz <= kz) -> Set
th ->/ ph = Sg _ \ ps -> (ps <&= ph) == th
\end{spec}
because the equation gives us few options when it comes to manipulating
triangles. Dependent pattern matching relies on \emph{unification} of
indices, but defined function symbols like |<&=| make unification
difficult, obliging us to reason about the \emph{edges} of the triangles.
A helpful move at this point is to define triangles inductively, as the
\emph{graph} of |<&=|.
%format Tri = "\D{Tri}"
%format t-'' = "\C{t\mbox{{}-}\apo\!\apo}"
%format t's' = "\C{t\apo\!s\apo}"
%format tsss = "\C{tsss}"
%format _t-'' = _ t-''
%format _t's' = _ t's'
%format _tsss = _ tsss
%format tzzz = "\C{tzzz}"
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
Observe that the indexing is now entirely in constructor form, which will allow
easy unification. Moreover, there is \emph{no information} in a |Tri| structure,
as its indexing (which derived from a pattern matching partition) completely
determines its structure.
The intended relationship between |Tri| and |<&=| thus holds.
%format tri = "\F{tri}"
%format comp = "\F{comp}"
\begin{code}
tri   :  forall {K}{iz jz kz : Bwd K}(th : iz <= jz)(ph : jz <= kz) -> Tri th ph (th <&= ph)
comp  :  forall {K}{iz jz kz : Bwd K}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
           Tri th ph ps -> ps == (th <&= ph)
\end{code}
The proofs are easy inductions.
%if False
\begin{code}
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
\begin{code}
egTri :  forall {K}{k0 k1 k2 k3 k4 : K} ->  Tri {kz = B0 - k0 - k1 - k2 - k3 - k4}
                                            (oz os o' os) (oz os o' os o' os) (oz os o' o' o' os)
egTri = tzzz tsss t-'' t's' t-'' tsss
\end{code}

We obtain a definition of morphisms in the slice as triangles. (The |Sg _| tells Agda
to infer the type of |ps|, which is forced by its use as an index of |Tri|.)
\begin{code}
_->/_ :  forall {K}{iz jz kz : Bwd K} -> (iz <= kz) -> (jz <= kz) -> Set
ps ->/ ph = Sg _ \ th -> Tri th ph ps
\end{code}

A useful property specific to thinnings is that morphisms in the slice category are \emph{unique}.
It is straightforward to formulate this property in terms of triangles with edges in
common, and then to work by induction on the triangles rather than their edges.
As a result, it will be cheap to establish \emph{universal properties} in the slices of
$\OPE$, asserting the existence of unique morphisms: uniqueness comes for free!
%format tri1 = "\F{tri1}"
\begin{code}
tri1 :  forall {K}{iz jz kz : Bwd K}{th th' : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
        Tri th ph ps -> Tri th' ph ps -> th == th'
\end{code}
%if False
\begin{code}
tri1 (t  t-'')  (t'  t-'')  rewrite tri1 t t'  = refl
tri1 (t  t's')  (t'  t's')  rewrite tri1 t t'  = refl
tri1 (t  tsss)  (t'  tsss)  rewrite tri1 t t'  = refl
tri1     tzzz        tzzz                      = refl
\end{code}
%endif


\section{Functors, a densely prevalent notion}

Haskell makes considerable use of the type class \texttt{Functor}
and its many subclasses, but this is only to scratch the surface: Haskell's functors
are \emph{endo}functors, mapping the `category' of types-and-functions into itself.
Once we adopt the appropriate level of
generality, functoriality sprouts everywhere, and the same structures
can be usefully functorial in many ways.

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

For example, every |k : K| induces a functor from $\OPE$ to itself
which acts by scope extension, |(_ - k)| on objects and |os| on
morphisms. The very definitions of |oi| and |<&=| show that |os|
preserves identity and composition. Let us refer to this
functor as \emph{weakening} by |k|.
%(I am sufficiently old-fashioned
%and pedantic to distinguish weakening --- adding new variables with
%most local scope --- from thinning --- adding new variables anywhere,
%but this is far from universal.)

Before we can have more examples, we shall need some more
categories. Let |Set| be the category whose objects are Agda types in
the |Set| universe and whose morphisms in $|Set|(S, T)$ are
functions of type $S\to T$, with the usual identity and
composition. Consider morphisms equal if they agree
\emph{pointwise}. As an exercise, find the action on morphisms of
show the |Set| to |Set| functor which is |Bwd| on objects.

However, our work takes us in a different direction, profiting from
the richness of dependent types: let us construct new categories by
\emph{indexing}. If |I : Set|, we may then take |I -> Set| to be the
category whose objects are \emph{families} of objects in |Set|, |S, T
: I -> Set| with morphisms being the corresponding (implicitly
indexed) families of morphisms in |{i : I} -> S i -> T i|. Let us
abbreviate:
%format -:> = "\mathrel{\dot{\to}}"
%format _-:>_ = _ -:> _
\begin{code}
_-:>_ : {I : Set}(S T : I -> Set) -> Set
S -:> T = forall {i} -> S i -> T i
\end{code}

Consider
morphisms equal if they map each index to pointwise equal functions.
We may define a functor from |K -> Set| to |Bwd K -> Set| as follows:

%format All = "\D{All}"
%format all = "\F{all}"
%format (Cix (k)) = "\F{\overline{\black{" k "}}}"
%format Cix_ = "\F{\overline{\black{\_}}}"
%format Set1 = Set "_1"
%if False
\begin{code}
Cix_ : Set -> Set1
Cix K = Bwd K -> Set
\end{code}
%endif
\noindent
\begin{code}
data  All {K}     (P  : K      -> Set) : Bwd K  -> Set where
  B0   :                                      All P B0
  _-_  : forall {kz k} -> All P kz -> P k ->  All P (kz - k)

all  :   forall {K}{P Q : K -> Set} -> (P -:> Q) -> (All P -:> All Q)
all f B0        = B0
all f (pz - p)  = all f pz - f p
\end{code}

For a given |K|, |All| acts on objects, giving for each
|k| in a scope, some value in |P k|, thus giving us a notion of
\emph{environment}. The action on morphisms, |all|, lifts \emph{kind-respecting}
operations on values to \emph{scope-repecting} operations on
environments. Identity and composition are readily
preserved. In the sequel, it will be convenient to abbreviate
|Bwd K -> Set| as |(Cix K)|, for types indexed over scopes.

However, |All| gives more functorial structure.
Fixing |kz|, we obtain |\ P -> All P kz|, a functor
from |K -> Set| to |Set|, again with the instantiated |all| acting on
morphisms. And still, there is more.

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

For example, $\op{\OPE}(|jz|,|iz|) = |iz <= jz|$ allows us to see the
category of thinnings as the category of \emph{selections}, where we choose
just |iz| from the available |jz|. If we have an environment for all of the
|jz|, we should be able to whittle it down to an environment for just the
|iz| by throwing away the values we no longer need. That is to say,
|All P| is a \emph{functor} from $\op\OPE$ to |Set|, whose action on
morphisms is
%format <?= = "\F{\le\!?}"
%format _<?=_ = _ <?= _
%format <?=_ = <?= _
\begin{code}
_<?=_ : forall {K P}{jz iz : Bwd K}  -> iz <= jz -> All P jz -> All P iz
oz       <?= B0        = B0
(th os)  <?= (pz - p)  = (th <?= pz) - p
(th o')  <?= (pz - p)  = th <?= pz
\end{code}
It is not hard to check that the identity selection (selecting all
elements) acts as the identity on environments, and that composition
(making a subselection from a selection) is also respected.

Note that a functor from $\op{\mathbb{C}}$ to $\mathbb{D}$ is sometimes
called a \emph{contravariant functor} from $\mathbb{C}$ to $\mathbb{D}$.
%Moreover, a functor from $\op{\mathbb{C}}$ to |Set| is sometimes called a
%\emph{presheaf} on $\mathbb{C}$. That is, |<?=| makes |All P| a presheaf on
%$\OPE$.

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
|<?=| is uniform in |P|, and hence that if |f : {k : K} -> P k -> Q k|, then
|all f (th <?= pz)| = |th <?= all f pz|.


Dependently typed programming thus offers us a much richer seam of
categorical structure than the basic types-and-functions familiar
from Haskell (which demands some negotiation of totality even to
achieve that much). For me, at any rate, this represents an opportunity
to make sense of the categorical taxonomy by relating it to concrete
programming examples, and at the same time, organising those programs
and giving healthy indications for \emph{what to prove}.

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


\section{De Bruijn Syntax via $\OPE$}

It is not unusual to find natural numbers as bound variables, perhaps
with some bound enforced by typing, either by an inequality or by using
a `finite set of size $n$' construction, often called `Fin'. However, we
may also see scope membership as exactly singleton embedding, and then
give the well scoped but untyped
de Bruijn $\lambda$-terms using membership for
variables~\cite{deBruijn:dummies}.
%format <- = "\F{\leftarrow}"
%format _<-_ = _ <- _
%format <> = "\C{\langle\rangle}"
%format LamTm = "\D{Lam}"
%format var = "\C{\scriptstyle\#}"
%format $ = "\C{\scriptstyle\$}"
%format _$_ = _ $ _
%format lam = "\C{\uplambda}"
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{1.8in}{
\begin{code}
_<-_ : forall {K} -> K -> (Cix K)
k <- kz = B0 - k <= kz
\end{code}}
\parbox[t]{4in}{
\begin{code}
data LamTm (iz : Bwd One) : Set where          -- |LamTm : (Cix One)|
  var  : (x : <> <- iz)  ->         LamTm iz   -- \emph{finds} a variable
  _$_  : (f s : LamTm iz) ->        LamTm iz   -- associates left
  lam  : (t : LamTm (iz - <>)) ->   LamTm iz   -- \emph{binds} a variable
\end{code}}
%if False
\begin{code}
infixl 5 _$_
\end{code}
%endif

Variables are represented by pointing, which saves choosing
names for them. We have but one way to encode a given term in a given scope.
It is only when we point to one variable in scope that we exclude
the possibility of choosing the others. That is to say de Bruijn index
representation effectively uses thinnings to discard unwanted variables as
\emph{late} as possible, in the \emph{leaves} of syntax trees.

Note the way the scope index |iz| is used in the data type, as the
target of a thinning in |var|, and acted on by weakening in |lam|.
Correspondingly, thinnings act functorially on terms, ultimately
by postcomposition, but because terms keep their thinnings at their leaves,
we must hunt the entire tree to find them.
%format ^L = "\F{\uparrow}"
%format _^L_ = _ ^L _
\begin{code}
_^L_ : forall {iz jz} -> LamTm iz -> iz <= jz -> LamTm jz
var i    ^L th = var (i <&= th)
(f $ s)  ^L th = (f ^L th) $ (s ^L th)
lam t    ^L th = lam (t ^L th os)
\end{code}
%if False
\begin{code}
infixl 7 _^L_
\end{code}
%endif

The point of this paper is to consider the other canonical placement of the
thinnings, nearest the \emph{roots} of syntax trees, discarding unwanted variables
at the \emph{earliest} possible opportunity.


\section{Things-with-Thinnings (a Monad)}

Let us develop the habit of working with well scoped terms packed with a thinning
at the root, discarding those variables from the scope which are not in the
\emph{support} of the term.

%format / = "\D{/}"
%format /_ = / _
%format _/_ = _ / _
%format ^ = "\C{\uparrow}"
%format _^_ = _ ^ _
%format support = "\F{support}"
%format thing = "\F{thing}"
%format thinning = "\F{thinning}"
\begin{code}
record _/_ {K}(T : (Cix K))(scope : Bwd K) : Set where -- |(T /_) : (Cix K)|
  constructor _^_
  field {support} : Bwd K; thing : T support; thinning : support <= scope
\end{code}
%if False
\begin{code}
infixl 7 _^_
open _/_
\end{code}
%endif

Notice that |/| is a functor from |(Cix K)| to itself, acting on
morphisms as follows:
%format map/ = "\F{map/}"
\begin{code}
map/ :  forall {K}{S T : (Cix K)} -> (S -:> T) -> ((S /_) -:> (T /_))
map/ f (s ^ th) = f s ^ th
\end{code}
In fact, the categorical structure of $\OPE$ makes |/| a \emph{monad}.
Let us recall the definition.

\paragraph{Monad.~} A functor $M$ from $\mathbb{C}$ to $\mathbb{C}$ gives
rise to a \emph{monad} $(M,\eta,\mu)$ if we can find a pair of natural
transformations, respectively `unit' and `multiplication'
\[
\eta_X : \Id(X) \to M(X)
\qquad\qquad
\mu_X : M(M(X)) \to M(X)
\]
which, respectively, `add an $M$ layer' and `merge $M$ layers', subject
to the conditions that merging an added layer yields the identity
(whether the layer added is `outer' or `inner'), and that
adjacent $M$ layers may be merged pairwise in any order.
\[
  \eta_{M(X)};\mu_X = \iota_{M(X)} \qquad\qquad
  M(\eta_X);\mu_X = \iota_{M(X)} \qquad\qquad
  \mu_{M(X)};\mu_X = M(\mu_X);\mu_X
\]

The categorical structure of thinnings induces a monadic structure on
things-with-thinnings. Here, `adding a layer' amounts to `wrapping with a
thinning', i.e., forgetting that only a selection from the variables in
scope is needed.
%format unit/ = "\F{unit/}"
%format mult/ = "\F{mult/}"
%format thin/ = "\F{thin/}"
\vspace*{ -0.2in} \\
%\noindent
\parbox{2.7in}{
\begin{code}
unit/ : forall {K}{T : (Cix K)} -> T -:> (T /_)
unit/ t = t ^ oi
\end{code}}
\parbox{2.9in}{
\begin{code}
mult/ : forall {K}{T : (Cix K)} -> ((T /_) /_) -:> (T /_)
mult/ ((t ^ th) ^ ph) = t ^ (th <&= ph)
\end{code}}
\\
The proof obligations to make $(|/|,|unit/|,|mult/|)$ a monad are
exactly those required to make $\OPE$ a category in the first place.

In particular, things-with-thinnings are easy to thin further, indeed,
parametrically so. In other words, |(T /)| is uniformly a functor from
$\OPE$ to |Set|.
\begin{code}
thin/ : forall {K T}{iz jz : Bwd K} -> T / iz -> iz <= jz -> T / jz
thin/ t th = mult/ (t ^ th)
\end{code}

\newcommand{\Kleisli}[1]{\textbf{Kleisli}(#1)}
\paragraph{Kleisli Category.~} Every monad $(M,\eta,\mu)$ on
$\mathbb{C}$ induces a category $\Kleisli(M,\eta,\mu)$ with
\[
||\Kleisli{M,\eta,\mu}|| = ||\mathbb{C}|| \qquad
\Kleisli{M,\eta,\mu}(S,T) = \mathbb{C}(S,M(T)) \qquad
\iota^{\textbf{K}}_X = \eta_X \qquad
f;^{\textbf{K}}g = f;M(g);\mu
\]
We sometimes call the morphisms in a Kleisli category \emph{Kleisli arrows}.

The Kleisli arrows for |/| are operations with types such as |S -:> (T /_)|
which \emph{discover dependency}: they turn an |S| over any scope |kz|
into a |T| known to depend on at most some of the |kz|.

Shortly, we shall give exactly such an operation to discover the
variables in scope on which a term syntactically depends. However, it
is not enough to allow a thinning at the root: |LamTm / iz| is a poor
representation of terms over |iz|, as we may choose whether to discard
unwanted variables either at root or at leaves. To recover a canonical
positioning of thinnings, we must enforce the property that a term's
|support| is \emph{relevant}: if a variable is not discarded by the
|thinning|, it \emph{must} be used in the |thing|. Or as Spike
Milligan put it, `Everybody's got to be somewhere.'.


\section{The Curious Case of the Coproduct in  Slices of $\OPE$}

The thing-with-thinning construction makes crucial use of `arrows into
|scope| from some |support|', which we might learn to recognize as objects
in the slice category $\OPE/|scope|$.

However, we also acquire some crucial additional structure. The key clue
is that an object in the slice |(_<= kz)| is effectively a \emph{bit vector},
with one bit per variable telling whether or not it has been selected.
Bit vectors inherit structure from Boolean algebra, via the
`Naperian' array structure of vectors~\cite{DBLP:conf/esop/Gibbons17}.

\paragraph{Initial object.~} A category $\mathbb{C}$ has initial object
$0$, if there is a unique morphism in $\mathbb{C}(0,X)$ for every $X$.

We are used to the \emph{empty type} playing this r\^ole in the
category of types-and-functions, with the empty case analysis giving
the morphism, which is vacuously pointwise unique. In $\OPE$, the
empty \emph{scope} plays the same r\^ole, with the unique morphism
given as the `constant false' bit vector:
%format oe = "\F{oe}"
%format law-oe = "\F{law-}" oe

\noindent
\parbox[t]{2.7in}{
\begin{code}
oe : forall {K}{kz : Bwd K} -> B0 <= kz
oe {kz = iz - k}  = oe o'
oe {kz = B0}      = oz
\end{code}}
\parbox[t]{3in}{
\begin{code}
law-oe :  forall {K}{kz : Bwd K}
          (th : B0 <= kz) -> th == oe
\end{code}}
%if False
\begin{code}
law-oe oz = refl
law-oe (th o') rewrite law-oe th = refl
\end{code}
%endif

By return of post, we obtain that $(|B0|,|oe|)$ is the initial object in the
slice category |_ <= kz|.
%format oe/ = oe "\F{\slash}"
\begin{code}
oe/ : forall {K}{iz kz : Bwd K}(th : iz <= kz) -> oe ->/ th
oe/ th with tri oe th
... | t rewrite law-oe (oe <&= th) = oe , t
\end{code}

The initial object gives us a way to make \emph{constants} with empty support,
i.e., noting that none of the available variables is \emph{relevant}.
%format OneR = One "_{R}"
%format <>R = "\F{\langle\rangle}_{R}"
\begin{code}
data OneR {K} : (Cix K) where  <> : OneR B0  -- `$R$' for \emph{relevant}

<>R : forall {K}{kz : Bwd K} -> OneR / kz
<>R = <> ^ oe
\end{code}

%In other words, we have found a \emph{terminal} object, namely
%|(OneR /_)|, in |Bwd K -> Set|.

%\paragraph{Terminal object.~} A category $\mathbb{C}$ has terminal object
%$1$, if there is a unique morphism in $\mathbb{C}(X,1)$ for every $X$.

%format *R = "\D{\times}_R"
%format _*R_ = _ *R _
%format ,R = "\F{,}_{R}"
%format _,R_ = _ ,R _
We should expect the trivial constant to be the limiting case of some notion
of \emph{relevant pairing}, induced by \emph{coproducts} in the slice category.
If we have two objects in |(_ <= kz)| representing two subscopes, there should
be a smallest subscope which includes both, amounting to pairwise disjunction
of the bitvectors.

\paragraph{Coproduct.~} Objects $S$ and $T$ of category $\mathbb{C}$ have
a coproduct object $S + T$ if there are morphisms $l\in \mathbb{C}(S, S + T)$ and
$r\in \mathbb{C}(S, S + T)$ such that every pair
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
let us try to construct the coproduct of two singleton scopes, $S = T = |B0 - <>|$.
We can begin one coproduct diagram by taking $U = |B0 - <>|$ and $f = g = |oi|$:
that forces the issue, as our only candidate for $S + T$ is once again the
singleton |B0 - <>|, with $l = r = |oi|$, making $h = |oi|$; a larger $S + T$
will not embed in $U$, a smaller will not embed $S$ and $T$. However, we may
begin a different coproduct diagram, taking $U' = |B0 - <> - <>|$ with two variables,
allowing us to choose $f' = |oz os o'|$ and $g' = |oz o' os|$, and now there is
no way to choose an $h'$ which post-composes $l$ and $r$ (both |oi|, making $h'$ itself)
to yield $f'$ and $g'$ respectively.

Fortunately, we shall get what we need. $\OPE$ may not have coproducts, but its
\emph{slices} do.
%It is not the case that colimit structure in $\mathbb{C}/I$
%arises \emph{only} via inheritance from $\mathbb{C}$.
Examine the data.
We have two subscopes of some |kz|, |th : iz <= kz| and |ph : jz <= kz|. Their
coproduct must be some |ps : ijz <= kz|, where our $l$ and $r$ must be
triangles |Tri th' ps th| and |Tri ph' ps ph|, giving us morphisms in
|th ->/ ps| and |ph ->/ ps|, respectively. Intuitively, we should choose |ps|
to be the pointwise disjunction of |th| and |ph|, so that |ijz| is as small
as possible: |th'| and |ph'| will then \emph{cover} |ijz|. Let us define this
notion of covering inductively, so we build diagrams and
reason by pattern matching.
%format Cover = "\D{Cover}"
%format c's = "\C{c\apo s}"
%format cs' = "\C{cs\apo}"
%format css = "\C{css}"
%format _c's = _ c's
%format _cs' = _ cs'
%format _css = _ css
%format czz = "\C{czz}"
\begin{code}
data Cover {K} : {iz jz ijz : Bwd K} -> iz <= ijz -> jz <= ijz -> Set where
  _c's  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover th ph -> Cover {ijz = _ - k}  (th o')  (ph os)
  _cs'  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover th ph -> Cover {ijz = _ - k}  (th os)  (ph o')
  _css  : forall {iz jz ijz k}{th : iz <= ijz}{ph : jz <= ijz} ->
            Cover th ph -> Cover {ijz = _ - k}  (th os)  (ph os)
  czz   : Cover oz oz
\end{code}
%if False
\begin{code}
infixl 8 _c's _cs' _css
\end{code}
%endif
Note that we have no constructor which allows both |th| and |ph| to
omit a target variable: everybody's got to be somewhere. Let us compute
the coproduct, then check its universal property.
%format cop = "\F{cop}"
\vspace*{ -0.2in} \\
%\noindent
\parbox{3.5in}{
\begin{code}
cop :  forall {K}{kz iz jz : Bwd K}
       (th : iz <= kz)(ph : jz <= kz) ->
       Sg _ \ ijz -> Sg (ijz <= kz) \ ps ->
       Sg (iz <= ijz) \ th' -> Sg (jz <= ijz) \ ph' ->
       Tri th' ps th * Cover th' ph' * Tri ph' ps ph
\end{code}}
\parbox{2in}{
\[\xymatrix{
 |iz| \ar[rrrd]^{|th|} \ar@@{.>}[rd]^{|th'|} &&& \\
 &  |ijz| \ar@@{.>}[rr]^{|ps|}  && |kz| \\ 
 |jz| \ar[rrru]^{|ph|} \ar@@{.>}[ru]^{|ph'|} &&& \\
}\]}

\begin{code}
cop (th  o') (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t-''  , c       , tr  t-''
cop (th  o') (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  t's'  , c  c's  , tr  tsss
cop (th  os) (ph  o')  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  cs'  , tr  t's'
cop (th  os) (ph  os)  = let ! ! ! ! tl , c , tr = cop th ph in  ! ! ! ! tl  tsss  , c  css  , tr  tsss
cop      oz       oz   =                                         ! ! ! !     tzzz  ,    czz  ,     tzzz
\end{code}
To show that we have really computed a coproduct, we must show
that any other pair of triangles from |th| and |ph| to
some |ps'| must induce a (unique) morphism from |ps| to |ps'|.
%format copU = "\F{copU}"
\begin{code}
copU :  forall {K}{kz iz jz ijz : Bwd K}
        {th : iz <= kz}{ph : jz <= kz}{ps : ijz <= kz}{th' : iz <= ijz}{ph' : jz <= ijz}->
        Tri th' ps th -> Cover th' ph' -> Tri ph' ps ph ->
        forall {ijz'}{ps' : ijz' <= kz} -> th ->/ ps' -> ph ->/ ps' -> ps ->/ ps'
\end{code}
The construction goes by induction on the triangles which share the edge |ps'|
and inversion of the coproduct construction.
%if False
\begin{code}
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
The payoff from this construction is the notion of \emph{relevant pair}:
%format *R = "\D{\times}_R"
%format _*R_ = _ *R _
%format ,R = "\C{,}_R"
%format _,R_ = _ ,R _
%format pair = "\C{pair}"
%format outl = "\F{outl}"
%format outr = "\F{outr}"
%format cover = "\F{cover}"
\begin{code}
record _*R_ {K}(S T : (Cix K))(ijz : Bwd K) : Set where -- |S *R T : (Cix K)|
  constructor pair
  field  outl : S / ijz;  outr : T / ijz;  cover : Cover (thinning outl) (thinning outr)

_,R_ : forall {K}{S T : (Cix K)}{kz} -> S / kz -> T / kz -> (S *R T) / kz
(s ^ th) ,R (t ^ ph) = let ! ps , th' , ph' , _ , c , _ = cop th ph in pair (s ^ th') (t ^ ph') c ^ ps
\end{code}


\section{Monoidal Structure of Order-Preserving Embeddings}

In order to talk about binding, we need to talk about context extension.
We have seen extension by a single `snoc', but simultaneous binding also
makes sense. Concatenation induces a monoidal structure on scopes, the
objects of $\OPE$, which extends to morphisms.
%format ++ = "\F{+\!\!+}"
%format _++_ = _ ++ _
%format <++= = ++ "_{" <= "}"
%format _<++=_ = _ <++= _
\vspace*{ -0.2in} \\
%\noindent
\parbox[t]{2.8in}{
\begin{code}
_++_ : forall {K}(kz jz : Bwd K) -> Bwd K
kz ++ B0        = kz
kz ++ (iz - j)  = (kz ++ iz) - j
\end{code}}
%if False
\begin{code}
infixl 7 _++_
\end{code}
%endif
\parbox[t]{3in}{
\begin{code}
_<++=_ :  forall {K}{iz jz iz' jz' : Bwd K} ->
  iz <= jz -> iz' <= jz' -> (iz ++ iz') <= (jz ++ jz')
th <++=      oz   =    th
th <++= (ph  os)  = (  th <++= ph) os
th <++= (ph  o')  = (  th <++= ph) o'
\end{code}}

Moreover, given a embedding into a concatenation, we can split it
into local and global parts.
%format -! = "\F{\dashv}"
%format _-!_ = _ -! _
\begin{code}
_-!_ : forall {K}{iz kz}(jz : Bwd K)(ps : iz <= (kz ++ jz)) ->
       Sg (Bwd K) \ kz' -> Sg (Bwd K) \ jz' -> Sg (kz' <= kz) \ th -> Sg (jz' <= jz) \ ph ->
       Sg (iz == (kz' ++ jz')) \ { refl -> ps == (th <++= ph) }
B0        -! ps                                               = ! ! ps , oz , refl , refl
(kz - k)  -! (ps os)             with kz -! ps
(kz - k)  -! (.(th <++= ph) os)  | ! ! th , ph , refl , refl  = ! ! th , ph os , refl , refl
(kz - k)  -! (ps o')             with kz -! ps
(kz - k)  -! (.(th <++= ph) o')  | ! ! th , ph , refl , refl  = ! ! th , ph o' , refl , refl
\end{code}

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
\begin{code}
data VaR {K}(k : K) : (Cix K) where only : VaR k (B0 - k)

vaR : forall {K}{k}{kz : Bwd K} -> k <- kz -> VaR k / kz
vaR x = only ^ x
\end{code}

\paragraph{Untyped $\lambda$-calculus.~}
We can now give the lambda terms for which all \emph{free} variables are
relevant as follows.
Converting de Bruijn to co-de-Bruijn representation is easy with
smart constructors.
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

%format combK = "\F{\mathbb{K}}"
%format combS = "\F{\mathbb{S}}"
E.g., compare de Bruijn terms for the |combK| and |combS| combinators with their co-de-Bruijn form.
\begin{spec}
combK combS : LamTm B0
combK         =  lam (lam (var (oe os o')))
lamTmR combK  =  lam (oz os \\ lam (oz o' \\ var only)) ^ oz

combS         =  lam (lam (lam (var (oe os o' o') $ var (oe os) $ (var (oe os o') $ var (oe os)))))
lamTmR combS  =  lam (oz os \\ lam (oz os \\ lam (oz os \\
  app (pair  (app  (pair (var only ^ oz os o') (var only ^ oz o' os) (czz cs' c's))  ^ oz os o' os)
             (app  (pair (var only ^ oz os o') (var only ^ oz o' os) (czz cs' c's))  ^ oz o' os os)
             (czz cs' c's css)) ))) ^ oz
\end{spec}
Staring bravely, we can see that |combK| uses its first argument
to deliver what is plainly a constant function: the second |lam|
discards its argument, leaving only one variable in scope. Meanwhile,
it is plain that |combS| uses all three inputs (`function', `argument',
`environment'): in the subsequent application, the function goes
left, the argument goes right, and the environment is shared.


\section{A Universe of Metasyntaxes-with-Binding}

%format Kind = "\D{Kind}"
%format Scope = "\F{Scope}"
%format => = "\C{\Rightarrow}"
%format _=>_ = _ => _
There is nothing specific to the $\lambda$-calculus about de Bruijn
representation or its co-de-Bruijn counterpart. We may develop the
notions generically for multisorted syntaxes. If the sorts of our
syntax are drawn from set $I$, then we may characterize terms-with-binding
as inhabiting |Kind|s |kz => i|, which specify an extension of the scope
with new bindings |kz| and the sort |i| for the body of the binder.
\begin{code}
data Kind (I : Set) : Set where _=>_ : Bwd (Kind I) -> I -> Kind I
\end{code}
%if False
\begin{code}
infix 6 _=>_
\end{code}
%endif
Notice that |Kind|s offer higher-order abstraction: a bound variable itself
has a |Kind|, being an object sort parametrized by a scope of bound variables,
where the latter is, as in previous  sections, a |Bwd| list, with the |K| parameter now
fixed to be |Kind I|. Object variables have sorts; \emph{meta}-variables have |Kind|s.
For example, when we write the $\beta$-rule
\[
  (\lambda x.\,t[x])\:s \;\leadsto\; t[s]
\]
the $t$ and the $s$ are not variables of the object calculus like $x$.
They stand as placeholders, $s$ for some term and $t[x]$ for some term
with a parameter which can be instantiated, and is instantiated by $x$
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
  RecD   : Kind I ->                              Desc I
  OneD   :                                        Desc I
  _*D_   : Desc I -> Desc I ->                    Desc I
  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
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
  field
    Data    : Set
    decide  : (x y : Data) -> Decide (x == y)
open Datoid
\end{code}}
%if False
\begin{code}
data Desc (I : Set) : Set1 where
  RecD   : Kind I ->                              Desc I
  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
  OneD   :                                        Desc I
  _*D_   : Desc I -> Desc I ->                    Desc I
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
\vspace*{ -0.2in}
\begin{code}
LamD : One -> Desc One
LamD <> = SgD LAMTAG \  { app  -> RecD (B0 => <>) *D RecD (B0 => <>)
                        ; lam  -> RecD (B0 - (B0 => <>) => <>) }
\end{code}
Note that we do not and cannot include a tag or description for
the use sites of variables in terms: use of variables in scope
pertains not to the specific syntax, but to the general notion
of what it is to be a syntax.

\paragraph{Interpreting |Desc| as de Bruijn Syntax.~}
%format [! = "\F{\llbracket}"
%format !! = "\F{\mid}"
%format !] = "\F{\rrbracket}"
%format [!_!!_!] = [! _ !! _ !]
Let us give the de Bruijn interpretation of our syntax descriptions.
We give meaning to |Desc| in the traditional manner, interpreting
them as strictly positive operators in some |R| which gives the semantics
to |RecD|. In recursive positions, the scope grows by the bindings demanded by the given |Kind|.
\begin{code}
[!_!!_!] : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD (jz => i)  !! R !] kz = R i (kz ++ jz)
[! SgD S T         !! R !] kz = Sg (Data S) \ s -> [! T s !! R !] kz
[! OneD            !! R !] kz = One
[! S *D T          !! R !] kz = [! S !! R !] kz * [! T !! R !] kz
\end{code}
%Note that we work with scope-indexed sets and an index |kz| giving the
%kinds of the variables in scope. 

At use sites, higher-kinded variables must be instantiated, just
like $t[x]$ in the $\beta$-rule example, above.
We can compute from a given scope the |Desc|ription of the
spine of actual parameters required.
%format SpD = "\F{Sp}_D"
\begin{code}
SpD : forall {I} -> Bwd (Kind I) -> Desc I
SpD      B0      =          OneD
SpD (kz  -   k)  = SpD kz   *D    RecD k
\end{code}

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
data Tm {I}(D : I -> Desc I)(i : I)(kz : Bwd (Kind I)) : Set where -- |Tm D i : (Cix (Kind I))|
  _#$_  : forall {jz} -> (jz => i) <- kz ->  [! SpD jz  !! Tm D !] kz ->  Tm D i kz
  [_]   :                                    [! D i     !! Tm D !] kz ->  Tm D i kz
infixr 5 _#$_
\end{code}

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

\paragraph{Interpreting |Desc| as co-de-Bruijn Syntax.~}
We may, of course, also interpret |Desc|riptions in co-de-Bruijn style,
enforcing that all variables in scope are relevant, and demanding that
binding sites make clear which variables are to be used. Let us work in
|Scope I -> Set| where practical.
%format !]R = "\F{\rrbracket}_R"
%format [!_!!_!]R = [! _ !! _ !]R
%format TmR = Tm "_R"
%format # = "\C{\scriptstyle \#}"
\begin{code}
[!_!!_!]R : forall {I} -> Desc I -> (I -> (Cix (Kind I))) -> (Cix (Kind I))
[! RecD (jz => i)  !! R !]R = jz !- R i
[! SgD S T         !! R !]R = \ kz -> Sg (Data S) \ s -> [! T s !! R !]R kz
[! OneD            !! R !]R = OneR
[! S *D T          !! R !]R = [! S !! R !]R *R [! T !! R !]R

data TmR {I}(D : I -> Desc I)(i : I) : (Cix (Kind I)) where
  #     : forall {jz} -> (VaR (jz => i) *R  [! SpD jz  !! TmR D !]R)  -:>  TmR D i
  [_]   :                                   [! D i     !! TmR D !]R   -:>  TmR D i
\end{code}

Let us compute co-de-Bruijn terms from de Bruijn terms, generically.
%format code = "\F{code}"
%format codes = "\F{codes}"
%format ,_ = , _
\begin{code}
code   : forall {I}{D : I -> Desc I}{i}  ->  Tm D i           -:>  (TmR D i /_)
codes  : forall {I}{D : I -> Desc I} S   ->  [! S !! Tm D !]  -:>  ([! S !! TmR D !]R /_)
code                    (_#$_ {jz} x ts)  = map/ #    (vaR x ,R codes (SpD jz) ts)
code {D = D}{i = i}     [ ts ]            = map/ [_]  (codes (D i) ts)
codes (RecD (jz => i))  t                 = jz \\R code t
codes (SgD S T)         (s , ts)          = map/ (s ,_) (codes (T s) ts)
codes OneD              <>                = <>R
codes (S *D T)          (ss , ts)         = codes S ss ,R codes T ts
\end{code}

%if False


The |code| translations of |combKD| and |combSD| are, respectively,
\begin{spec}
[ lam , oz os \\ [ lam , oz o' \\ # (only <[ czz cs' ]> <>) ] ] ^ oz
\end{spec}
and
\begin{spec}
[  lam , oz os \\  [ lam , oz os \\  [ lam , oz os \\
   [ app
   ,  (  (oz \\ [ app , ((oz \\ # (only <[ czz cs' ]> <>))  <[ czz cs' c's ]>  (oz \\ # (only <[ czz cs' ]> <>))) ])
         <[ czz cs' c's css ]>
         (oz \\ [ app , ((oz \\ # (only <[ czz cs' ]> <>))  <[ czz cs' c's ]>  (oz \\ # (only <[ czz cs' ]> <>))) ]))
   ]
]                  ]                 ] ^ oz
\end{spec}
exactly as we hand-coded them, above, with a little extra noise, |oz \\|, recording the fact that |app| binds
no variables in either function or argument subterms.



\begin{spec}
_<??=_ : forall {I R}{iz jz kz : Scope I} -> iz <= jz -> [! SpD jz !! R !]RR / kz -> [! SpD iz !! R !]RR / kz
oz <??= (<> ^ ps) = <>R
(th os) <??= ((rz ^ phl) <-> (r ^ phr) ! _ ^ ps) = (th <??= (rz ^ (phl <&= ps))) ,RR (r ^ (phr <&= ps))
(th o') <??= ((rz ^ phl) <-> (r ^ phr) ! _ ^ ps) = th <??= (rz ^ (phl <&= ps))

data Deal {K} : Bwd K -> Bwd K -> Bwd K -> Set where
  dzz : Deal B0 B0 B0
  ds' : forall {iz i jz kz} -> Deal iz jz kz -> Deal (iz - i) jz (kz - i)
  d's : forall {iz jz j kz} -> Deal iz jz kz -> Deal iz (jz - j) (kz - j)

dealRefine : forall {K}{iz' jz' kz kz' : Bwd K} -> kz <= kz' -> Deal iz' jz' kz' ->
  Sg _ \ iz -> Sg _ \ jz -> iz <= iz' * Deal iz jz kz * jz <= jz'
dealRefine oz dzz = B0 , B0 , oz , dzz , oz
dealRefine (ps os) (ds' de) with dealRefine ps de
... | _ , _ , th , ga , ph = _ , _ , th os , ds' ga , ph
dealRefine (ps os) (d's de) with dealRefine ps de
... | _ , _ , th , ga , ph = _ , _ , th , d's ga , ph os
dealRefine (ps o') (ds' de) with dealRefine ps de
... | _ , _ , th , ga , ph = _ , _ , th o' , ga , ph
dealRefine (ps o') (d's de) with dealRefine ps de
... | _ , _ , th , ga , ph = _ , _ , th , ga , ph o'

TmK : forall {I}(D : I -> Desc I)(kz : Scope I)(k : Kind I) -> Set
TmK D kz (jz => i) = (jz !- TmR D i) / kz

wTmK : forall {I}{D : I -> Desc I}{kz kz' : Scope I} -> kz <= kz' -> {k : Kind I} -> TmK D kz k -> TmK D kz' k
wTmK th {jz => i} t = thin/ t th

record Morph {I}(D : I -> Desc I)(iz kz : Scope I) : Set where
  constructor _<:_$>_
  field
    {leave write} : Scope I
    leaven  : leave <= kz
    fate : Deal leave write iz
    written : All (TmK D kz) write
open Morph


record MorphR {I}(D : I -> Desc I)(iz kz : Scope I) : Set where
  constructor mor
  field
    {leave write} : Scope I
    leaven  : leave <= kz
    fate : DealR leave write iz
    written : [! SpD write !! TmRR D !]RR / kz
open MorphR

morphRefine : forall {I}{D : I -> Desc I}{iz iz' kz}(th : iz <= iz')(m : Morph D iz' kz) ->
  Sg (Morph D iz kz) \ m' -> write m' <= write m
morphRefine {I}{D}{iz}{iz'}{jz} ps (th' <: de $> pz) with dealRefine ps de
... | le , wr , th , ga , ph = (th <&= th') <: ga $> (ph <?= pz) , ph

morR : forall {I}{D : I -> Desc I}{hz iz iz' kz}(th : iz <= iz') ->
       (Sg (MorphR D iz' kz) \ m -> write m <= hz) -> (Sg (MorphR D iz kz) \ m -> write m <= hz)
morR ps (mor th (psl , psr , d') sz , ze) with mkINT psl ps | mkINT psr ps | lemma (\ a b -> Tt (a <+> b)) psl psr d' ps
... | _ , psll , pslr , ql | _ , psrl , psrr , qr | d = mor (psll <&= th) (pslr , psrr , d) (psrl <??= sz) , psrl <&= ze 


data Hered {I}(kz : Scope I) : Set where
  hered : (forall {jz i} -> (jz => i) <- kz -> Hered jz) -> Hered kz
here : forall {I}{kz : Scope I} -> Hered kz -> forall {jz i} -> (jz => i) <- kz -> Hered jz
here (hered h) = h

inherit : forall {I}(kz : Scope I) -> Hered kz
inherit B0 = hered \ ()
inherit (kz - (jz => i)) = hered \  {
  (x os) -> inherit jz              ;
  (x o') -> here (inherit kz) x     }

spAll :  forall {I}{D : I -> Desc I} jz {kz : Scope I} -> [! SpD jz !! TmR D !]R / kz -> All (TmK D kz) jz
spAll B0 (<> ^ th) = B0
spAll (jz - (iz => i)) ((ts <[ ch ]> t) ^ th) = spAll jz (ts ^ (lope ch <&= th)) - (t ^ (rope ch <&= th))

dealL : forall {K}{iz : Bwd K} -> Deal iz B0 iz
dealL {iz = B0} = dzz
dealL {iz = _ - _} = ds' dealL
deal+L : forall {K}{iz jz kz}(lz : Bwd K) -> Deal iz jz kz -> Deal (iz ++ lz) jz (kz ++ lz)
deal+L B0 de = de
deal+L (lz - l) de = ds' (deal+L lz de)
dealLR : forall {K}{iz jz : Bwd K} -> Deal iz jz (iz ++ jz)
dealLR {jz = B0} = dealL
dealLR {jz = _ - _} = d's dealLR

leftCover : forall {K}(kz : Bwd K) -> Pairwise (\ a b -> Tt (a <+> b)) (oi {kz = kz}) oe
leftCover B0 = <>
leftCover (kz - k) = leftCover kz , <>
left+Cover : forall {K iz jz kz}(th : iz <= kz)(ph : jz <= kz) ->
  Pairwise (\ a b -> Tt (a <+> b)) th ph ->  (lz : Bwd K) ->
  Pairwise (\ a b -> Tt (a <+> b)) (th <++= oi {kz = lz}) (ph <++= oe {kz = lz})
left+Cover th ph c B0 = c
left+Cover th ph c (lz - l) = left+Cover th ph c lz , <>

dealLR' : forall {K}(iz jz : Bwd K) -> DealR iz jz (iz ++ jz)
dealLR' iz B0 = oi , oe , leftCover iz
dealLR' iz (jz - j) with dealLR' iz jz
... | th , ph , c = th o' , ph os , c , <>

morphWeak : forall {I}{D : I -> Desc I}{iz kz iz' kz'} -> Morph D iz kz -> iz' <= kz' -> Morph D (iz ++ iz') (kz ++ kz')
morphWeak {iz' = iz'}{kz' = kz'} (th <: de $> tz) ph = (th <++= ph) <: deal+L iz' de $> all (wTmK (oi <++= oe {kz = kz'})) tz

morWk : forall {I}{D : I -> Desc I}{hz iz kz iz' kz'} ->
        (Sg (MorphR D iz kz) \ m -> write m <= hz) -> iz' <= kz' -> (Sg (MorphR D (iz ++ iz') (kz ++ kz')) \ m -> write m <= hz)
morWk (mor th (thl , thr , c) (sz ^ ps) , ze) ph =
  mor (th <++= ph)
      ((thl <++= oi {kz = src ph}) , (thr <++= oe {kz = src ph}) , left+Cover thl thr c (src ph))
      (sz ^ (ps <++= oe {kz = trg ph}))
  , ze

act : forall {I}{D : I -> Desc I}{hz iz kz i} -> (m : Morph D iz kz) -> write m <= hz -> Hered hz -> TmR D i iz -> TmR D i / kz
acts : forall {I}{D : I -> Desc I}{hz iz kz} T -> (m : Morph D iz kz) -> write m <= hz -> Hered hz -> [! T !! TmR D !]R iz -> [! T !! TmR D !]R / kz
act m th h (# (only <[ ch ]> ts)) with morphRefine (lope ch) m | morphRefine (rope ch) m
act m th h (# {jz = jz} (only <[ ch ]> ts)) | ml , thl | mr , thr with acts (SpD jz) mr (thr <&= th) h ts
act m th h (# {jz} (only <[ ch ]> ts)) | leaven <: ds' dzz $> written , thl | mr , thr | ts' = map/ # (vaR leaven ,R ts')
act m th (hered h) (# {jz} (only <[ ch ]> ts)) | leaven <: d's dzz $> (B0 - ((ps \\ t) ^ ph)) , thl | mr , thr | ts' =
  act (ph <: dealLR $> (ps <?= spAll jz ts')) ps (h (thl <&= th)) t
act {D = D}{i = i} m th h [ ts ] = map/ [_] (acts (D i) m th h ts)
acts (RecD (jz => i)) m th h (ph \\ t) = jz \\R act (morphWeak m ph) th h t
acts (SgD S T) m th h (s , t) = map/ (s ,_) (acts (T s) m th h t)
acts OneD m th h <> = <>R
acts (S *D T) m th h (s <[ ch ]> t) with morphRefine (lope ch) m | morphRefine (rope ch) m
... | ml , thl | mr , thr = acts S ml (thl <&= th) h s ,R acts T mr (thr <&= th) h t

actR : forall {I}{D : I -> Desc I}{hz iz kz i} -> (Sg (MorphR D iz kz) \ m -> write m <= hz) -> Hered hz -> TmRR D i iz -> TmRR D i / kz
actsR : forall {I}{D : I -> Desc I}{hz iz kz} T -> (Sg (MorphR D iz kz) \ m -> write m <= hz) -> Hered hz -> [! T !! TmRR D !]RR iz -> [! T !! TmRR D !]RR / kz
actR m h (# {jz} ((only ^ thl) <-> (tz ^ thr) ! _)) with morR thl m | actsR (SpD jz) (morR thr m) h tz
actR m h (# {jz} ((only ^ thl) <-> tz ^ thr ! _)) | mor ph (dl os , dr os , _ , ()) sz , ze | tz'
actR m h (# {jz} ((only ^ thl) <-> tz ^ thr ! _)) | mor ph (oz os , oz o' , <> , <>) _ , ze | tz' =
  map/ # (vaR ph ,RR tz')
actR m (hered h) (# {jz} ((only ^ thl) <-> tz ^ thr ! _)) | mor _ (oz o' , oz os , <> , <>) ((_ <-> (ph \\ s) ^ ps' ! _) ^ ps) , ze | tz' =
  actR (mor (ps' <&= ps) (dealLR' (src ps') (src ph)) (ph <??= tz') , ph) (h ze) s
actR m h (# {jz} ((only ^ thl) <-> tz ^ thr ! _)) | mor ph (dl o' , dr o' , _ , ()) sz , ze | tz'
actR {D = D}{i = i} m h [ ts ] = map/ [_] (actsR (D i) m h ts)
actsR (RecD (jz => i)) m h (ph \\ t) = jz \\R actR (morWk m ph) h t
actsR (SgD S T) m h (s , t) = map/ (s ,_) (actsR (T s) m h t)
actsR OneD m h <> = <>R
actsR (S *D T) m h ((s ^ th) <-> (t ^ ph) ! _) = actsR S (morR th m) h s ,RR actsR T (morR ph m) h t

co : forall {I}{D : I -> Desc I}{iz jz kz} -> MorphR D iz jz -> MorphR D jz kz -> MorphR D iz kz
co (mor ph (thl , thr , c) (sz ^ ps)) m1 with morR ph (m1 , oi) | actsR (SpD (src thr)) (morR ps (m1 , oi)) (inherit _) sz
... | mor ph1 (thl1 , thr1 , c1) (sz1 ^ ps1) , _ | sz0 ^ ps0 = mor ph1 (thl1 <&= thl , {!!} , {!!}) {!!}
\end{spec}

%endif

\bibliographystyle{eptcs}
\bibliography{EGTBS}
\end{document}

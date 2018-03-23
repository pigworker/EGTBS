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

%if False
\begin{code}
module EGTBS where
\end{code}
%endif

%format Sg = "\D{\Upsigma}"
%format * = "\F{\times}"
%format _*_ = _ * _
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format , = "\C{,}"
%format _,_ = _ , _
%if False
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

data Zero : Set where
record One : Set where constructor <>

data Two : Set where ff tt : Two
not : Two -> Two
not ff = tt
not tt = ff
_/\_ _\/_ _<+>_ : Two -> Two -> Two
b /\ ff = ff
b /\ tt = b
b \/ ff = b
b \/ tt = tt
ff <+> b = b
tt <+> b = not b

Tt : Two -> Set
Tt ff = Zero
Tt tt = One
\end{code}
%endif

\begin{document}
\maketitle

This paper gives a nameless \emph{co}-de-Bruijn representation of syntax with
binding. It owes a great deal to the work of Pollack and Sato
\textbf{[citation]}
on canonical representation of
variable binding by mapping the use sites of each variable.

The key to any nameless representation of syntax is how it manages the way, at
a variable usage site, we choose to use \emph{one} variable and thus, implicitly
not any of the others in scope. The business of selecting from variables in
scope may, in general, be treated by considering how to embed the selection into
the whole scope.


\section{\textbf{OPE}: The Category of Order-Preserving Embeddings}

A \emph{scope} will be given by a backward (or `snoc') list giving the \emph{kinds}
of variables.

%format where = "\mathkw{where}"
%format Set = "\D{Set}"
%format Bwd = "\D{Bwd}"
%format B0 = "\C{[]}"
%format - = "\C{\mbox{{}-}\!,}"
%format _-_ = _ - _

\begin{code}
data Bwd (K : Set) : Set where
  B0   : Bwd K
  _-_  : Bwd K -> K -> Bwd K
infixl 7 _-_
\end{code}

Scopes constitute the objects of a category whose arrows are the order-preserving
embeddings, or `thinnings'. I write the step constructors postfix, as thinnings
(like contexts) grow on the right.

\newcommand{\apo}{\mbox{'}}
%format <= = "\D{\le}"
%format _<=_ = _ <= _
%format oz = "\C{oz}"
%format os = "\C{os}"
%format o' = "\C{o\apo}"
%format _o' = _ o'
%format _os = _ os
\begin{code}
data _<=_ {K} : Bwd K -> Bwd K -> Set where
  oz   :                                          B0      <=       B0
  _os  : forall {iz jz k} ->  iz <= jz ->  (  iz  -   k)  <=  (jz  -   k)
  _o'  : forall {iz jz k} ->  iz <= jz ->     iz          <=  (jz  -   k)

infixl 8 _os _o'
\end{code}

\begin{code}
src trg : forall {K}{iz jz : Bwd K} -> iz <= jz -> Bwd K
src {iz = iz} th = iz
trg {jz = jz} th = jz
\end{code}


Every scope has the identity thinning, and thinnings compose (diagramatically).
%format oi = "\F{oi}"
%format <&= = "\F{\fatsemi}"
%format _<&=_ = _ <&= _
%format th = "\V{\theta}"
%format ph = "\V{\phi}"
%format ps = "\V{\psi}"

\noindent
\parbox[t]{3in}{
\begin{code}
oi :  forall {K}{kz : Bwd K} ->
      kz <= kz
oi {kz = B0}      = oz
oi {kz = iz - k}  = oi os -- |os| preserves |oi|
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

It is worth noting at this stage that context extension, |(_ - k)|,
on objects extends to a functor, acting on arrows by |os|, with
the functor laws holding definitionally. Let us refer to this
functor as \emph{weakening}.

%format == = "\D{=\!\!=}"
%format _==_ = _ == _
%if False
\begin{code}
data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
infixr 6 _==_
infixr 7 _<&=_
infixr 6 _<=_
\end{code}
%endif

The categorical laws are provable by functional inductions omitted
for lack of incident.
%format law-oi<&= = "\F{law-}" oi <&=
%format law-<&=oi = "\F{law-}" <&= oi
%format law-<&=<&= = "\F{law-}" <&= <&=
\begin{code}
law-oi<&=   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->
               oi <&= th == th
law-<&=oi   :  forall {K}{iz jz : Bwd K}        (th : iz <= jz) ->
               th <&= oi == th
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

Let us refer to this category as $\textbf{OPE}$. We shall unpack more
of its structure later, but let us have an example.

As one might expect, order-preserving embeddings have a strong
antisymmetry property. The \emph{only} invertible arrows are the
identities.
%format antisym = "\F{antisym}"
\begin{code}
antisym :  forall {K}{iz jz : Bwd K}(th : iz <= jz)(ph : jz <= iz) ->
           Sg (iz == jz) \ { refl -> th == oi * ph == oi }
\end{code}
Note that we must match on the proof of |iz == jz| even to claim
that |th| and |ph| are the identity.
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

A simple consequence is that only the identity has the same source
and target.
%format law-oi = "\F{law-oi}"
\begin{code}
law-oi : forall {K}{kz : Bwd K}(th : kz <= kz) -> th == oi
law-oi th with antisym th th
law-oi .oi | refl , refl , refl = refl
\end{code}

\section{De Bruijn Syntax via OPE}

It is not unusual to find natural numbers as bound variables, perhaps
with some bound enforced by typing, either by an inequality or by using
a `finite set of size $n$' construction, often called `Fin'. However, we
may also see scope membership as exactly singleton embedding:
%format <- = "\F{\leftarrow}"
%format _<-_ = _ <- _
\begin{code}
_<-_ : forall {K} -> K -> Bwd K -> Set
k <- kz = B0 - k <= kz
\end{code}

Now we may give the well scoped but untyped
de Bruijn $\lambda$-terms using membership for
variables.
%format One = "\D{One}"
%format <> = "\C{\langle\rangle}"
%format LamTm = "\D{LamTm}"
%format var = "\C{\scriptstyle\#}"
%format $ = "\C{\scriptstyle\$}"
%format _$_ = _ $ _
%format lam = "\C{\uplambda}"
\begin{code}
data LamTm (iz : Bwd One) : Set where
  var  : <> <- iz  ->             LamTm iz
  _$_  : LamTm iz -> LamTm iz ->  LamTm iz
  lam  : LamTm (iz - <>) ->       LamTm iz
infixl 5 _$_
\end{code}

Variables are represented by pointing, which saves any bother about choosing
names for them. We have just one way to encode a given term in a given scope.
It is only when we point to one of the variables in scope that we exclude
the possibility of choosing any of the others. That is to say de Bruijn index
representation effectively uses thinnings to discard unwanted variables at
the \emph{latest} possible opportunity, in the \emph{leaves} of the syntax trees.

Note the way the scope index |iz| is used in the data type: it occurs as the
target of a thinning in the |var| constructor and acted on by the weakening
functor. Correspondingly, thinnings act functorially on terms, ultimately
by postcomposition, but because terms keep their thinnings at their leaves,
we must hunt the entire tree to find them, weakening as we go under |lam|.
%format ^L = "\F{\uparrow}"
%format _^L_ = _ ^L _
\begin{code}
_^L_ : forall {iz jz} -> LamTm iz -> iz <= jz -> LamTm jz
var i    ^L th = var (i <&= th)
(f $ s)  ^L th = (f ^L th) $ (s ^L th)
lam t    ^L th = lam (t ^L th os)
infixl 7 _^L_
\end{code}

The point of this paper is to consider the other canonical placement of the
thinnings, nearest the \emph{roots} of syntax trees, discarding unwanted variables
at the \emph{earliest} possible opportunity.


\section{Things-with-Thinnings}

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
record _/_ {K}(T : Bwd K -> Set)(scope : Bwd K) : Set where
  constructor _^_
  field
    {support}  : Bwd K
    thing      : T support
    thinning   : support <= scope
infixl 7 _^_
open _/_
\end{code}

The categorical structure of thinnings induces a monadic structure on
things-with-thinnings.
%format map/ = "\F{map/}"
%format unit/ = "\F{unit/}"
%format mult/ = "\F{mult/}"
%format thin/ = "\F{thin/}"
\begin{code}
map/ :  forall {K S T} ->
        ({kz : Bwd K} -> S kz -> T kz) ->
        {kz : Bwd K} -> S / kz -> T / kz
map/ f (s ^ th) = f s ^ th

unit/ : forall {K T}{kz : Bwd K} -> T kz -> T / kz
unit/ t = t ^ oi

mult/ : forall {K T}{kz : Bwd K} -> (T /_) / kz -> T / kz
mult/ (t ^ th ^ ph) = t ^ (th <&= ph)
\end{code}

In particular, things-with-thinnings are easy to thin further, indeed,
parametrically so.
\begin{code}
thin/ : forall {K T}{iz jz : Bwd K} -> T / iz -> iz <= jz -> T / jz
thin/ t th = mult/ (t ^ th)
\end{code}

However, it is not enough to allow a thinning at the root: |LamTm / iz|
is a poor representation of terms over |iz|, as we may choose whether
to discard unwanted variables either at root or at leaves. To recover a
canonical positioning of thinnings, we must enforce the property that a
term's |support| is \emph{relevant}: if a variable is not discarded by the
|thinning|, it \emph{must} be used in the |thing|. Or as Spike Milligan
put it, `Everybody's got to be somewhere.'.


\section{Slices of Thinnings}

The thing-with-thinning construction makes crucial use of `arrows into
|scope| from some |support|', which we might learn to recognize as objects
in the slice category $\textbf{OPE}/|scope|$. By way of a reminder, if
$\mathbb{C}$ is a category and $I$ one of its objects, the slice category
$\mathbb{C}/I$ has as its objects pairs $(S, f)$, where $S$ is an object
of $\mathbb{C}$ and $f : S \to I$ is an arrow in $\mathbb{C}$. A morphism
in $(S, f) \to (T, g)$ is some $h : S \to T$ such that $f = h;g$.
\[\xymatrix{
  S \ar[rr]^h \ar[dr]^f &   & T \ar[dl]^g \\
    & I \ar@@{.}@@(ul,dl)[ul]\ar@@{.}@@(ul,ur)[ul]
        \ar@@{.}@@(ur,dr)[ur]\ar@@{.}@@(ur,ul)[ur]
        &
}\qquad\mbox{$h$ is an arrow from $(S,f)$ to $(T,g)$}\]

In our case, selections from `what's in scope' are related by inclusion.
However, we also acquire some crucial colimit (zero, sum) structure, which
will allow us to recover limit (one, product) structure for
things-with-thinnings.
The empty scope gives us an initial object in the slice.
%format oe = "\F{oe}"
\begin{code}
oe : forall {K}{kz : Bwd K} -> B0 <= kz
oe {kz = B0}      = oz
oe {kz = iz - k}  = oe o'
\end{code}
We may readily show that the initial object is unique.
%format law-oe = "\F{law-}" oe
\begin{code}
law-oe : forall {K}{kz : Bwd K}(th : B0 <= kz) -> th == oe
\end{code}
%if False
\begin{code}
law-oe oz = refl
law-oe (th o') rewrite law-oe th = refl
\end{code}
%endif
and thus establish that there is a unique arrow from $(|B0|,|oe|)$ to
any other arrow in the slice.

The initial object gives us a way to make \emph{constants} with empty support,
i.e., noting that no variables are \emph{relevant}.
%format OneR = One "_{R}"
%format <>R = "\F{\langle\rangle}_{R}"
\begin{code}
data OneR {K} : Bwd K -> Set where -- `$R$' for \emph{relevant}
  <> : OneR B0

<>R : forall {K}{kz : Bwd K} -> OneR / kz
<>R = <> ^ oe
\end{code}

Now, suppose we wish to construct pairs in a relevant way, ensuring that every variable in scope
is used at least once. We shall need something like the following.
%format *R = "\D{*}_R"
%format _*R_ = _ *R _
%format <[ = "\C{\langle\!{}[}"
%format ]> = "\C{]\!{}\rangle}"
%format _<[_]>_ = _ <[ _ ]> _
%format lsupport = "\F{lsupport}"
%format rsupport = "\F{rsupport}"
%format outl = "\F{outl}"
%format director = "\F{director}"
%format outr = "\F{outr}"
%format Cop = "\D{Cop}"
%format ,R = "\F{,}_{R}"
%format _,R_ = _ ,R _
\begin{spec}
record _*R_ {K}(S T : Bwd K -> Set)(scope : Bwd K) : Set where
  constructor _<[_]>_
  field
    {lsupport rsupport}  : Bwd K
    outl                 : S lsupport
    director             : Cop lsupport rsupport scope
    outr                 : T rsupport
\end{spec}
Each component has its own support, but we must police the invariant
that these two supports together cover the whole |scope|, and also
know into which component to direct each variable. We should
be able to recover ordinary pairing for things-with-thinnings,
\begin{spec}
_,R_ : forall {K S T}{kz : Bwd K} -> S / kz -> T / kz -> (S *R T) / kz
\end{spec}
Both components have some of the |kz| as support. The support of the
pair is the smallest subscope of |kz| that embeds the support of the
components. Categorically, it is the coproduct of objects in the slice
category. To code up the notion, we shall need to express the relationship
between the supports of the components and the support of the pair: everything
in the latter should appear in at least one of the former, but possibly
both. In other words, everybody's got to be somewhere.

%format czz = "\C{czz}"
%format cs' = "\C{cs\apo}"
%format c's = "\C{c\apo s}"
%format css = "\C{css}"
%format _cs' = _ cs'
%format _c's = _ c's
%format _css = _ css
\begin{code}
data Cop {K} : Bwd K -> Bwd K -> Bwd K -> Set where
  czz    :                                         Cop    B0            B0           B0
  _cs'   : forall {iz jz kz k} -> Cop iz jz kz ->  Cop (  iz - k  )     jz        (  kz - k)
  _c's   : forall {iz jz kz k} -> Cop iz jz kz ->  Cop    iz         (  jz - k)   (  kz - k)
  _css   : forall {iz jz kz k} -> Cop iz jz kz ->  Cop (  iz - k  )  (  jz - k)   (  kz - k)
infixl 8 _cs' _c's _css
\end{code}

Of course, whenever we have a |Cop iz jz kz| we must have embeddings |iz <= kz| and |jz <= kz|.
%format lope = "\F{lope}"
%format rope = "\F{rope}"
%format ch = "\V{\chi}"

\noindent
\parbox{3.2in}{
\begin{code}
lope :  forall {K}{iz jz kz : Bwd K} ->
        Cop iz jz kz -> iz <= kz
lope      czz   =            oz
lope (ch  cs')  = (lope ch)  os
lope (ch  c's)  = (lope ch)  o'
lope (ch  css)  = (lope ch)  os
\end{code}}
\hfill
\parbox{3.2in}{
\begin{code}
rope :  forall {K}{iz jz kz : Bwd K} ->
        Cop iz jz kz -> jz <= kz
rope      czz   =            oz
rope (ch  cs')  = (rope ch)  o'
rope (ch  c's)  = (rope ch)  os
rope (ch  css)  = (rope ch)  os
\end{code}}

Let us compute coproducts! A thinning is, in effect, a vector of `used or not' bits. We are computing their
pointwise disjunction `used on either side' in a proof-relevant way. Specifically, we compute some
|ch ^ ps : Cop iz jz / kz| so that $(\cdot,|ps|)$ is the coproduct object in the slice over |kz|, with
|lope ch| and |rope ch| the two injections. We are thus obliged to show that these injections are
arrows in the slice, which amounts to factoring both of our original thinning through |ps|.
%format cop = "\F{cop}"
%format refl = "\C{refl}"
%format . = "."
\begin{code}
cop :  forall {K}{iz jz kz : Bwd K}
       (th : iz <= kz)(ph : jz <= kz) ->  Sg (Cop iz jz / kz) \ { (ch ^ ps) ->
                                          th == lope ch <&= ps * ph == rope ch <&= ps }
cop      oz        oz                                                      =     czz  ^     oz , refl , refl
cop (th  os)  (ph  os) with cop th ph
cop (.(lope ch <&= ps) os) (.(rope ch <&= ps) os) | ch ^ ps , refl , refl  = ch  css  ^ ps  os , refl , refl
cop (th  os)  (ph  o') with cop th ph
cop (.(lope ch <&= ps) os) (.(rope ch <&= ps) o') | ch ^ ps , refl , refl  = ch  cs'  ^ ps  os , refl , refl
cop (th  o')  (ph  os) with cop th ph
cop (.(lope ch <&= ps) o') (.(rope ch <&= ps) os) | ch ^ ps , refl , refl  = ch  c's  ^ ps  os , refl , refl
cop (th  o')  (ph  o') with cop th ph
cop (.(lope ch <&= ps) o') (.(rope ch <&= ps) o') | ch ^ ps , refl , refl  = ch       ^ ps  o' , refl , refl
\end{code}

Observe that wherever one of the input thinnings has an |os|, meaning that a variable is used on one side or the other,
we grow the coproduct witness and ensure that its thinning has an |os| to keep the variable available. However, when
both input thinnings have |o'|, meaning that neither side uses the variable, the coproduct remains the same and its
thinning gets an |o'| to discard the variable.

%if False
\begin{code}
record _*R_ {K}(S T : Bwd K -> Set)(scope : Bwd K) : Set where
  constructor _<[_]>_
  field
    {lsupport rsupport}  : Bwd K
    outl                 :      S  lsupport
    director             : Cop     lsupport     rsupport  scope
    outr                 :                   T  rsupport
\end{code}
infixr 4 _*R_
%endif

\begin{code}
_,R_ : forall {K S T}{kz : Bwd K} -> S / kz -> T / kz -> (S *R T) / kz
(s ^ th) ,R (t ^ ph) with cop th ph
(s ^ .(lope ch <&= ps)) ,R (t ^ .(rope ch <&= ps)) | ch ^ ps , refl , refl = (s <[ ch ]> t) ^ ps
\end{code}


\begin{code}
Pairwise :  (Two -> Two -> Set) ->
            forall {K}{iz jz kz : Bwd K} -> iz <= kz -> jz <= kz -> Set
Pairwise F oz oz = One
Pairwise F (th os) (ph os) = Pairwise F th ph * (F tt tt)
Pairwise F (th os) (ph o') = Pairwise F th ph * (F tt ff)
Pairwise F (th o') (ph os) = Pairwise F th ph * (F ff tt)
Pairwise F (th o') (ph o') = Pairwise F th ph * (F ff ff)

cong : forall {S T : Set}(f : S -> T){x y : S} -> x == y -> f x == f y
cong f refl = refl

mkINT : forall {K}{iz jz kz : Bwd K}(th : iz <= kz)(ph : jz <= kz) ->
        Sg _ \ hz -> Sg (hz <= iz) \ th' -> Sg (hz <= jz) \ ph' ->
        (th' <&= th) == (ph' <&= ph)
mkINT oz oz = _ , oz , oz , refl
mkINT (th' os) (ph' os) with mkINT th' ph'
... | _ , th , ph , q = _ , th os , ph os , cong _os q
mkINT (th' os) (ph' o') with mkINT th' ph'
... | _ , th , ph , q = _ , th o' , ph , cong _o' q
mkINT (th' o') (ph' os) with mkINT th' ph'
... | _ , th , ph , q = _ , th , ph o' , cong _o' q
mkINT (th' o') (ph' o') with mkINT th' ph'
... | _ , th , ph , q = _ , th , ph , cong _o' q

COP : forall {K}(iz jz kz : Bwd K) -> Set
COP iz jz kz = Sg (iz <= kz) \ th -> Sg (jz <= kz) \ ph -> Pairwise (\ a b -> Tt (a \/ b)) th ph

DealR : forall {K}(iz jz kz : Bwd K) -> Set
DealR iz jz kz = Sg (iz <= kz) \ th -> Sg (jz <= kz) \ ph -> Pairwise (\ a b -> Tt (a <+> b)) th ph

mkCOP : forall {K}{iz jz kz : Bwd K}(th' : iz <= kz)(ph' : jz <= kz) ->
        Sg (COP iz jz / kz) \ { ((th , ph , c) ^ ps) ->
        th' == th <&= ps * ph' == ph <&= ps }
mkCOP oz oz = (oz , oz , _) ^ oz , refl , refl
mkCOP (th' os) (ph' os) with mkCOP th' ph'
mkCOP (.(th <&= ps) os) (.(ph <&= ps) os) | (th , ph , c) ^ ps , refl , refl = (th os , ph os , c , <>) ^ ps os , refl , refl
mkCOP (th' os) (ph' o') with mkCOP th' ph'
mkCOP (.(th <&= ps) os) (.(ph <&= ps) o') | (th , ph , c) ^ ps , refl , refl = (th os , ph o' , c , <>) ^ ps os , refl , refl
mkCOP (th' o') (ph' os) with mkCOP th' ph'
mkCOP (.(th <&= ps) o') (.(ph <&= ps) os) | (th , ph , c) ^ ps , refl , refl = (th o' , ph os , c , <>) ^ ps os , refl , refl
mkCOP (th' o') (ph' o') with mkCOP th' ph'
mkCOP (.(th <&= ps) o') (.(ph <&= ps) o') | (th , ph , c) ^ ps , refl , refl = (th , ph , c) ^ ps o' , refl , refl

record _*RR_ {K}(S T : Bwd K -> Set)(scope : Bwd K) : Set where
  constructor _<->_!_
  field
    outll                 : S / scope
    outrr                 : T / scope
    cover                 : Pairwise (\ a b -> Tt (a \/ b)) (thinning outll) (thinning outrr)

_,RR_ : forall {K S T}{kz : Bwd K} -> S / kz -> T / kz -> (S *RR T) / kz
(s ^ th') ,RR (t ^ ph') with mkCOP th' ph'
(s ^ .(th <&= ps)) ,RR (t ^ .(ph <&= ps)) | (th , ph , c) ^ ps , refl , refl = ((s ^ th) <-> (t ^ ph) ! c) ^ ps

lemma : forall (F : Two -> Two -> Set){K}{iz jz kz kz' : Bwd K}(th : iz <= kz')(ph : jz <= kz') -> Pairwise F th ph ->
        (ps : kz <= kz') ->
        let  (iz' , thl , thr , ql) = mkINT th ps
             (jz' , phl , phr , qr) = mkINT ph ps
        in   Pairwise F thr phr
lemma F oz oz z oz = <>
lemma F (th os) (ph os) (x , y) (ps os) = lemma F th ph x ps , y
lemma F (th os) (ph os) (x , y) (ps o') = lemma F th ph x ps
lemma F (th os) (ph o') (x , y) (ps os) = lemma F th ph x ps , y
lemma F (th os) (ph o') (x , y) (ps o') = lemma F th ph x ps
lemma F (th o') (ph os) (x , y) (ps os) = lemma F th ph x ps , y
lemma F (th o') (ph os) (x , y) (ps o') = lemma F th ph x ps
lemma F (th o') (ph o') (x , y) (ps os) = lemma F th ph x ps , y
lemma F (th o') (ph o') (x , y) (ps o') = lemma F th ph x ps


\end{code}



\section{Monoidal Structure of Order-Preserving Embeddings}

In order to talk about binding, we need to talk about context extension.
We have seen extension by a single `snoc', but simultaneous binding also
makes sense. Concatenation induces a monoidal structure on scopes.

%format ++ = "\F{+\!\!+}"
%format _++_ = _ ++ _
\begin{code}
_++_ : forall {K} -> Bwd K -> Bwd K -> Bwd K
kz ++ B0        = kz
kz ++ (iz - j)  = (kz ++ iz) - j
infixl 7 _++_
\end{code}

We can extend this monoidal structure to arrows:
%format <++= = ++ "_{" <= "}"
%format _<++=_ = _ <++= _
\begin{code}
_<++=_ :  forall {K}{iz jz iz' jz' : Bwd K} ->
          iz <= jz -> iz' <= jz' -> (iz ++ iz') <= (jz ++ jz')
th <++=      oz   =    th
th <++= (ph  os)  = (  th <++= ph) os
th <++= (ph  o')  = (  th <++= ph) o'
\end{code}

Moreover, given a embedding into a concatenated scope, we can split it
into the local end and the global end.
%format -! = "\F{\dashv}"
%format _-!_ = _ -! _
\begin{code}
_-!_ : forall {K}{iz kz}(jz : Bwd K)(ps : iz <= (kz ++ jz)) ->
       Sg (Bwd K) \ kz' -> Sg (Bwd K) \ jz' -> Sg (kz' <= kz) \ th -> Sg (jz' <= jz) \ ph ->
       Sg (iz == (kz' ++ jz')) \ { refl -> ps == (th <++= ph) }
B0        -! ps      = _ , _ , ps , oz , refl , refl
(kz - k) -! (ps os)             with kz -! ps
(kz - k) -! (.(th <++= ph) os)  | _ , _ , th , ph , refl , refl = _ , _ , th , ph os , refl , refl
(kz - k) -! (ps o')             with kz -! ps
(kz - k) -! (.(th <++= ph) o')  | _ , _ , th , ph , refl , refl = _ , _ , th , ph o' , refl , refl
\end{code}

Thus equipped, we can say how to bind some variables. The key is to say
at the binding site which of the bound variables will actually be used:
if they are not used, we should not even bring them into scope.

%format !- = "\D{\vdash}"
%format _!-_ = _ !- _
%format \\ = "\C{\fatbslash}"
%format _\\_ = _ \\ _
\begin{code}
data _!-_ {K}(jz : Bwd K)(T : Bwd K -> Set)(kz : Bwd K) : Set where
  _\\_ : forall {iz} -> iz <= jz -> T (kz ++ iz) -> (jz !- T) kz
infixr 5 _!-_
infixr 6 _\\_
\end{code}

We have a smart constructor for thinned bindings:
%format \\R = "\F{\fatbslash}_R"
%format _\\R_ = _ \\R _
\begin{code}
_\\R_ : forall {K T}{kz}(jz : Bwd K) -> T / (kz ++ jz) -> (jz !- T) / kz
jz \\R (t ^ ps) with jz -! ps
jz \\R (t ^ .(th <++= ph)) | _ , _ , th , ph , refl , refl = (ph \\ t) ^ th
infixr 6 _\\R_
\end{code}

The monoid of scopes is generated from its singletons. By the time we \emph{use}
a variable, it should be the only thing in scope.
%format VaR = "\D{Va}_R"
%format only = "\C{only}"
\begin{code}
data VaR {K}(k : K) : Bwd K -> Set where
  only : VaR k (B0 - k)
\end{code}
The associated smart constructor computes the thinned representation of variables.
%format vaR = "\F{va}_R"
\begin{code}
vaR : forall {K}{k}{kz : Bwd K} -> k <- kz -> VaR k / kz
vaR x = only ^ x
\end{code}


\section{Co-De-Bruijn Representations of Untyped Lambda Calculus}

We can now give the type of lambda terms for which all \emph{free} variables are
relevant as follows.
%format LamTmR = LamTm "_R"
%format app = "\C{app}"
\begin{code}
data LamTmR (kz : Bwd One) : Set where
  var  : VaR <> kz ->               LamTmR kz
  app  : (LamTmR *R LamTmR) kz ->   LamTmR kz
  lam  : (B0 - <> !- LamTmR) kz ->  LamTmR kz
\end{code}

Converting from de Bruijn to co-de-Bruijn representations is easy, given our
smart constructors:
%format lamTmR = "\F{lamTm}_R"
\begin{code}
lamTmR : forall {kz : Bwd One} -> LamTm kz -> LamTmR / kz
lamTmR (var x)  = map/ var  (vaR x)
lamTmR (f $ s)  = map/ app  (lamTmR f ,R lamTmR s)
lamTmR (lam t)  = map/ lam  (_ \\R lamTmR t) 
\end{code}

%format combK = "\F{\mathbb{K}}"
%format combS = "\F{\mathbb{S}}"
For example, the de Bruijn representations of the |K| and |S| combinators are
\begin{code}
combK combS : LamTm B0
combK  = lam (lam (var (oe os o')))
combS  = lam (lam (lam (var (oe os o' o') $ var (oe os) $ (var (oe os o') $ var (oe os)))))
\end{code}

%if False
\begin{code}
codbK codbS : LamTmR / B0
codbK = lam (oz os \\ lam (oz o' \\ var only)) ^ oz

codbS =  lam (oz os \\ lam (oz os \\ lam (oz os \\
                   app (
                     app (var only <[ czz cs' c's ]> var only)
                     <[ czz cs' c's css ]>
                     app (var only <[ czz cs' c's ]> var only))
                 )))
                 ^ oz
\end{code}
%endif
and these become the much more explicit co-de-Bruijn terms
\begin{spec}
lamTmR combK  =  lam (oz os \\ lam (oz o' \\ var only)) ^ oz
lamTmR combS  =  lam (oz os \\ lam (oz os \\ lam (oz os \\
                   app (
                     app (var only <[ czz cs' c's ]> var only)
                     <[ czz cs' c's css ]>
                     app (var only <[ czz cs' c's ]> var only))
                 )))
                 ^ oz
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
Scope : Set -> Set
data Kind (I : Set) : Set where
  _=>_ : Scope I -> I -> Kind I
infix 6 _=>_
Scope I = Bwd (Kind I)
\end{code}
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
\[
|D : I -> Desc I|
\]
where |Desc| is as follows:
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
\begin{code}
data Decide (X : Set) : Set where
  yes  : X ->            Decide X
  no   : (X -> Zero) ->  Decide X

record Datoid : Set1 where
  field
    Data    : Set
    decide  : (x y : Data) -> Decide (x == y)
open Datoid
\end{code}
%if False
\begin{code}
data Desc (I : Set) : Set1 where
  RecD   : Kind I ->                              Desc I
  SgD    : (S : Datoid) -> (Data S -> Desc I) ->  Desc I
  OneD   :                                        Desc I
  _*D_   : Desc I -> Desc I ->                    Desc I
\end{code}
%endif

For our $\lambda$-calculus example, let us have the enumeration
%format LamTag = "\D{LamTag}"
%format LAMTAG = "\F{LAMTAG}"
\begin{code}
data LamTag : Set where app lam : LamTag
LAMTAG : Datoid
Data    LAMTAG = LamTag
decide  LAMTAG app  app  = yes refl
decide  LAMTAG app  lam  = no \ ()
decide  LAMTAG lam  app  = no \ ()
decide  LAMTAG lam  lam  = yes refl
\end{code}
and then take
%format LamD = "\F{Lam}_D"
\begin{code}
LamD : One -> Desc One
LamD <> = SgD LAMTAG \  { app  -> RecD (B0 => <>) *D RecD (B0 => <>)
                        ; lam  -> RecD (B0 - (B0 => <>) => <>)
                        }
\end{code}
Note that we do not and cannot include a tag or description for
the use sites of variables in terms: use of variables in scope
pertains not to the specific syntax, but to the general notion
of what it is to be a syntax.

At use sites, higher-kinded variables must be instantiated with
parameters, just like $t[x]$ in the $\beta$-rule example, above.
We can compute from a given |Scope| the |Desc|ription of the
spine of actual parameters required.
%format SpD = "\F{Sp}_D"
\begin{code}
SpD : forall {I} -> Scope I -> Desc I
SpD      B0      =          OneD
SpD (kz  -   k)  = SpD kz   *D    RecD k
\end{code}


\subsection{Interpreting |Desc| as de Bruijn Syntax}
%format [! = "\F{\llbracket}"
%format !! = "\F{\mid}"
%format !] = "\F{\rrbracket}"
%format [!_!!_!] = [! _ !! _ !]
Let us give the de Bruijn interpretation of our syntax descriptions.
We give meaning to |Desc| in the traditional manner, interpreting
them as strictly positive operators in some |R| which gives the semantics
to |RecD|. We shall `tie the knot', taking a fixpoint, shortly.
\begin{code}
[!_!!_!] : forall {I} -> Desc I -> (I -> Scope I -> Set) -> Scope I -> Set
[! RecD (jz => i)  !! R !] kz = R i (kz ++ jz)
[! SgD S T         !! R !] kz = Sg (Data S) \ s -> [! T s !! R !] kz
[! OneD            !! R !] kz = One
[! S *D T          !! R !] kz = [! S !! R !] kz * [! T !! R !] kz
\end{code}
Note that we work with scope-indexed sets and an index |kz| giving the
kinds of the variables in scope. In recursive positions, the scope
grows by the bindings indicated by the given |Kind|.

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
data Tm {I}(D : I -> Desc I)(i : I)(kz : Scope I) : Set where
  _#$_  : forall {jz} -> (jz => i) <- kz ->  [! SpD jz  !! Tm D !] kz ->  Tm D i kz
  [_]   :                                    [! D i     !! Tm D !] kz ->  Tm D i kz
infixr 5 _#$_
\end{code}

In this setting, |combK| and |combS| become
%format combKD = combK "_D"
%format combSD = combS "_D"
\begin{code}
combKD combSD : Tm LamD <> B0
combKD  =  [ lam ,  [ lam , oe os o' #$ <> ] ]
combSD  =  [ lam ,  [ lam ,  [ lam ,  [ app  , [ app , oe os o' o' #$ <> , oe os #$ <> ]
                                             , [ app , oe os o' #$ <> , oe os #$ <> ]
           ]        ]        ]        ]
\end{code}


\section{Interpreting |Desc| as co-de-Bruijn Syntax}

We may, of course, also interpret |Desc|riptions in co-de-Bruijn style,
enforcing that all variables in scope are relevant, and demanding that
binding sites make clear which variables are to be used. Let us work in
|Scope I -> Set| where practical.
%format !]R = "\F{\rrbracket}"
%format [!_!!_!]R = [! _ !! _ !]R
%format TmR = Tm "_R"
%format # = "\C{\scriptstyle \#}"
\begin{code}
[!_!!_!]R : forall {I} -> Desc I -> (I -> Scope I -> Set) -> Scope I -> Set
[! RecD (jz => i)  !! R !]R = jz !- R i
[! SgD S T         !! R !]R = \ kz -> Sg (Data S) \ s -> [! T s !! R !]R kz
[! OneD            !! R !]R = OneR
[! S *D T          !! R !]R = [! S !! R !]R *R [! T !! R !]R

data TmR {I}(D : I -> Desc I)(i : I)(kz : Scope I) : Set where
  #     : forall {jz} -> (VaR (jz => i) *R  [! SpD jz  !! TmR D !]R)  kz ->  TmR D i kz
  [_]   :                                   [! D i     !! TmR D !]R   kz ->  TmR D i kz
\end{code}

\begin{code}
[!_!!_!]RR : forall {I} -> Desc I -> (I -> Scope I -> Set) -> Scope I -> Set
[! RecD (jz => i)  !! R !]RR = jz !- R i
[! SgD S T         !! R !]RR = \ kz -> Sg (Data S) \ s -> [! T s !! R !]RR kz
[! OneD            !! R !]RR = OneR
[! S *D T          !! R !]RR = [! S !! R !]RR *RR [! T !! R !]RR

data TmRR {I}(D : I -> Desc I)(i : I)(kz : Scope I) : Set where
  #     : forall {jz} -> (VaR (jz => i) *RR  [! SpD jz  !! TmRR D !]RR)  kz ->  TmRR D i kz
  [_]   :                                    [! D i     !! TmRR D !]RR   kz ->  TmRR D i kz
\end{code}

Let us compute co-de-Bruijn terms from de Bruijn terms, generically.
%format code = "\F{code}"
%format codes = "\F{codes}"
%format ,_ = , _
\begin{code}
code   : forall {I}{D : I -> Desc I}{i iz} ->   Tm D i iz ->           TmR D i / iz
codes  : forall {I}{D : I -> Desc I} S {iz} ->  [! S !! Tm D !] iz ->  [! S !! TmR D !]R / iz
code                    (_#$_ {jz} x ts)  = map/ #    (vaR x ,R codes (SpD jz) ts)
code {D = D}{i = i}     [ ts ]            = map/ [_]  (codes (D i) ts)
codes (RecD (jz => i))  t                 = jz \\R code t
codes (SgD S T)         (s , ts)          = map/ (s ,_) (codes (T s) ts)
codes OneD              <>                = <>R
codes (S *D T)          (ss , ts)         = codes S ss ,R codes T ts
\end{code}

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



\begin{code}
data All {K}(P : K -> Set) : Bwd K -> Set where
  B0 : All P B0
  _-_ : forall {kz k} -> All P kz -> P k -> All P (kz - k)

all : forall {K P Q} -> ({k : K} -> P k -> Q k) ->
      {kz : Bwd K} -> All P kz -> All Q kz
all f B0 = B0
all f (pz - p) = all f pz - f p

_<?=_ : forall {K P}{iz jz : Bwd K} -> iz <= jz -> All P jz -> All P iz
oz <?= B0 = B0
(th os) <?= (pz - p) = (th <?= pz) - p
(th o') <?= (pz - p) = th <?= pz

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
\end{code}


\bibliographystyle{eptcs}
\bibliography{EGTBS}
\end{document}

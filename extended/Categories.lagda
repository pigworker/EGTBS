\section{Something Not Entirely Unlike Categories in Type Theory}

%if False
\begin{code}
module Categories where

open import Agda.Primitive renaming (_⊔_ to _\-/_)

open import DeBruijn
open import Thinnings
open import Slime
open import Worry
\end{code}
%endif

What follows is far from perfect. The best that can be said is that it is an
effective pragmatic compromise. Neither is it an unusual recipe. I labour the
point only to teach the craft of the cooking.

A category will have a |Set| of objects and, indexed by source and target objects,
a |Setoid| of arrows.

But there's another catch: type theoretic level. There is no
good reason to believe that the level objects live on is in any way related to the
the level that arrows live on. Agda is particularly bad at supporting
\emph{cumulativity} --- implicit upward flow between levels --- and by `bad', I mean
it just does not. (Coq by contrast, is rather good at it.) Agda forces one to use
level polymorphism instead of cumulativity. The two are poor stablemates, but they
have backed the wrong horse. In the now, the pragmatic policy is to keep the levels
of objects and arrows separate.

%format Level = "\D{Level}"
%format Cat = "\D{Cat}"
%format Obj = "\F{Obj}"
%format Arr = "\F{Arr}"
%format ~> = "\F{\vartriangleright\!}"
%format _~>_ = "\F{" _ "\!}" ~> "\F{\!" _ "}"
%format _~~_ = "\D{" _ "\!}" ~~ "\D{\!" _ "}"
%format id = "\F{\upiota}"
%format - = "\F{\fatsemi}"
%format _-_ = "\F{" _ "\!}" - "\F{\!" _ "}"
%format coex = "\F{coex}"
%format idco = "\F{idco}"
%format coid = "\F{coid}"
%format coco = "\F{coco}"
\begin{definition}[|Cat|egory]
Fix |k|, the level of objects, and |l|, the level of arrows.
%if False
\begin{code}
module _ (k l : Level) where  -- fix |k|, the level of objects,
                              -- and |l|, the level of arrows
\end{code}
%endif

We may then define a notion of |Cat|egory.
\begin{code}
  record Cat : Set (lsuc (k \-/ l)) where
    -- We have a |Set| of |Obj|ects, and a family of |Setoid|s of |Arr|ows.
    field      Obj   :  Set k
               Arr   :  Obj -> Obj -> Setoid l
               -- Agda allows one to pause between |field|s to make \emph{definitions}\ldots
    _~>_ : Obj -> Obj -> Set l
    S ~> T = El (Arr S T)
               -- \ldots and then resume requesting |field|s.
    -- We have identity and composition.
    field      id    :  {-<-}{T : Obj} -> {->-}      T ~> T
               _-_   :  {-<-}{R S T : Obj} -> {->-}  R ~> S -> S ~> T -> R ~> T
    -- Locally define equality of arrows\ldots
    _~~_ : {S T : Obj}(f g : S ~> T) -> Set l
    _~~_ {S}{T} f g = Arr S T :> f ~~ g
    -- \ldots then require the laws.
    field      coex  :  {-<-}{R S T : Obj}{f f' : R ~> S}{g g' : S ~> T} -> {->-}  f ~~ f' -> g ~~ g' -> (f - g) ~~ (f' - g')
               idco  :  {-<-}{S T : Obj}{->-}(f : S ~> T) ->                              (id - f)       ~~  f
               coid  :  {-<-}{S T : Obj}{->-}(f : S ~> T) ->                              (f - id)       ~~  f
               coco  :  {-<-}{R S T U : Obj}{->-}(f : R ~> S)(g : S ~> T)(h : T ~> U) ->  (f - (g - h))  ~~  ((f - g) - h)
\end{code}
%if False
\begin{code}
open Cat
\end{code}
%endif
Note the inevitable necessity of |coex|, the explicit witness that composition
respects the weak notion of equivalence given by |~~|: let us ensure that this
proof is always trivial.
\end{definition}

As a warm-up, let us construct the category of sets and
functions-up-to-pointwise-equality.

\begin{definition}[Pointwise Set]
Every level {l} of the type theoretic hierarchy has a category of sets and
functions, considered up to pointwise equality. The objects in the category
are large, but the arrows are small.
%format SET = "\F{SET}"
\begin{code}
module _ (l : Level) where

  SET : Cat (lsuc l) l
  Obj  SET = Set l
  Arr  SET S T = PI S \ _ -> IN T
  id   SET x      = x
  _-_  SET f g x  = g (f x)
  qe (coex SET {f = f} (eq qf) (eq qg)) x  with f x  | qf x
  ...                                      | _       | r~ = qg _
  qe (idco SET f)      x = r~
  qe (coid SET f)      x = r~
  qe (coco SET f g h)  x = r~
\end{code}
\end{definition}
When giving the extensionality witness for composition, we know only that
its arguments agree pointwise. Fortunately for us, the definition of
composition uses its arguments by invoking them at specific points.

\begin{definition}[Discrete Category]
Every |Set| induces a \emph{discrete category} with its elements for objects
and only identity arrows, given by intensional equality.
%format DISCRETE = "\F{DISCRETE}"
%format splatvr = contraction
%format splateqrv = contraction
%format splateqr = contraction
%if False
\begin{code}
pattern splatvr = <> , r~
pattern splateqrv = eq (r~ , <>)
pattern splateqr = eq r~
module _ {l : Level} where
\end{code}
%endif
\begin{code}
  DISCRETE : (X : Set l) -> Cat l l
  Obj   (DISCRETE X)                          = X
  Arr   (DISCRETE X) x y                      = IN (One {l}) || \ _ -> x ~ y
  id    (DISCRETE X)                          = splatvr
  _-_   (DISCRETE X) splatvr splatvr          = splatvr
  coex  (DISCRETE X) splateqrv splateqrv      = splateqrv
  idco  (DISCRETE X) splatvr                  = splateqrv
  coid  (DISCRETE X) splatvr                  = splateqrv
  coco  (DISCRETE X) splatvr splatvr splatvr  = splateqrv
\end{code}
I make the arrows carry \emph{trivial} information, subject to the \emph{condition}
that source and target are equal. I am therefore not obliged to reason about
equality between equality proofs.
\end{definition}

%format OP = "\F{OP}"
%format Cdot = "\V{C}."
%format C.Obj = Cdot Obj
%format C.Arr = Cdot Arr
%format C.id = Cdot id
%format C.- = Cdot -
%format C.~> = Cdot ~>
%format C.~~ = Cdot ~~
%format C._-_ = Cdot _-_
%format C.coex = Cdot coex
%format C.idco = Cdot idco
%format C.coid = Cdot coid
%format C.coco = Cdot coco
\begin{definition}[Opposite Category]
Fix a category |C|. (The following declaration allows us to refer to its
components as |C.Obj|, and so on.)
\begin{code}
module _ {k l}(C : Cat k l)where
  private module C = Cat C
\end{code}
We construct |OP|, whose objects are those of |C| but whose arrows are reversed,
as follows:
\begin{code}
  OP : Cat k l
  Obj   OP        = C.Obj
  Arr   OP S T    = C.Arr T S
  id    OP        = C.id
  _-_   OP f g    = g C.- f
  coex  OP qf qg  = C.coex qg qf
  idco  OP        = C.coid
  coid  OP        = C.idco
  coco  OP f g h  = eq (Sy (C.Arr _ _) _ _ (qe (C.coco h g f)))
\end{code}
Identities are preserved but composition is flipped. Correspondingly, the
witness to extensionality of composition also flips and the identity absorption
proofs swap over. Associativity of composition relies essentially on the symmetry
of setoid equivalence for the arrows of |C|.

Outside our module, we may now write |OP C| for the opposite category of |C|.
\end{definition}

\begin{definition}[Restricting Objects]
%format OB = "\F{OB}"
One way to construct a \emph{sub}category is to restrict the objects to the
image of a function.
\begin{code}
module _ {k l}(C : Cat k l){k'}{O : Set k'} where
  private module C = Cat C
  OB : (O -> C.Obj) -> Cat k' l
  Obj   (OB f) = O
  Arr   (OB f) S T = C.Arr (f S) (f T)
\end{code}
I omit the remaining fields as they are copied from |C|.
%if False
\begin{code}
  id    (OB f) = C.id
  _-_   (OB f) = C._-_
  coex  (OB f) = C.coex
  idco  (OB f) = C.idco
  coid  (OB f) = C.coid
  coco  (OB f) = C.coco
\end{code}
%endif
\end{definition}

Finally, in this section, let us assemble the jigsaw pieces which make up the
category of thinnings.

\begin{lemma}[Category of Thinnings]
Thinnings form the arrows of a category.
%format THIN = "\F{THIN}"
%format lzero = "\D{0}"
\begin{code}
THIN : Set -> Cat lzero lzero
Obj   (THIN X)                     = Bwd X
Arr   (THIN X) ga de               = IN (ga <= de)
id    (THIN X)                     = io
_-_   (THIN X)                     = _-<=_
coex  (THIN X) splateqr splateqr   = splateqr
idco  (THIN X) th                  = eq (io~ th)
coid  (THIN X) th                  = eq (th ~io)
coco  (THIN X) th ph ps            = eq (assoc th ph ps)
\end{code}
\end{lemma}

Now, the crucial structure that we exploit in codeBruijn programming arises
from the relationship between the discrete category on scopes and the category
of thinnings. That relationship requires us to consider `arrows between categories',
i.e., \emph{functors}.


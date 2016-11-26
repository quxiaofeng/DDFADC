Inductive type :=
| tytop
| tybot
| tyreal
| tysum (l r : type)
| typrod (l r : type)
| tyarr (l r : type).

Infix "~>" := tyarr (at level 55, right associativity).

Inductive term : type -> Type :=
| ttt : term tytop
| texf { T } : term (tybot ~> T)
| tlit : (*Double ->*) term tyreal
| tplus : term (tyarr tyreal (tyreal ~> tyreal))
| tminus : term (tyreal ~> tyreal ~> tyreal)
| tdiv : term (tyreal ~> tyreal ~> tyreal)
| tmult : term (tyreal ~> tyreal ~> tyreal)
| tleft { A B } : term (A ~> (tysum A B))
| tright { A B } : term (B ~> (tysum A B))
| tsummatch { A B C } : term ((tysum A B) ~> (A ~> C) ~> (B ~> C) ~> C)
| tmkprod { A B } : term (A ~> B ~> (typrod A B))
| tzro { A B } : term ((typrod A B) ~> A)
| tfst { A B } : term ((typrod A B) ~> B)
| tapp { A B } (f : term (A ~> B)) (x : term A) : term B
| tS { A B C } : term ((A ~> B ~> C) ~> (A ~> B) ~> (A ~> C))
| tK { A B } : term (A ~> B ~> A)
| tI { A } : term (A ~> A)
| tB { A B C } : term ((B ~> C) ~> (A ~> B) ~> (A ~> C))
| tC { A B C } : term ((A ~> B ~> C) ~> (B ~> A ~> C))
| tW { A B } : term ((A ~> A ~> B) ~> (A ~> B))
| tY { A B } : term (((A ~> B) ~> (A ~> B)) ~> (A ~> B)).

Inductive val : forall { A }, term A -> Prop :=.

Inductive red : forall { A }, term A -> term A -> Prop :=
| rtleft { A B C } a f g :
    red (tapp (tapp (tapp (@tsummatch A B C) (tapp tleft a)) f) g) (tapp f a)
| rtright { A B C } b f g :
    red (tapp (tapp (tapp (@tsummatch A B C) (tapp tright b)) f) g) (tapp g b)
| rtzro { A B } a b : red (tapp tzro (tapp (tapp (@tmkprod A B) a) b)) a
| rtfst { A B } a b : red (tapp tfst (tapp (tapp (@tmkprod A B) a) b)) b
| rtS { A B C } f x arg :
    red (tapp (tapp (tapp (@tS A B C) f) x) arg) (tapp (tapp f arg) (tapp x arg))
| rtK { A B } x y : red (tapp (tapp (@tK A B) x) y) x
| rtI { A } x : red (tapp (@tI A) x) x
| rtB { A B C } f g x : red (tapp (tapp (tapp (@tB A B C) f) g) x) (tapp f (tapp g x))
| rtC { A B C } f x y : red (tapp (tapp (tapp (@tC A B C) f) x) y) (tapp (tapp f y) x)
| rtW { A B } f x : red (tapp (tapp (@tW A B) f) x) (tapp (tapp f x) x)
| rtY { A B } f x : red (tapp (tapp (@tY A B) f) x) (tapp (tapp f (tapp tY f)) x).

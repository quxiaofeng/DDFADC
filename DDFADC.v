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
| tsummatch { A B C } : term ((tysum A B) ~> ((A ~> C) ~> ((B ~> C) ~> C)))
| tmkprod { A B } : term (A ~> (B ~> (typrod A B)))
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
Inductive type :=
| tytop
| tybot
| tyreal
| tysum (l r : type)
| typrod (l r : type)
| tyarr (l r : type).

Inductive term : type -> Type :=
| ttt : term tytop
| texf { T } : term (tyarr tybot T)
| tlit : (*Double ->*) term tyreal
| tplus : term (tyarr tyreal (tyarr tyreal tyreal))
| tminus : term (tyarr tyreal (tyarr tyreal tyreal))
| tdiv : term (tyarr tyreal (tyarr tyreal tyreal))
| tmult : term (tyarr tyreal (tyarr tyreal tyreal))
| tleft { A B } : term (tyarr A (tysum A B))
| tright { A B } : term (tyarr B (tysum A B))
| tsummatch { A B C } : term (tyarr (tysum A B) (tyarr (tyarr A C) (tyarr (tyarr B C) C)))
| tmkprod { A B } : term (tyarr A (tyarr B (typrod A B)))
| tzro { A B } : term (tyarr (typrod A B) A)
| tfst { A B } : term (tyarr (typrod A B) B)
| tapp { A B } (f : term (tyarr A B)) (x : term A) : term B
| tS { A B C } : term (tyarr (tyarr A (tyarr B C)) (tyarr (tyarr A B) (tyarr A C)))
| tK { A B } : term (tyarr A (tyarr B A))
| tI { A } : term (tyarr A A)
| tB { A B C } : term (tyarr (tyarr B C) (tyarr (tyarr A B) (tyarr A C)))
| tC { A B C } : term (tyarr (tyarr A (tyarr B C)) (tyarr B (tyarr A C)))
| tW { A B } : term (tyarr (tyarr A (tyarr A B)) (tyarr A B))
| tY { A B } : term (tyarr (tyarr (tyarr A B) (tyarr A B)) (tyarr A B)).
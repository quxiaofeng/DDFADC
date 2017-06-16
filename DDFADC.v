Require Export List Reals.Rdefinitions Reals.Ranalysis Program CoqUtil.Tactic.

Inductive typ :=
| tytop
| tybot
| tyreal
| typrod (l r : typ)
| tysum (l r : typ)
| tyarr (l r : typ).

Infix "~>" := tyarr (at level 6).

Inductive mem { A }: A -> list A -> Type :=
| memHd a tl: mem a (a :: tl)
| memSkip { a } hd { tl }: mem a tl -> mem a (hd :: tl).

Hint Constructors mem.

Fixpoint delete { A a l }(m: @mem A a l): list A :=
  match m with
  | memHd _ tl => tl
  | memSkip hd m => hd :: delete m
  end.

Fixpoint before { A a l }(m: @mem A a l): list A :=
  match m with
  | memHd _ tl => []
  | memSkip hd m => hd :: before m
  end.

Fixpoint after { A a l }(m: @mem A a l): list A :=
  match m with
  | memHd _ tl => tl
  | memSkip _ m => after m
  end.

Definition delete_before_after { A a l } (m: @mem A a l):
  delete m = before m ++ after m :=
  ltac:(induction m; simpl in *; f_equal; auto).

Fixpoint mem_length { A a l }(m: @mem A a l): nat :=
  match m with
  | memHd _ _ => 0
  | memSkip _ m => S (mem_length m)
  end.
  
Definition memDelete { A a b l } (m: @mem A a l) (m': mem b l):
  mem a (delete m') + (m ~= m').
  induction m; dependent destruction m'; ii; simpl in *; eauto; [].
  specialize (IHm m'); destruct IHm; eauto; [right].
  apply (@eq_dep_JMeq A (fun a => mem a (hd :: tl))
                      a (memSkip hd m)
                      a0 (memSkip hd m')).
  apply (@EqdepFacts.f_eq_dep A (fun a => mem a tl) (fun a => mem a (hd :: tl))
                              a a0 m m' (fun _ m => memSkip hd m)).
  
  Search EqdepFacts.eq_dep.
  Check @EqdepFacts.f_eq_dep Type.
  apply EqdepFacts.eq_sigT_iff_eq_dep.
  Search existT.
  Search EqdepFacts.eq_dep.
Defined.

Inductive term: list typ -> typ -> Type :=
| tvar { h a }: @mem typ a h -> term h a
| ttt h: term h tytop
| texf h a: term h (tybot ~> a)
| tlit h: R -> term h tyreal
| tplus { h }: term h tyreal -> term h tyreal -> term h tyreal
| tminus { h }: term h tyreal -> term h tyreal -> term h tyreal 
| tmult { h }: term h tyreal -> term h tyreal -> term h tyreal
| tdiv { h }: term h tyreal -> term h tyreal -> term h tyreal
| tprod { h a b }: term h a -> term h b -> term h (typrod a b)
| tzro { h a b }: term h (typrod a b) -> term h a
| tfst { h a b }: term h (typrod a b) -> term h b
| tleft { h a } b: term h a -> term h (tysum a b)
| tright { h } a { b }: term h b -> term h (tysum a b)
| tmatch { h a b c }:
    term h (a ~> c) -> term h (b ~> c) -> term h (tysum a b) -> term h c 
| tabs { h a b }: term (a :: h) b -> term h (a ~> b)
| tapp { h a b }: term h (a ~> b) -> term h a -> term h b.

Inductive val: forall { h a }, term h a -> Prop :=
| vtt h: val (ttt h)
| vexf h a: val (@texf h a)
| vlit h r: val (tlit h r)
| vprod { h a b } ate bte: @val h a ate -> @val h b bte -> val (tprod ate bte)
| vleft { h a } b t: @val h a t -> val (tleft b t)
| vright { h } a { b } t: @val h b t -> val (tright a t)
| vabs { h a b } t: val (@tabs h a b t).

Inductive sub { A }: list A -> list A -> Type :=
| subNil r: sub [] r
| subCons { l ls r }: mem l r -> sub ls r -> sub (l :: ls) r.

Hint Constructors sub.

Definition subMem { A a l r }: @sub A l r -> mem a l -> mem a r :=
  ltac:(induction 2; invcs X; ii).

Definition memApp { A } a l r: @mem A a (l ++ a :: r) :=
  ltac:(induction l; simpl in *; eauto).

Hint Resolve memApp.

Definition subApp { A } l r: @sub A r (l ++ r).
  revert l; induction r; eauto; [].
  intros; constructor; eauto; [].
  change (sub r (l ++ [a] ++ r)); rewrite app_assoc; eauto.
Defined.

Definition subTrans { A x y z }: @sub A x y -> sub y z -> sub x z.
  induction 1; ii; eauto.
  econstructor; ii; [].
  eapply (subMem X0); ii.
Defined.

Definition subConsSelf { A a ax }: @sub A ax (a :: ax) := subApp [a] ax.

Hint Resolve subConsSelf.

Definition subConsCons { A x y } a (s: @sub A x y) :=
  subCons (memHd a y) (subTrans s (subApp [a] y)).

Hint Resolve subConsCons.

Inductive shift: forall x y { s: sub x y } { a }, term x a -> term y a -> Prop :=
| shvar x y { s } a m: @shift x y s a (tvar m) (tvar (subMem s m))
| shtt x y { s }: @shift x y s _ (ttt _) (ttt _)
| shexf x y { s a }: @shift x y s _ (texf _ a) (texf _ a)
| shlit x y { s } r: @shift x y s _ (tlit _ r) (tlit _ r)
| shplus x y { s } l r l' r':
    @shift x y s _ l l' -> @shift x y s _ r r' ->
    @shift x y s _ (tplus l r) (tplus l' r')
| shminus x y { s } l r l' r':
    @shift x y s _ l l' -> @shift x y s _ r r' ->
    @shift x y s _ (tminus l r) (tminus l' r')
| shmult x y { s } l r l' r':
    @shift x y s _ l l' -> @shift x y s _ r r' ->
    @shift x y s _ (tmult l r) (tmult l' r')
| shdiv x y { s } l r l' r':
    @shift x y s _ l l' -> @shift x y s _ r r' ->
    @shift x y s _ (tdiv l r) (tdiv l' r')
| shprod x y { s } { a b } l r l' r':
    @shift x y s _ l l' -> @shift x y s _ r r' ->
    @shift x y s (typrod a b) (tprod l r) (tprod l' r')
| shzro x y { s a } b t t':
    @shift x y s _ t t' -> @shift x y s _ (@tzro _ a b t) (tzro t')
| shfst x y { s } a { b } t t':
    @shift x y s _ t t' -> @shift x y s _ (@tfst _ a b t) (tfst t')
| shleft x y { s a } b t t':
    @shift x y s _ t t' -> @shift x y s _ (@tleft _ a b t) (tleft _ t')
| shright x y { s } a { b } t t':
    @shift x y s _ t t' -> @shift x y s _ (@tright _ a b t) (tright _ t')
| shmatch x y { s a b c } l r m l' r' m':
    @shift x y s _ l l' -> @shift x y s _ r r' -> @shift x y s _ m m' ->
    @shift x y s _ (@tmatch _ a b c l r m) (tmatch l' r' m')
| shabs x y a b s t t':
    @shift (a :: x) (a :: y) (subConsCons _ s) _ t t' ->
    @shift x y s (a ~> b) (tabs t) (tabs t') 
| shapp x y { s a b } l r l' r':
    @shift x y s _ l l' -> @shift x y s _ r r' ->
    @shift x y s _ (@tapp _ a b l r) (tapp l' r').

Hint Constructors shift.

Definition shiftFun { x y } s { a } t:
  { res | @shift x y s a t res }.
  generalize dependent y; induction t; intros;
    repeat match goal with H: _ |- _ => specialize (H _ s) end;
    DestructSig; eauto; [].
  specialize (IHt (a :: y) (subConsCons a s));
    DestructSig; eauto.
Defined.

Definition shiftDet { x y } s { a } t l r:
  @shift x y s a t l -> @shift x y s a t r -> l = r :=
  ltac:(intros H H0;
          induction H;
          dependent destruction H0; f_equal; eauto).

Definition subDelete { A a ax } (m: mem a ax): @sub A (delete m) ax :=
  ltac:(induction m; simpl in *; eauto).

Definition subAfter { A a ax } (m: mem a ax): @sub A (after m) ax.
  induction m; simpl in *; eauto; [].
  eapply subTrans; try eassumption; eauto.
Defined.

Definition subBefore { A a ax } (m: mem a ax): @sub A (before m) ax :=
  ltac:(induction m; simpl in *; eauto).

Inductive subst { h a }(m: mem a h):
  forall { b }, term (after m) a -> term h b -> term h b -> Prop :=
| svarSubst s: subst m s (tvar m) (` (shiftFun (subAfter m) s)).
| svarSkip { h a b } s (m: mem a h): subst s (tvar (memSkip b m)) (tvar m) 
| stt { h a } s: @subst h a _ s (ttt _) (ttt _)
| sexf { h a b } s: @subst h a (tybot ~> b) s (texf _ _) (texf _ _)
| slit { h a } s r: @subst h a _ s (tlit _ r) (tlit _ r)
| splus { h a } s l r l' r':
    subst s l l' -> subst s r r' -> @subst h a _ s (tplus l r) (tplus l' r')
| sminus { h a } s l r l' r':
    subst s l l' -> subst s r r' -> @subst h a _ s (tminus l r) (tminus l' r')
| smult { h a } s l r l' r':
    subst s l l' -> subst s r r' -> @subst h a _ s (tmult l r) (tmult l' r')
| sdiv { h a } s l r l' r':
    subst s l l' -> subst s r r' -> @subst h a _ s (tdiv l r) (tdiv l' r')
| sprod { h a b c } s l r l' r':
    subst s l l' -> subst s r r' ->
    @subst h c (typrod a b) s (tprod l r) (tprod l' r')
| szro { h a b c } s x x':
    @subst h c (typrod a b) s x x' -> subst s (tzro x) (tzro x')
| sfst { h a b c } s x x':
    @subst h c (typrod a b) s x x' -> subst s (tfst x) (tfst x')
| sleft { h a b c } s x x':
    subst s x x' -> @subst h c (tysum a b) s (tleft _ x) (tleft _ x')
| sright { h a b c } s x x':
    subst s x x' -> @subst h c (tysum a b) s (tright _ x) (tright _ x')
| smatch { h a b c d } s x y z x' y' z':
    subst s x x' -> subst s y y' -> subst s z z' ->
    @subst h d _ s (tmatch x y z) (@tmatch h a b c x' y' z')
| sapp { h a b c } s x x' y y':
    @subst h c (a ~> b) s x x' -> subst s y y' -> subst s (tapp x y) (tapp x' y').

Hint Constructors subst.

Ltac especialize :=
  match goal with
  | H: forall (_: ?x), _ |- _ =>
    Not ltac:(isProp x; idtac);
    let f := fresh in evar (f: x); specialize (H f)
  end.

Ltac unc :=
  match goal with
  | H: _ |- _ => unfold H in *; clear H
  end.

Definition substFunc: forall{ h a b } (m: mem a h) (s: term (after m) b) (t: term h b),
    { res | subst s t res }.
  dependent induction t;
    try (repeat match goal with H: _ |- _ => specialize (H a h s) end;
         repeat especialize;
         remove_premise ltac:(f_equal; compute in *; trivial); repeat unc;
         DestructSig; try dependent destruction m; solve [eauto]).
  specialize (IHt a0 (a :: h)).
Defined.

Inductive red: forall{ h a }, 
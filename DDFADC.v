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
| mem_hd a tl: mem a (a :: tl)
| mem_skip { a } hd { tl }: mem a tl -> mem a (hd :: tl).

Hint Constructors mem.

Fixpoint mem_loc { A a l }(m: @mem A a l): nat :=
  match m with
  | mem_hd _ _ => O
  | mem_skip _ m => S (mem_loc m)
  end.

Definition mem_loc_eq { A a b l }(m: @mem A a l)(n: mem b l):
  mem_loc m = mem_loc n -> a = b /\ m ~= n :=
  ltac:(induction m; dependent destruction n; simpl; ii; try congruence;
          invcs H; specialize (IHm n); ii; repeat subst; trivial).

Definition mem_eq_dec { A a b l }(m: @mem A a l)(n: mem b l):
  { a = b /\ m ~= n } + { ~ (a = b /\ m ~= n) }.
  destruct (Nat.eq_dec (mem_loc m) (mem_loc n));
    try Apply (@mem_loc_eq A); ii; [].
  right; ii; repeat subst; ii.
Defined.
  
  Fixpoint delete { A a l }(m: @mem A a l): list A :=
  match m with
  | mem_hd _ tl => tl
  | mem_skip hd m => hd :: delete m
  end.

Fixpoint before { A a l }(m: @mem A a l): list A :=
  match m with
  | mem_hd _ tl => []
  | mem_skip hd m => hd :: before m
  end.

Fixpoint after { A a l }(m: @mem A a l): list A :=
  match m with
  | mem_hd _ tl => tl
  | mem_skip _ m => after m
  end.

Definition delete_before_after { A a l } (m: @mem A a l):
  delete m = before m ++ after m :=
  ltac:(induction m; simpl in *; f_equal; auto).

Fixpoint mem_length { A a l }(m: @mem A a l): nat :=
  match m with
  | mem_hd _ _ => 0
  | mem_skip _ m => S (mem_length m)
  end.

Definition mem_try_delete { A a b l }(m: @mem A a l)(m': mem b l):
  mem a (delete m') + (a = b /\ m ~= m').
  induction m; dependent destruction m'; ii; simpl in *; eauto; [].
  specialize (IHm m'); destruct IHm; eauto; ii; repeat subst; ii.
Defined.

Definition mem_delete { A a b l }(m: @mem A a l)(m': mem b l):
  (~ m ~= m') -> mem a (delete m') :=
  ltac:(destruct (mem_try_delete m m'); ii).

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
| sub_nil r: sub [] r
| sub_cons { l ls r }: mem l r -> sub ls r -> sub (l :: ls) r.

Hint Constructors sub.

Definition sub_mem { A a l r }: @sub A l r -> mem a l -> mem a r :=
  ltac:(induction 2; invcs X; ii).

Definition mem_app { A } a l r: @mem A a (l ++ a :: r) :=
  ltac:(induction l; simpl in *; eauto).

Hint Resolve mem_app.

Definition sub_app { A } l r: @sub A r (l ++ r).
  revert l; induction r; eauto; [].
  intros; constructor; eauto; [].
  change (sub r (l ++ [a] ++ r)); rewrite app_assoc; eauto.
Defined.

Definition sub_trans { A x y z }: @sub A x y -> sub y z -> sub x z.
  induction 1; ii; eauto.
  econstructor; ii; [].
  eapply (sub_mem X0); ii.
Defined.

Definition sub_cons_self { A a ax }: @sub A ax (a :: ax) := sub_app [a] ax.

Hint Resolve sub_cons_self.

Definition sub_cons_cons { A x y } a (s: @sub A x y) :=
  sub_cons (mem_hd a y) (sub_trans s (sub_app [a] y)).

Hint Resolve sub_cons_cons.

Inductive shift: forall x y { s: sub x y } { a }, term x a -> term y a -> Prop :=
| shvar x y { s } a m: @shift x y s a (tvar m) (tvar (sub_mem s m))
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
    @shift (a :: x) (a :: y) (sub_cons_cons _ s) _ t t' ->
    @shift x y s (a ~> b) (tabs t) (tabs t') 
| shapp x y { s a b } l r l' r':
    @shift x y s _ l l' -> @shift x y s _ r r' ->
    @shift x y s _ (@tapp _ a b l r) (tapp l' r').

Hint Constructors shift.

Definition shift_fun { x y } s { a } t:
  { res | @shift x y s a t res }.
  generalize dependent y; induction t; intros;
    repeat match goal with H: _ |- _ => specialize (H _ s) end;
    DestructSig; eauto; [].
  specialize (IHt (a :: y) (sub_cons_cons a s));
    DestructSig; eauto.
Defined.

Definition shift_det { x y } s { a } t l r:
  @shift x y s a t l -> @shift x y s a t r -> l = r :=
  ltac:(intros H H0;
          induction H;
          dependent destruction H0; f_equal; eauto).

Definition sub_delete { A a ax } (m: mem a ax): @sub A (delete m) ax :=
  ltac:(induction m; simpl in *; eauto).

Definition sub_after { A a ax } (m: mem a ax): @sub A (after m) ax.
  induction m; simpl in *; eauto; [].
  eapply sub_trans; try eassumption; eauto.
Defined.

Definition sub_before { A a ax } (m: mem a ax): @sub A (before m) ax :=
  ltac:(induction m; simpl in *; eauto).

Inductive subst { h a }(m: mem a h):
  forall { b }, term (after m) a -> term h b -> term h b -> Prop :=
| svarSubst s: subst m s (tvar m) (` (shift_fun (sub_after m) s))
| svarSkip { b } s (m': mem b h):
    (~ (a = b /\ m ~= m')) -> subst m s (tvar m') (tvar m')
| stt s: @subst h a m _ s (ttt _) (ttt _)
| sexf { b } s: @subst h a m (tybot ~> b) s (texf _ _) (texf _ _)
| slit s r: @subst h a m _ s (tlit _ r) (tlit _ r)
| splus s l r l' r':
    subst m s l l' -> subst m s r r' -> @subst h a m _ s (tplus l r) (tplus l' r')
| sminus s l r l' r':
    subst m s l l' -> subst m s r r' -> @subst h a m _ s (tminus l r) (tminus l' r')
| smult s l r l' r':
    subst m s l l' -> subst m s r r' -> @subst h a m _ s (tmult l r) (tmult l' r')
| sdiv s l r l' r':
    subst m s l l' -> subst m s r r' -> @subst h a m _ s (tdiv l r) (tdiv l' r')
| sprod { b c } s l r l' r':
    subst m s l l' -> subst m s r r' ->
    @subst h _ m _ s (@tprod _ b c l r) (tprod l' r')
| szro { b c } s x x':
    @subst h a _ (typrod b c) s x x' -> subst m s (tzro x) (tzro x')
| sfst { b c } s x x':
    @subst h a _ (typrod b c) s x x' -> subst m s (tfst x) (tfst x')
| sleft { b c } s x x':
    subst m s x x' -> @subst h _ m (tysum b c) s (tleft _ x) (tleft _ x')
| sright { b c } s x x':
    subst m s x x' -> @subst h _ m (tysum b c) s (tright _ x) (tright _ x')
| smatch { b c d } s x y z x' y' z':
    subst m s x x' -> subst m s y y' -> subst m s z z' ->
    @subst h _ m _ s (tmatch x y z) (@tmatch h b c d x' y' z')
| sabs { b c } s x x':
    @subst (b :: h) _ (mem_skip _ m) c s x x' -> subst m s (tabs x) (tabs x')
| sapp { b c } s x x' y y':
    @subst h _ m (b ~> c) s x x' -> subst m s y y' ->
    subst m s (tapp x y) (tapp x' y').

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

Definition subst_func { h a b }(m: mem a h)(s: term (after m) a)(t: term h b):
    { res | subst m s t res }.
  dependent induction t;
    repeat
      match goal with
      | H: _ |- _ => specialize (H m s)
      end;
    DestructSig; eauto.
  + destruct (mem_eq_dec m m0); ii; repeat subst; eauto; [].
    econstructor; eapply svarSkip; ii.
  + specialize (IHt (mem_skip _ m) s); DestructSig; eauto.
Defined.

Definition subst_det { h a b } m s x y z :
  @subst h a m b s x y -> @subst h a m b s x z -> y = z :=
  ltac:(induction 1; ii;
          match goal with
          | H: subst _ _ _ _ |- _ => dependent destruction H; ii
          end; f_equal; eauto).

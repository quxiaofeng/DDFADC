Require Export Program.

Require Import CoqUtil.Tactic.

Inductive type :=
| tytop
| tybot
| tyreal
| tysum (l r : type)
| typrod (l r : type)
| tyarr (l r : type).

Infix "~>" := tyarr (at level 55, right associativity).

Require Export Coq.Reals.Rdefinitions.

Inductive term : type -> Type :=
| tapp { A B } (f : term (A ~> B)) (x : term A) : term B
| ttt : term tytop
| texf { A } : term (tybot ~> A)
| tlit : R -> term tyreal
| tplus : term (tyreal ~> tyreal ~> tyreal)
| tminus : term (tyreal ~> tyreal ~> tyreal)
| tmult : term (tyreal ~> tyreal ~> tyreal)
| tdiv : term (tyreal ~> tyreal ~> tyreal)
| tleft { A B } : term (A ~> (tysum A B))
| tright { A B } : term (B ~> (tysum A B))
| tsummatch { A B C } : term ((tysum A B) ~> (A ~> C) ~> (B ~> C) ~> C)
| tmkprod { A B } : term (A ~> B ~> (typrod A B))
| tzro { A B } : term ((typrod A B) ~> A)
| tfst { A B } : term ((typrod A B) ~> B)
| tS { A B C } : term ((A ~> B ~> C) ~> (A ~> B) ~> (A ~> C))
| tK { A B } : term (A ~> B ~> A)
| tI { A } : term (A ~> A)
| tB { A B C } : term ((B ~> C) ~> (A ~> B) ~> (A ~> C))
| tC { A B C } : term ((A ~> B ~> C) ~> (B ~> A ~> C))
| tW { A B } : term ((A ~> A ~> B) ~> (A ~> B))
| tY { A B } : term (((A ~> B) ~> (A ~> B)) ~> (A ~> B)).

Inductive val : forall { A }, term A -> Prop :=
| vttt : val ttt
| vtexf A : val (@texf A)
| vtlit r : val (tlit r)
| vtplus : val tplus
| vtplus' x : val x -> val (tapp tplus x)
| vtminus : val tminus
| vtminus' x : val x -> val (tapp tminus x)
| vtmult : val tmult
| vtmult' x : val x -> val (tapp tmult x)
| vtdiv : val tdiv
| vtdiv' x : val x -> val (tapp tdiv x)
| vtleft A B : val (@tleft A B)
| vtleft' A B a : val a -> val (tapp (@tleft A B) a)
| vtright A B : val (@tright A B)
| vtright' A B b : val b -> val (tapp (@tright A B) b)
| vtsummatch A B C : val (@tsummatch A B C)
| vtsummatch' A B C s : val s -> val (tapp (@tsummatch A B C) s)
| vtsummatch'' A B C s f : val s -> val f -> val (tapp (tapp (@tsummatch A B C) s) f)
| vtmkprod A B : val (@tmkprod A B)
| vtmkprod' A B a : val a -> val (tapp (@tmkprod A B) a)
| vtmkprod'' A B a b : val a -> val b -> val (tapp (tapp (@tmkprod A B) a) b)
| vtzro A B : val (@tzro A B)
| vtfst A B : val (@tfst A B)
| vtS A B C : val (@tS A B C)
| vtS' A B C f : val f -> val (tapp (@tS A B C) f)
| vtS'' A B C f x : val f -> val x -> val (tapp (tapp (@tS A B C) f) x)
| vtK A B : val (@tK A B)
| vtK' A B a : val a -> val (tapp (@tK A B) a)
| vtI A : val (@tI A)
| vtB A B C : val (@tB A B C)
| vtB' A B C f : val f -> val (tapp (@tB A B C) f)
| vtB'' A B C f g : val f -> val g -> val (tapp (tapp (@tB A B C) f) g)
| vtC A B C : val (@tC A B C)
| vtC' A B C f : val f -> val (tapp (@tC A B C) f)
| vtC'' A B C f x : val f -> val x -> val (tapp (tapp (@tC A B C) f) x)
| vtW A B : val (@tW A B)
| vtW' A B f : val f -> val (tapp (@tW A B) f)
| vtY A B : val (@tY A B)
| vtY' A B f : val f -> val (tapp (@tY A B) f).

Hint Constructors val.

Inductive red : forall { A }, term A -> term A -> Prop :=
| rtplus l r : red (tapp (tapp tplus (tlit l)) (tlit r)) (tlit (Rplus l r))
| rtminus l r : red (tapp (tapp tminus (tlit l)) (tlit r)) (tlit (Rminus l r))
| rtmult l r : red (tapp (tapp tmult (tlit l)) (tlit r)) (tlit (Rmult l r))
| rtdiv l r : red (tapp (tapp tdiv (tlit l)) (tlit r)) (tlit (Rdiv l r))
| rtleft { A B C } a f g :
    val a -> val f -> val g ->
    red (tapp (tapp (tapp (@tsummatch A B C) (tapp tleft a)) f) g) (tapp f a)
| rtright { A B C } b f g :
    val b -> val f -> val g ->
    red (tapp (tapp (tapp (@tsummatch A B C) (tapp tright b)) f) g) (tapp g b)
| rtzro { A B } a b :
    val a -> val b ->
    red (tapp tzro (tapp (tapp (@tmkprod A B) a) b)) a
| rtfst { A B } a b :
    val a -> val b ->
    red (tapp tfst (tapp (tapp (@tmkprod A B) a) b)) b
| rtS { A B C } f x arg :
    val f -> val x -> val arg ->
    red (tapp (tapp (tapp (@tS A B C) f) x) arg) (tapp (tapp f arg) (tapp x arg))
| rtK { A B } x y :
    val x -> val y ->
    red (tapp (tapp (@tK A B) x) y) x
| rtI { A } x :
    val x ->
    red (tapp (@tI A) x) x
| rtB { A B C } f g x :
    val f -> val g -> val x ->
    red (tapp (tapp (tapp (@tB A B C) f) g) x) (tapp f (tapp g x))
| rtC { A B C } f x y :
    val f -> val x -> val y ->
    red (tapp (tapp (tapp (@tC A B C) f) x) y) (tapp (tapp f y) x)
| rtW { A B } f x :
    val f -> val x ->
    red (tapp (tapp (@tW A B) f) x) (tapp (tapp f x) x)
| rtY { A B } f x :
    val f -> val x ->
    red (tapp (tapp (@tY A B) f) x) (tapp (tapp f (tapp tY f)) x)
| rtappf { A B } f f' x : @red (A ~> B) f f' -> red (tapp f x) (tapp f' x)
| rtappx { A B } f x x' : val f -> red x x' -> red (@tapp A B f x) (tapp f x').

Hint Constructors red.
Hint Resolve rtappx.

Definition val_func { A B } {f : term (A ~> B)} {x : term A} : val (tapp f x) -> val f :=
  ltac:(intros H; dependent induction H; constructor; tauto).

Definition val_arg { A B } {f : term (A ~> B)} {x : term A} : val (tapp f x) -> val x :=
  ltac:(intros H; dependent induction H; tauto).

Definition vexf A x : val (tapp (@texf A) x) -> False :=
  ltac:(intros H; dependent destruction H).

Definition vreal x : val x -> { r | x = tlit r } :=
  ltac:(dependent destruction x;
          intros H;
          solve[eauto] ||
               exfalso; dependent destruction H).

Inductive checked (X : Prop) { T : Type } (t : T) : Prop :=
| is_checked (x : X) : checked X t.

Ltac check H t :=
  pose proof (is_checked _ t H); clear H.

Ltac uncheck H := inversion H; clear H.

Ltac uncheck_all t :=
  repeat
    match goal with
    | H : checked _ t |- _ => uncheck H
    end.

Require Import String.

Ltac work :=
  repeat intro;
  repeat
    (match goal with
    | H : val (tapp texf _) |- _ => apply vexf in H; contradict H
    | H : val _ |- _ => apply vreal in H
    | H : val _ |- _ =>
     try solve [(exfalso; dependent destruction H)];
      pose proof (val_func H);
      pose proof (val_arg H);
      check H "val_app"%string
    | H : tlit _ = tlit _ |- _ =>
      invcs H
     end ||
         destruct_exists ||
         subst);
  uncheck_all "val_app"%string;
  cleanPS tauto.

Ltac dd1 := let x := fresh in intros x; dependent destruction x.

Definition val_dec X (tm : term X) : { val tm } + { ~ (val tm) }.
  induction tm; eauto; [].
  destruct IHtm1, IHtm2; try (right; intuition idtac; work; solve[eauto]); eauto; [].
  dependent destruction tm1; eauto; try (right; dd1; fail); [].
  dependent destruction tm1_1; work; eauto;
    (right;
     repeat destruct_exists;
     subst;
     dd1;
     fail).
Defined.

Definition red_not_val A x y : red x y -> ~ @val A x.
  intros H;
    dependent induction H;
    work; try tauto; repeat destruct_exists; congruence.
Defined.

Definition val_not_red A x y : @val A x -> ~ red x y.
  intros X H;
    dependent induction H;
    work; try tauto; repeat destruct_exists; congruence.
Defined.

Definition eval A x : { y | red x y } + { @val A x }.
  Ltac red_it := left; repeat destruct_exists; repeat econstructor; eauto; fail.
  dependent induction x;
    repeat
      match goal with
      | H : { _ | _ } + { _ } |- _ => destruct H as [[]|]
      end;
    eauto;
    try red_it; [].
  dependent destruction x1; eauto; try red_it; work.
  + dependent destruction x1_1; eauto; work; try red_it; [].
    dependent destruction x1_1_1; try red_it; work; [].
    dependent destruction x1_1_2; dependent destruction x1_1_2_1; work; red_it.
  + dependent destruction x2; dependent destruction x2_1; work; [].
    dependent destruction x2_1_1; work; [].
    red_it.
  + dependent destruction x2; dependent destruction x2_1; work; [].
    dependent destruction x2_1_1; work; [].
    red_it.
Defined.

Inductive hasY : forall { x }, term x -> Prop :=
| direct_Y A B : hasY (@tY A B)
| left_Y A B l r : hasY l -> hasY (@tapp A B l r)
| right_Y A B l r : hasY r -> hasY (@tapp A B l r).

Hint Constructors hasY.

Inductive transitive_closure { X } (p : X -> X -> Prop) : X -> X -> Prop :=
| here x : transitive_closure p x x
| step x y z : p x y -> transitive_closure p y z -> transitive_closure p x z.

Hint Constructors transitive_closure.

Definition halt { ty } (x : term ty) := exists y, transitive_closure red x y /\ val y.

Hint Unfold halt.

Inductive track { T } (t : T) : Prop :=
| tracking.

Hint Constructors track.

Definition YoH { ty : type } (t : term ty) :=
  hasY t \/ halt t.

Definition rel { ty : type } : forall (t : term ty), Prop.
  assert (track ty) by eauto.
  dependent induction ty; intro.
  + exact (YoH t).
  + exact (YoH t). 
  + exact (YoH t).
  + exact (YoH t).
  + exact (YoH t).
  + exact (hasY t \/ (halt t /\ (forall x, IHty1 (tracking _) x -> IHty2 (tracking _) (tapp t x)))).
Defined.

Definition rel_top t : @YoH tytop t -> rel t := ltac:(ii).
Definition rel_bot t : @YoH tybot t -> rel t := ltac:(ii).
Definition rel_real t : @YoH tyreal t -> rel t := ltac:(ii).
Definition rel_sum A B t : @YoH (tysum A B) t -> rel t := ltac:(ii).
Definition rel_prod A B t : @YoH (typrod A B) t -> rel t := ltac:(ii).
Definition rel_arr A B t :
  (@hasY (A ~> B) t \/ (halt t /\ (forall x, rel x -> rel (tapp t x)))) -> rel t :=
  ltac:(compute; ii).

Definition top_rel t : rel t -> @YoH tytop t := ltac:(ii).
Definition bot_rel t : rel t -> @YoH tybot t := ltac:(ii).
Definition real_rel t : rel t -> @YoH tyreal t := ltac:(ii).
Definition sum_rel A B t : rel t -> @YoH (tysum A B) t := ltac:(ii).
Definition prod_rel A B t : rel t -> @YoH (typrod A B) t := ltac:(ii).
Definition arr_rel A B t : rel t ->
  (@hasY (A ~> B) t \/ (halt t /\ (forall x, rel x -> rel (tapp t x)))) :=
  ltac:(compute; ii).

Definition tcrf { A B } (f f' : term (A ~> B)) x :
  transitive_closure red f f' -> transitive_closure red (tapp f x) (tapp f' x) :=
  ltac:(induction 1; eauto).

Hint Resolve tcrf.

Definition tcrx { A B } (f : term (A ~> B)) x x' :
  val f -> transitive_closure red x x' -> transitive_closure red (tapp f x) (tapp f x') :=
  ltac:(induction 2; eauto).

Hint Resolve tcrx.

Definition hasY_rel t x : hasY x -> @rel t x.
  intros; compute.
  dependent destruction t; tauto.
Defined.

Hint Resolve hasY_rel.

Definition transitive_closure_transitive { T } p (x y z : T) :
  transitive_closure p x y -> transitive_closure p y z -> transitive_closure p x z :=
  ltac:(induction 1; eauto).

Definition transitive_closure_appf { A B } f f' x :
  transitive_closure red f f' ->
  transitive_closure red (@tapp A B f x) (tapp f' x) :=
  ltac:(induction 1; eauto).

Definition transitive_closure_appx { A B } f x x' :
  val f ->
  transitive_closure red x x' ->
  transitive_closure red (@tapp A B f x) (tapp f x') :=
  ltac:(induction 2; eauto).

Inductive type_real_sub_exp : type -> type -> Prop :=
| trse_sum_l { A B } : type_real_sub_exp A (tysum A B)
| trse_sum_r { A B } : type_real_sub_exp B (tysum A B)
| trse_prod_l { A B } : type_real_sub_exp A (typrod A B)
| trse_prod_r { A B } : type_real_sub_exp B (typrod A B)
| trse_arr_l { A B } : type_real_sub_exp A (tyarr A B)
| trse_arr_r { A B } : type_real_sub_exp B (tyarr A B)
| trse_trans { A B C } :
    type_real_sub_exp A B -> type_real_sub_exp B C -> type_real_sub_exp A C.

Fixpoint type_size (x : type) : nat :=
  match x with
  | tytop => 1
  | tybot => 1
  | tyreal => 1
  | tysum A B => 1 + type_size A + type_size B
  | typrod A B => 1 + type_size A + type_size B
  | tyarr A B => 1 + type_size A + type_size B
  end.

Require Import Omega.

Definition trse_ts x y : type_real_sub_exp x y -> type_size x < type_size y :=
  ltac:(induction 1; simpl; omega).

Definition trse_neq x y : type_real_sub_exp x y -> x <> y :=
  ltac:(ii; subst; Apply trse_ts; omega).

Definition hasY_dec { A } x : { @hasY A x } + { ~ hasY x }.
  dependent induction x;
    repeat
      match goal with
      | H : { _ } + { _ } |- _ => destruct H
      end;
    eauto; right; ii; dependent destruction H; eauto.
  all: symmetry in x0.
  all: eapply trse_neq; try (eexact x0).
  eapply trse_trans; [| apply trse_arr_l].
  eapply trse_trans; [| apply trse_arr_r].
  all: try solve [econstructor].
  eapply trse_trans; [| apply trse_arr_r].
  solve [econstructor].
  eapply trse_trans; [| apply trse_arr_r].
  solve [econstructor].
Defined.

Definition term_eq_dec A (x : term A) (y : term A) : { x = y } + { x <> y }.
  Ltac ric := right; ii; congruence.
  dependent induction x; ii; dependent destruction y; eauto; try ric.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Admitted. (*All of them can be dischargeed. Write a ltac for that.*)

Definition type_eq_dec (x y : type) : { x = y } + { x <> y } := ltac:(decide equality).

Definition red_det t x x' x'' : @red t x x' -> red x x'' -> x' = x''.
  induction 1; let H := fresh in intros H; dependent destruction H; ii;
                                   match goal with
                                   | H : red ?x _ |- _ =>
                                     try (assert (val x) by eauto; Apply val_not_red; ii)
                                   end.
  f_equal; solve [eauto].
  EApply (val_not_red _ f); exfalso; solve [eauto].
  f_equal; solve [eauto].
Defined.

Definition rel_hold t x : @rel t x.
  induction x;
    compute in * |-;
                   repeat (destruct_exists || ii);
    eauto; try (compute; eauto; fail).
  + specialize (H1 x2); ii.
  + apply rel_arr.
    right; ii; eauto.
    Apply bot_rel; unfold YoH in *; ii; work; eauto.
    exfalso; compute in *; work; ii; eauto; work.
  + right; ii; eauto.
    fold (@rel (tyreal ~> tyreal)).
    compute in H; ii; repeat destruct_exists; ii; eauto.
    right; ii; eauto.
    exists (tapp tplus H0); eauto.
    compute in *; ii; repeat destruct_exists; ii; eauto.
    right.
    work.
    exists (tlit (Rplus H2 H5)); ii; eauto.
    eapply transitive_closure_transitive.
    eapply transitive_closure_appf.
    eapply transitive_closure_appx; eauto.
    eapply transitive_closure_transitive.
    eapply transitive_closure_appx; eauto.
    eauto.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + apply rel_arr.
    right; ii; eauto.
    apply rel_arr.
    Apply arr_rel; ii; eauto.
    right; ii.
    admit.
    apply rel_arr.
    right; ii; eauto.
    admit.
    Apply arr_rel; ii; eauto.
    specialize (H1 x1); specialize (H4 x1); ii.
    Apply arr_rel; ii.
    dependent destruction H4; eauto.
    specialize (H5 (tapp x0 x1)); ii.
    admit.
  + apply rel_arr.
    right; ii; eauto.
    apply rel_arr.
    destruct (hasY_dec x); eauto.
    right; ii; eauto.
    admit.
  + admit.    
  + admit.
  + admit.
  + admit.
Admitted.

Hint Constructors transitive_closure.

Definition Y_or_val { ty } :
  forall (x : term ty), hasY x \/ halt x.
  intros x.
  pose proof (rel_hold ty x).
  induction ty; compute in *; ii.
Defined.
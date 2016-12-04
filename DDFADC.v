Require Export Program.

Require Import CoqUtil.Tactic CoqUtil.MoreRelations.

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

Definition val_func { A B } { f } { x } : val (@tapp A B f x) -> val f :=
  ltac:(intros H; dependent induction H; constructor; tauto).

Definition val_arg { A B } { f } { x } : val (@tapp A B f x) -> val x :=
  ltac:(intros H; dependent induction H; tauto).

Definition vexf { A } x : val (tapp (@texf A) x) -> False :=
  ltac:(intros H; dependent destruction H).

Definition vprod { A B } p :
  val p -> { l : _ & { r | p = (tapp (tapp (@tmkprod A B) l) r)} }.
  dependent destruction p; intros H.
  dependent destruction p1; try (solve [exfalso; dependent destruction H]).
  dependent destruction p1_1; try (solve [exfalso; dependent destruction H]).
  eauto.
Defined.

Definition vsum { A B } s :
  val s -> { l | s = tapp (@tleft A B) l } + { r | s = tapp tright r }.
  dependent destruction s; intros H.
  dependent destruction s1; try (solve [exfalso; dependent destruction H]);
    eauto.
Defined.

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
    | H : _ + _ |- _ => destruct H
     end ||
         destruct_exists ||
         subst);
  uncheck_all "val_app"%string;
  cleanPS tauto.

Ltac dd1 := let x := fresh in intros x; dependent destruction x.

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

Ltac discharge_type_eq :=
  repeat (Apply (f_equal type_size)); simpl in *; omega.

Inductive track { T } (t : T) : Prop :=
| tracking.

Hint Constructors track.

Definition val_dec X (tm : term X) : { val tm } + { ~ (val tm) }.
  induction tm; eauto; [].
  destruct IHtm1, IHtm2; try (right; intuition idtac; work; solve [eauto]); eauto; [].
  dependent destruction tm1; eauto; try (right; solve [dd1]); [].
  dependent destruction tm1_1; work; eauto;
    (right;
     repeat destruct_exists;
     subst;
     solve [dd1]).
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
  Ltac red_it := left; repeat destruct_exists; repeat econstructor; solve [eauto].
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

Definition eval_to { t } x y := transitive_closure red x y /\ @val t y.

Hint Unfold eval_to.

Definition halt { t } (x : term t) := exists y, eval_to x y.

Hint Unfold halt.

Definition rel { ty : type } : forall (t : term ty), Prop.
  assert (track ty) by eauto.
  dependent induction ty; intro.
  + assert (track tytop) by assumption.
    exact (halt t).
  + assert (track tybot) by assumption.
    exact (halt t). 
  + assert (track tyreal) by assumption.
    exact (halt t).
  + assert (exists l r, track (tysum l r)) by (do 2 econstructor; eassumption).
    exact ((exists l, eval_to t (tapp tleft l) /\
                 IHty1 (tracking _) l) \/
           (exists r, eval_to t (tapp tright r) /\
                 IHty2 (tracking _) r)).
  + assert (exists l r, track (typrod l r)) by (do 2 econstructor; eassumption).
    exact (exists l r, eval_to t (tapp (tapp tmkprod l) r) /\
                  IHty1 (tracking _) l /\
                  IHty2 (tracking _) r).
  + assert (exists l r, track (tyarr l r)) by (do 2 econstructor; eassumption).
    exact (exists t', eval_to t t' /\
                 (forall x, IHty1 (tracking _) x -> val x -> IHty2 (tracking _) (tapp t' x))).
Defined.

Definition rel_top t : @halt tytop t -> rel t := ltac:(ii).

Definition rel_bot t : @halt tybot t -> rel t := ltac:(ii).

Definition rel_real t : @halt tyreal t -> rel t := ltac:(ii).

Definition rel_sum A B t :
  ((exists l, eval_to t (tapp tleft l) /\ @rel A l) \/
   (exists r, eval_to t (tapp tright r) /\ @rel B r)) -> rel t :=
  ltac:(compute; tauto).

Definition rel_prod A B t :
  (exists l r, eval_to t (tapp (tapp tmkprod l) r) /\
          @rel A l /\
          @rel B r) -> rel t := ltac:(ii).

Definition rel_arr A B t :
  (exists t', @eval_to (A ~> B) t t' /\
         (forall x, rel x -> val x -> rel (tapp t' x))) -> rel t :=
  ltac:(compute; ii).

Definition top_rel t : rel t -> @halt tytop t := ltac:(ii).

Definition bot_rel t : rel t -> @halt tybot t := ltac:(ii).

Definition real_rel t : rel t -> @halt tyreal t := ltac:(ii).

Definition sum_rel A B t :
  rel t -> ((exists l, eval_to t (tapp tleft l) /\ @rel A l) \/
           (exists r, eval_to t (tapp tright r) /\ @rel B r)) :=
  ltac:(ii).

Definition prod_rel A B t :
  rel t -> (exists l r, eval_to t (tapp (tapp tmkprod l) r) /\
                  @rel A l /\
                  @rel B r) := ltac:(ii).

Definition arr_rel A B t : rel t ->
  (exists t', @eval_to (A ~> B) t t' /\
         (forall x, rel x -> val x -> rel (tapp t' x))) :=
  ltac:(compute; ii).

Ltac unfold_rel :=
  repeat
    (try
       match goal with
       | H : @rel tytop _ |- _ =>
         apply top_rel in H; ii
       | H : @rel tybot _ |- _ =>
         apply bot_rel in H; ii
       | H : @rel tyreal _ |- _ =>
         apply real_rel in H; ii
       | H : @rel (tysum _ _) _ |- _ =>
         apply sum_rel in H; repeat (destruct_exists || ii)
       | H : @rel (typrod _ _) _ |- _ =>
         apply prod_rel in H; repeat (destruct_exists || ii)
       | H : @rel (tyarr _ _) _ |- _ =>
         apply arr_rel in H; repeat (destruct_exists || ii)
       end;
     try (apply rel_top; ii);
     try (apply rel_bot; ii);
     try (apply rel_real; ii);
     try (apply rel_sum; repeat (destruct_exists || ii));
     try (apply rel_prod; repeat (destruct_exists || ii));
     try (apply rel_arr; repeat (destruct_exists || ii))).

Definition rel_halt t te : @rel t te -> halt te :=
  ltac:(destruct t; ii; unfold_rel; eauto 6).

Definition transitive_closure_appf { A B } f f' x :
  transitive_closure red f f' ->
  transitive_closure red (@tapp A B f x) (tapp f' x) :=
  ltac:(induction 1; eauto).

Definition transitive_closure_appx { A B } f x x' :
  val f ->
  transitive_closure red x x' ->
  transitive_closure red (@tapp A B f x) (tapp f x') :=
  ltac:(induction 2; eauto).

Definition hasY_dec { A } x : { @hasY A x } + { ~ hasY x } :=
  ltac:(
    dependent induction x;
      repeat
        match goal with
        | H : { _ } + { _ } |- _ => destruct H
        end;
      eauto; right; ii; dependent destruction H; eauto; discharge_type_eq).

Definition type_eq_dec (x y : type) : { x = y } + { x <> y } := ltac:(decide equality).

Definition term_eq_dec
           (rdec : forall l r : R, { l = r } + { l <> r })
           A (x : term A) (y : term A)
  : { x = y } + { x <> y }.
  Ltac ric := right; ii; congruence.
  dependent induction x; ii; dependent destruction y; eauto; try ric;
    try discharge_type_eq.
  + destruct (type_eq_dec A A0); subst.
     ++ destruct (IHx1 y1), (IHx2 y2); subst; eauto;
          right; intros H; inversion H;
            repeat Apply (Eqdep_dec.inj_pair2_eq_dec type type_eq_dec); tauto.
     ++ right; intros H; inversion H; tauto.
  + destruct (rdec r r0); [left|right]; congruence.
Defined.

Definition red_det { t x x' x'' } : @red t x x' -> red x x'' -> x' = x''.
  induction 1;
    let H := fresh in intros H; dependent destruction H; ii;
                        match goal with
                        | H : red ?x _ |- _ =>
                          try (assert (val x) by eauto; Apply val_not_red; ii)
                        end.
  f_equal; solve [eauto].
  EApply (val_not_red _ f); exfalso; solve [eauto].
  f_equal; solve [eauto].
Defined.

Definition halt_red_back t x y : @red t x y -> halt y -> halt x :=
  ltac:(unfold halt, eval_to; ii; destruct_exists; ii; eauto).

Hint Resolve halt_red_back.

Ltac break_hasY :=
  repeat
    match goal with
    | H : hasY (tapp _ _) |- _ => dependent destruction H
    | H : hasY (tlit _) |- _ => dependent destruction H
    end;
  try
    match goal with
    | H : hasY _ |- _ => solve[dependent destruction H]
    end;
  try discharge_type_eq.

Definition hasY_red_back t x y : @red t x y -> hasY y -> hasY x :=
  ltac:(intros H; dependent induction H; ii; break_hasY; eauto).

Hint Resolve hasY_red_back.

Definition rel_red_back t : forall x y, @red t x y -> rel y -> rel x :=
  ltac:(induction t;
        intros H;
        dependent destruction H;
        ii;
        unfold_rel;
        unfold eval_to in *;
        ii;
        eauto 8).

Hint Resolve rel_red_back.

Definition red_app_func_det {A B : type} (f f' : term (A ~> B)) (x : term A) y :
    red f f' -> red (tapp f x) y -> y = tapp f' x :=
  ltac:(intros; eapply red_det; [eassumption|solve [eauto]]).

Definition red_app_arg_det {A B : type} (f : term (A ~> B)) (x x' : term A) y :
  val f -> red x x' -> red (tapp f x) y -> y = tapp f x' :=
  ltac:(intros; eapply red_det; [eassumption|solve [eauto]]).

Ltac use_red_det :=
  repeat (
      match goal with
      | L : red ?x ?y, R : red ?x ?z |- _ =>
        pose proof (red_det L R); subst; clear R
      end).

Definition halt_red_preserve t x y : @red t x y -> halt x -> halt y.
  intros R H.
  destruct H as [? [H (*bug: using [] will not work*)]]; destruct H; use_red_det; eauto.
  Apply red_not_val; tauto.
Defined.

Definition red_trans_val { t x y z } :
  @red t x y ->
  transitive_closure red x z ->
  val z ->
  transitive_closure red y z.
  destruct 2; ii; use_red_det; eauto.
  Apply red_not_val; tauto.
Defined.

Ltac use_red_trans_val :=
  repeat (
      match goal with
      | L : red ?x ?y, R : transitive_closure red ?x ?z |- _ =>
        let H := fresh in
        assert (val z) as H by eauto;
        pose proof (red_trans_val L R H); clear R
      end).

Definition rel_red_preserve t : forall x y, @red t x y -> rel x -> rel y.
  induction t; ii; unfold_rel; unfold eval_to in *; eauto using halt_red_preserve.
  left; econstructor; ii; eauto; []; use_red_trans_val; tauto.
  right; econstructor; ii; eauto; []; use_red_trans_val; tauto.
  do 2 econstructor; ii; eauto; []; use_red_trans_val; tauto.
  econstructor; ii; use_red_trans_val; eauto.  
Defined.

Definition hasY_trans_back t x y : transitive_closure (@red t) x y -> hasY y -> hasY x :=
  ltac:(induction 1; eauto).

Hint Resolve hasY_trans_back.

Definition rel_trans_preserve t x y :
  transitive_closure (@red t) x y -> rel x -> rel y.
  induction 1; ii; [].
  eapply IHtransitive_closure; ii.
  eapply rel_red_preserve; solve [eauto].
Defined.

Definition rel_trans_back t x y :
  transitive_closure (@red t) x y -> rel y -> rel x :=
  ltac:(induction 1; ii; eauto).

Ltac Deduct t :=
  match goal with
  | H : _ |- _ => pose proof H; apply t in H
  end.

Ltac goal_rel_step :=
  eapply rel_red_back; [solve [eauto]|].

Definition rel_app { A B } f x : rel f -> rel x -> rel (@tapp A B f x). 
  ii; Apply arr_rel; destruct_exists; unfold eval_to in *; ii.
  Deduct rel_halt;
    unfold halt, eval_to in *;
    destruct_exists; ii.
  eapply rel_trans_back.
  eapply transitive_closure_transitive.
  eapply transitive_closure_appf; solve [eauto].
  eapply transitive_closure_appx; solve [eauto].
  eapply H3; eauto.
  eapply rel_trans_preserve; eassumption.
Defined.

Hint Resolve rel_app.

Definition rel_lit r : rel (tlit r) := ltac:(compute; eauto).

Hint Resolve rel_lit.

Definition trans_red_val_eq { t x y } :
  transitive_closure (@red t) x y -> val x -> x = y :=
  ltac:(destruct 1; try Apply red_not_val; tauto).

Ltac use_trans_red_val_eq :=
  repeat
    match goal with
    | H : transitive_closure red ?x _, V : val ?x |- _ =>
      pose proof (trans_red_val_eq H V); clear H; subst
    end.

Definition noY_split A B f x : ~ hasY (@tapp A B f x) -> ~ hasY f /\ ~ hasY x :=
  ltac:(ii; eauto).

Definition rel_hold t x (_ : ~ hasY x) : @rel t x.
  induction x;
    try (compute; solve [eauto]);
    repeat (
        try goal_rel_step;
        try (econstructor; ii; [solve [eauto]|solve [eauto]|]);
        unfold_rel;
        unfold halt, eval_to in *;
        use_trans_red_val_eq;
        try Apply noY_split;
        ii;
        work);
    eauto.
  + eapply rel_trans_back.
    eapply transitive_closure_appf; try eassumption.
    Deduct rel_halt; unfold halt, eval_to in *; destruct_exists; ii.
    eapply rel_trans_back.
    eapply transitive_closure_appx; eauto.
    apply H5; eauto; [].
    eapply rel_trans_preserve; eassumption.
  + left; econstructor; ii; solve [eauto].
  + right; econstructor; ii; solve [eauto].
  + do 2 econstructor; ii; solve [eauto].
  + specialize (H9 _ H5 H8).
    pose proof (rel_halt _ _ H9); unfold halt, eval_to in *; destruct_exists; ii.
    eapply rel_trans_back.
    eapply transitive_closure_appx; eassumption.
    eapply H4; eauto; [].
    eapply rel_trans_preserve; eassumption.
  + exfalso; eauto.
Defined.

Definition Y_or_val { ty } :
  forall (x : term ty), hasY x \/ halt x.
  intros x.
  pose proof (rel_hold ty x).
  destruct (hasY_dec x); ii.
  Apply rel_halt; ii.
Defined.

Class FTG (repr : type -> Type) :=
  {
    fapp { A B } : repr (A ~> B) -> repr A -> repr B;
    ftt : repr tytop;
    fexf { A } : repr (tybot ~> A);
    fexf_ { A } : _  (*bug? A will not be implicit without : _*) := fapp (@fexf A);
    flit : R -> repr tyreal;
    fplus : repr (tyreal ~> tyreal ~> tyreal);
    fplus_ := fapp fplus;
    fplus__ x := fapp (fplus_ x);
    fminus : repr (tyreal ~> tyreal ~> tyreal);
    fminus_ := fapp fminus;
    fminus__ x := fapp (fminus_ x);
    fmult : repr (tyreal ~> tyreal ~> tyreal);
    fmult_ := fapp fmult;
    fmult__ x := fapp (fmult_ x);
    fdiv : repr (tyreal ~> tyreal ~> tyreal);
    fdiv_ := fapp fdiv;
    fdiv__ x := fapp (fdiv_ x);
    fleft { A B } : repr (A ~> tysum A B);
    fleft_ { A B } : _ := fapp (@fleft A B);
    fright { A B } : repr (B ~> tysum A B);
    fright_ { A B } : _ := fapp (@fright A B);
    fsummatch { A B C } : repr (tysum A B ~> (A ~> C) ~> (B ~> C) ~> C);
    fsummatch_ { A B C } : _ := fapp (@fsummatch A B C);
    fsummatch__ { A B C } f : _ := fapp (@fsummatch_ A B C f);
    fsummatch___ { A B C } f g : _ := fapp (@fsummatch__ A B C f g);
    fmkprod { A B } : repr (A ~> B ~> typrod A B);
    fmkprod_ { A B } : _ := fapp (@fmkprod A B);
    fmkprod__ { A B } x : _ := fapp (@fmkprod_ A B x);
    fzro { A B } : repr (typrod A B ~> A);
    fzro_ { A B } : _ := fapp (@fzro A B);
    ffst { A B } : repr (typrod A B ~> B);
    ffst_ { A B } : _ := fapp (@ffst A B);
    fS { A B C } : repr ((A ~> B ~> C) ~> (A ~> B) ~> (A ~> C));
    fS_ { A B C } : _ := fapp (@fS A B C);
    fS__ { A B C } f : _ := fapp (@fS_ A B C f);
    fS___ { A B C } f x : _ := fapp (@fS__ A B C f x);
    fK { A B } : repr (A ~> B ~> A);
    fK_ { A B } : _ := fapp (@fK A B);
    fK__ { A B } x : _ := fapp (@fK_ A B x);
    fI { A } : repr (A ~> A);
    fI_ { A } : _ := fapp (@fI A);
    fB { A B C } : repr ((B ~> C) ~> (A ~> B) ~> (A ~> C));
    fB_ { A B C } : _ := fapp (@fB A B C);
    fB__ { A B C } f : _ := fapp (@fB_ A B C f);
    fB___ { A B C } f g : _ := fapp (@fB__ A B C f g);
    fC { A B C } : repr ((A ~> B ~> C) ~> (B ~> A ~> C));
    fC_ { A B C } : _ := fapp (@fC A B C);
    fC__ { A B C } f : _ := fapp (@fC_ A B C f);
    fC___ { A B C } f g : _ := fapp (@fC__ A B C f g);
    fW { A B } : repr ((A ~> A ~> B) ~> (A ~> B));
    fW_ { A B } : _ := fapp (@fW A B);
    fW__ { A B } f : _ := fapp (@fW_ A B f);
    fY { A B } : repr (((A ~> B) ~> (A ~> B)) ~> (A ~> B));
    fY_ { A B } : _ := fapp (@fY A B);
    fY__ { A B } f : _ := fapp (@fY_ A B f)
  }.

Instance Eval : FTG term :=
  {
    fapp A B := tapp;
    ftt := ttt;
    fexf A := texf;
    flit := tlit;
    fplus := tplus;
    fminus := tminus;
    fmult := tmult;
    fdiv := tdiv;
    fleft A B := tleft;
    fright A B := tright;
    fsummatch A B C := tsummatch;
    fmkprod A B := tmkprod;
    fzro A B := tzro;
    ffst A B := tfst;
    fS A B C := tS;
    fK A B := tK;
    fI A := tI;
    fB A B C := tB;
    fC A B C := tC;
    fW A B := tW;
    fY A B := tY
  }.

Instance Next repr Arg { orig : FTG repr } :
  FTG (fun x => repr x + repr (Arg ~> x))%type :=
  {
    fapp A B f x :=
      match f, x with
      | inl f', inl x' => inl (fapp f' x')
      | inr f', inr x' => inr (fapp (fapp fS f') x')
      | inl f', inr x' => inr (fapp (fapp fS (fapp fK f')) x')
      | inr f', inl x' => inr (fapp (fapp fS f') (fapp fK x'))
      end;
    ftt := inl ftt;
    fexf A := inl fexf;
    flit r := inl (flit r);
    fplus := inl fplus;
    fminus := inl fminus;
    fmult := inl fmult;
    fdiv := inl fdiv;
    fleft A B := inl fleft;
    fright A B := inl fright;
    fsummatch A B C := inl fsummatch;
    fmkprod A B := inl fmkprod;
    fzro A B := inl fzro;
    ffst A B := inl ffst;
    fS A B C := inl fS;
    fK A B := inl fK;
    fI A := inl fI;
    fB A B C := inl fB;
    fC A B C := inl fC;
    fW A B := inl fW;
    fY A B := inl fY
  }.

Definition flam { repr Arg A } { orig : FTG repr } (exp : repr A + repr (Arg ~> A)) :=
  match exp with
  | inl exp' => fapp fK exp'
  | inr exp' => exp'
  end.

Definition Term A := forall { repr } { ftg : FTG repr }, repr A.

Instance GetTerm : FTG Term :=
  {
    fapp A B f x := fun R O => fapp (f R O) (x R O);
    ftt := fun _ _ => ftt;
    fexf A := fun _ _ => fexf;
    flit r := fun _ _ => flit r;
    fplus := fun _ _ => fplus;
    fminus := fun _ _ => fminus;
    fmult := fun _ _ => fmult;
    fdiv := fun _ _ => fdiv;
    fleft A B := fun _ _ => fleft;
    fright A B := fun _ _ => fright;
    fsummatch A B C := fun _ _ => fsummatch;
    fmkprod A B := fun _ _ => fmkprod;
    fzro A B := fun _ _ => fzro;
    ffst A B := fun _ _ => ffst;
    fS A B C := fun _ _ => fS;
    fK A B := fun _ _ => fK;
    fI A := fun _ _ => fI;
    fB A B C := fun _ _ => fB;
    fC A B C := fun _ _ => fC;
    fW A B := fun _ _ => fW;
    fY A B := fun _ _ => fY
  }.

Class Gradient A :=
  {
    gzro : Term A;
    gplus : Term (A ~> A ~> A);
    gplus_ : Term A -> Term (A ~> A) := fapp gplus;
    gplus__ : Term A -> Term A -> Term A := fun x => fapp (gplus_ x);
    gmult : Term (tyreal ~> A ~> A);
    gmult_ : Term tyreal -> Term (A ~> A) := fapp gmult;
    gmult__ : Term tyreal -> Term A -> Term A := fun x => fapp (gmult_ x)
  }.

Instance GReal : Gradient tyreal :=
  {
    gzro := flit R0;
    gplus := fplus;
    gmult := fmult
  }.

Instance GProd A B { GA : Gradient A } { GB : Gradient B } : Gradient (typrod A B) :=
  {
    gzro := fapp (fapp fmkprod gzro) gzro;
    gplus := flam (flam (fmkprod__
                           (fapp (fapp (inl (inl gplus))
                                       (fzro_ (inl (inr fI))))
                                 (fzro_ (inr fI)))
                           (fapp (fapp (inl (inl gplus))
                                       (ffst_ (inl (inr fI))))
                                 (ffst_ (inr fI)))));
    gmult := flam (flam (fmkprod__
                           (fapp (fapp (inl (inl gmult))
                                       (inl (inr fI)))
                                 (fzro_ (inr fI)))
                           (fapp (fapp (inl (inl gmult))
                                       (inl (inr fI)))
                                 (ffst_ (inr fI)))))
  }.

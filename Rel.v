Require Export Red.

Inductive val_app_type := val_app.
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
      check H val_app
    | H : tlit _ = tlit _ |- _ =>
      invcs H
    | H : _ + _ |- _ => destruct H
     end ||
         destruct_exists ||
         subst);
  uncheck_all val_app;
  cleanPS tauto.

Definition vprod { A B } p :
  val p -> { l : _ & { r | p = (tapp (tapp (@tmkprod A B) l) r) /\ val l /\ val r } }.
  dependent destruction p; intros H.
  dependent destruction p1; try (solve [exfalso; dependent destruction H]).
  dependent destruction p1_1; try (solve [exfalso; dependent destruction H]).
  work; eauto.
Defined.

Definition vsum { A B } s :
  val s -> { l | s = tapp (@tleft A B) l /\ val l } + { r | s = tapp tright r /\ val r }.
  dependent destruction s; intros H.
  dependent destruction s1; try (solve [exfalso; dependent destruction H]);
    work; eauto.
Defined.

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

Definition val_dec X (tm : term X) : { val tm } + { ~ (val tm) }.
  induction tm; eauto; [].
  destruct IHtm1, IHtm2; try (right; ii; work; solve [eauto]); eauto; [].
  dependent destruction tm1; eauto; try (right; solve [dd1]); [].
  dependent destruction tm1_1; work; eauto;
    right; work; congruence.
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

Definition eval_to { T } x y := (transitive_closure red x y /\ @val T y).

Hint Unfold eval_to.

Definition halt { T } (x : term T) := exists y, eval_to x y.

Arguments halt { T } x /.

Fixpoint rel { ty : type } : term ty -> Prop :=
  match ty with
  | tytop => halt
  | tybot => halt
  | tyreal => halt
  | tysum _ _ => fun x => (exists l, eval_to x (tapp tleft l) /\ rel l) \/
                      (exists r, eval_to x (tapp tright r) /\ rel r)
  | typrod _ _ => fun x => exists l r, eval_to x (tapp (tapp tmkprod l) r) /\ rel l /\ rel r
  | _ ~> _ => fun f => exists f', eval_to f f' /\ (forall x, rel x -> val x -> rel (tapp f' x))
  end.

Arguments rel ty _ : simpl never.

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
  ltac:(destruct t; ii; unfold_rel; simpl in *; eauto 6).

Definition transitive_closure_appf { A B } f f' x :
  transitive_closure red f f' ->
  transitive_closure red (@tapp A B f x) (tapp f' x) :=
  ltac:(induction 1; eauto).

Definition transitive_closure_appx { A B } f x x' :
  val f ->
  transitive_closure red x x' ->
  transitive_closure red (@tapp A B f x) (tapp f x') :=
  ltac:(induction 2; eauto).

Definition type_eq_dec (x y : type) : { x = y } + { x <> y } :=
  ltac:(decide equality).

Definition app_eq_func { A B } fl fr xl xr :
  @tapp A B fl xl = tapp fr xr -> fl = fr.
  intros H; invcs H.
  repeat Apply (Eqdep_dec.inj_pair2_eq_dec _ type_eq_dec); tauto.
Defined.

Definition app_eq_arg { A B } fl fr xl xr : @tapp A B fl xl = @tapp A B fr xr -> xl = xr.
  intros H; invcs H.
  repeat Apply (Eqdep_dec.inj_pair2_eq_dec _ type_eq_dec); tauto.
Defined.

Ltac Deduct t :=
  match goal with
  | H : _ |- _ => pose proof H; apply t in H
  end.

Definition app_eq { A B } fl fr xl xr : @tapp A B fl xl = tapp fr xr ->
                                        fl = fr /\ xl = xr :=
  ltac:(ii; Deduct (@app_eq_arg A B); Deduct (@app_eq_func A B); ii).

Definition term_eq_dec
           (rdec : forall l r : R, { l = r } + { l <> r })
           A (x : term A) (y : term A)
  : { x = y } + { x <> y }.
  Ltac ric := right; ii; congruence.
  dependent induction x; ii; dependent destruction y; eauto; try ric;
    try discharge_type_eq.
  + destruct (type_eq_dec A A0); subst.
     ++ destruct (IHx1 y1), (IHx2 y2); subst; eauto;
          right; ii;
        repeat Apply @app_eq; ii; subst; try tauto.
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

Hint Unfold eval_to.

Definition rel_red_back t : forall x y, @red t x y -> rel y -> rel x :=
  ltac:(induction t;
          intros H;
          dependent destruction H;
          ii;
          unfold_rel;
          simpl in *;
          repeat destruct_exists;
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
  destruct H as [? [H (*bug: using [] will not work*)]]; destruct H;
    simpl in *; use_red_det; eauto; [].
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

Definition rel_trans_preserve t x y :
  transitive_closure (@red t) x y -> rel x -> rel y.
  induction 1; ii; [].
  eapply IHtransitive_closure; ii.
  eapply rel_red_preserve; solve [eauto].
Defined.

Definition rel_trans_back t x y :
  transitive_closure (@red t) x y -> rel y -> rel x :=
  ltac:(induction 1; ii; eauto).

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

Definition trans_val_eq { t x y } :
  transitive_closure (@red t) x y -> val x -> x = y :=
  ltac:(destruct 1; try Apply red_not_val; tauto).

Ltac use_trans_val_eq_with T :=
  repeat
    match goal with
    | H : transitive_closure red ?x _ |- _ =>
      (let V := fresh in
      assert(V : val x) by T; pose proof (trans_val_eq H V); clear H; subst)
    end.

Ltac use_trans_val_eq := use_trans_val_eq_with eauto.

Definition rel_hold t x : @rel t x.
  induction x;
    try (compute; solve [eauto]);
    repeat (
        try goal_rel_step;
        try (econstructor; ii; [solve [eauto]|solve [eauto]|]);
        unfold_rel;
        unfold eval_to in *;
        simpl in *;
        use_trans_val_eq;
        try Apply noZ_split;
        ii;
        work);
    eauto.
  + eapply rel_trans_back.
    eapply transitive_closure_appf; try eassumption.
    Deduct rel_halt; unfold halt, eval_to in *; destruct_exists; ii.
    eapply rel_trans_back.
    eapply transitive_closure_appx; eauto.
    apply H1; eauto; [].
    eapply rel_trans_preserve; eassumption.
  + left; econstructor; ii; solve [eauto].
  + right; econstructor; ii; solve [eauto].
  + do 2 econstructor; ii; solve [eauto].
  + specialize (H8 _ H4 H6).
    pose proof (rel_halt _ _ H8); unfold halt, eval_to in *; destruct_exists; ii.
    eapply rel_trans_back.
    eapply transitive_closure_appx; eassumption.
    eapply H3; eauto; [].
    eapply rel_trans_preserve; eassumption.
Defined.

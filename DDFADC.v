Require Export red.

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

Definition eval_to { T } x y := (transitive_closure red x y /\ @val T y).

Arguments eval_to { T } x y /.

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

Definition hasY_dec { A } x : { @hasY A x } + { ~ hasY x } :=
  ltac:(
    dependent induction x;
      repeat
        match goal with
        | H : { _ } + { _ } |- _ => destruct H
        end;
      eauto; right; ii; dependent destruction H; eauto; discharge_type_eq).

Definition type_eq_dec (x y : type) : { x = y } + { x <> y } := ltac:(decide equality).

Definition app_eq_func { A B } fl fr xl xr : @tapp A B fl xl = tapp fr xr -> fl = fr.
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

Ltac break_hasY :=
  repeat
    match goal with
    | H : hasY (tapp _ _) |- _ => dependent destruction H
    | H : hasY (tlit _) |- _ => dependent destruction H
    end;
  try
    match goal with
    | H : hasY _ |- _ => solve[dependent destruction H; discharge_type_eq]
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
        simpl in *;
        repeat destruct_exists;
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

Definition noY_split A B f x : ~ hasY (@tapp A B f x) -> ~ hasY f /\ ~ hasY x :=
  ltac:(ii; eauto).

Definition rel_hold t x (_ : ~ hasY x) : @rel t x.
  induction x;
    try (compute; solve [eauto]);
    repeat (
        try goal_rel_step;
        try (econstructor; ii; [solve [eauto]|solve [eauto]|]);
        unfold_rel;
        simpl in *;
        use_trans_val_eq;
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
  + specialize (H9 _ H5 H7).
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

Definition Term A := forall repr (ftg : FTG repr), repr A.

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

Fixpoint sem_eq { A } : term A -> term A -> Prop :=
  match A with
  | tytop => fun x y => halt x <-> halt y
  | tybot => fun _ _ => True
  | tyreal => fun x y =>
               (halt x <-> halt y) /\
               (forall r, eval_to x (tlit r) <-> eval_to y (tlit r))
  | tysum _ _ => fun x y =>
                  (halt x <-> halt y) /\
                  (forall xl yl, eval_to x (fleft_ xl) ->
                            eval_to y (fleft_ yl) ->
                            sem_eq xl yl) /\
                  (forall xr yr,
                      eval_to x (fright_ xr) ->
                      eval_to y (fright_ yr) ->
                      sem_eq xr yr) /\
                  (forall xl yr, eval_to x (fleft_ xl) ->
                            eval_to y (fright_ yr) ->
                            False) /\
                  (forall xr yl,
                      eval_to x (fright_ xr) ->
                      eval_to y (fleft_ yl) ->
                      False)
  | typrod _ _ => fun x y =>
                   (halt x <-> halt y) /\
                   (forall xl xr yl yr,
                       eval_to x (fmkprod__ xl xr) ->
                       eval_to y (fmkprod__ yl yr) ->
                       sem_eq xl yl /\ sem_eq xr yr)
  | _ ~> _ => fun x y =>
               (halt x <-> halt y) /\
               (forall x' y', eval_to x x' -> eval_to y y' ->
                         forall xa ya, sem_eq xa ya -> val xa -> val ya ->
                                  sem_eq (tapp x' xa) (tapp y' ya))
  end.

Definition trans_val_det { A } (x y z : term A) :
  transitive_closure red x y -> transitive_closure red x z ->
  val y -> val z ->
  y = z :=
  ltac:(induction 1; ii; use_trans_val_eq; use_red_trans_val; ii; solve [eauto]).

Ltac use_trans_val_det_with T :=
  repeat
    match goal with
    | A : transitive_closure red ?x ?y,
          B : transitive_closure red ?x ?z |- _ =>
      let C := fresh in
      let D := fresh in
      assert(C : val y) by T;
      assert(D : val z) by T;
      pose proof (trans_val_det _ _ _ A B C D); clear B D; subst
    end.

Ltac use_trans_val_det := use_trans_val_det_with eauto.

Definition trans_val_trans { t : type } (x y z : term t) :
  transitive_closure red x z ->
  val z ->
  transitive_closure red x y ->
  transitive_closure red y z :=
  ltac:(induction 3; ii; use_trans_val_eq; use_red_trans_val; eauto).

Ltac use_trans_val_trans :=
  repeat
    match goal with
    | A : transitive_closure red ?x ?z,
          B : val ?z,
              C : transitive_closure red ?x ?y |- _ =>
      pose proof (trans_val_trans _ _ _ A B C); clear A
    end.

Ltac remove_premise L :=
  (repeat
    match goal with
    | H : ?P -> _ |- _ =>
      match type of P with
      | Prop => (assert P by L; ii)
      end
    end);
  cleanPS tauto.

Ltac discharge_app_eq :=
  repeat
    match goal with
    | H : tapp _ _ = tapp _ _ |- _ => solve [inversion H]
    end.

Definition sem_eq_arr { A B } fl fr :
  val fl -> val fr ->
  (forall xl xr, sem_eq xl xr -> val xl -> val xr -> sem_eq (@tapp A B fl xl) (tapp fr xr)) ->
  sem_eq fl fr.
  simpl in *; ii; use_trans_val_eq; eauto.
Defined.

Definition sem_eq_eval_back { A } (x y x' y' : term A) :
  eval_to x x' -> eval_to y y' -> sem_eq x' y' -> sem_eq x y.
  destruct A; simpl in *; ii; remove_premise eauto; repeat destruct_exists; ii;
    use_trans_val_det; eauto.
  + specialize (H5 r); ii; remove_premise eauto;
      eapply transitive_closure_transitive; solve [eauto].
  + specialize (H5 r); ii; remove_premise eauto;
      use_trans_val_det; eapply transitive_closure_transitive; solve [eauto].
  + specialize (H5 xl xr yl yr); remove_premise eauto.
  + specialize (H5 xl xr yl yr); remove_premise eauto.
Defined.

Definition sem_eq_red_back { A } (x y x' y' : term A) :
  red x x' -> red y y' -> sem_eq x' y' -> sem_eq x y.
  destruct A; simpl in *;
    repeat (
        destruct_exists;
        ii;
        use_red_trans_val;
        use_trans_val_det;
        remove_premise eauto);
    eauto.
  + specialize (H3 r); ii; remove_premise eauto; eauto.
  + specialize (H3 r); ii; remove_premise eauto; eauto.
  + specialize (H3 xl xr yl yr); ii.
  + specialize (H3 xl xr yl yr); ii.
Defined.

Definition sem_eq_eval { A } (x y x' y' : term A) :
  eval_to x x' -> eval_to y y' -> sem_eq x y -> sem_eq x' y'.
  destruct A; simpl in *; ii; remove_premise eauto; repeat destruct_exists; ii;
    use_trans_val_det; use_trans_val_eq; eauto;
      cleanPS tauto; repeat (work; use_trans_val_eq).
  + specialize (H5 H3); ii; remove_premise eauto.
    use_trans_val_det; work; eauto.
  + specialize (H5 H4); ii; remove_premise eauto.
    use_trans_val_det; work; eauto.
  + specialize (H5 xl xr yl yr); tauto.
  + specialize (H5 xl xr yl yr); tauto.
Defined.

Definition sem_eq_red { A } (x y x' y' : term A) :
  red x x' -> red y y' -> sem_eq x y -> sem_eq x' y'.
  destruct A; simpl in *; ii;
    repeat (
        destruct_exists;
        ii;
        use_trans_val_det;
        use_red_trans_val;
        remove_premise eauto);
    eauto 6.
  + specialize (H3 r); ii; remove_premise eauto; use_red_trans_val; eauto.
  + specialize (H3 r); ii; remove_premise eauto; use_red_trans_val; eauto.
  + specialize (H3 xl xr yl yr); ii; remove_premise eauto.
  + specialize (H3 xl xr yl yr); ii; remove_premise eauto.
Defined.

Require Export Classical.

Definition sem_eq_halt { A } (x y : term A) : sem_eq x y -> halt x -> halt y :=
  ltac:(induction A; simpl in *; ii; destruct_exists; ii; eauto; work).

Definition sem_eq_symm { A } (x y : term A) : sem_eq x y -> sem_eq y x.
  induction A; simpl in *; ii; remove_premise eauto; repeat destruct_exists; ii;
    use_trans_val_det; eauto.
  + apply H1; ii.
  + apply H1; ii.
  + apply IHA1.
    eapply H1; ii; try eassumption.
  + apply IHA2.
    eapply H1; ii; try eassumption.
  + eapply IHA2; eapply H1; ii; eauto.
Defined.

Definition sem_eq_trans_back { A } (x y x' y' : term A) :
  transitive_closure red x x' -> transitive_closure red y y' -> sem_eq x' y' -> sem_eq x y.
  destruct A; simpl in *;
    repeat (
        destruct_exists;
        ii;
        use_trans_val_trans;
        use_trans_val_eq;
        remove_premise eauto); eauto;
      try (econstructor; ii; [eapply transitive_closure_transitive|]; eassumption).
  + specialize (H3 r); ii.
    eapply transitive_closure_transitive; eassumption.
  + specialize (H3 r); ii.
    eapply transitive_closure_transitive; eassumption.
  + eapply H3; ii; eassumption.
  + eapply H3; ii; eassumption.
Defined.

Definition sem_eq_trans { A } (x y x' y' : term A) :
  transitive_closure red x x' -> transitive_closure red y y' -> sem_eq x y -> sem_eq x' y'.
  destruct A; simpl in *;
    repeat (
        destruct_exists; ii;
        remove_premise
          ltac:(econstructor; ii; [eapply transitive_closure_transitive|]; eassumption);
        use_trans_val_det;
        use_trans_val_trans;
        use_trans_val_eq);
    eauto.
  + specialize (H3 r);
      ii;
      remove_premise
        ltac:(eauto; eapply transitive_closure_transitive; eassumption).
    repeat
      (try match goal with
           | A:transitive_closure red ?x ?z, B:val ?z, C:transitive_closure red ?x ?y
             |- _ => pose proof (trans_val_trans _ _ _ A B C); clear A
           end; use_trans_val_eq); eauto.
  + specialize (H3 r); ii;
      remove_premise ltac:(eauto; eapply transitive_closure_transitive; eassumption).
    repeat
      (try match goal with
           | A:transitive_closure red ?x ?z, B:val ?z, C:transitive_closure red ?x ?y
             |- _ => pose proof (trans_val_trans _ _ _ A B C); clear A
           end; use_trans_val_eq); eauto.
  + specialize (H1 xl yl);
      remove_premise ltac:(
        ii; [eapply transitive_closure_transitive]; eassumption).
  + specialize (H3 xr yr);
      remove_premise ltac:(
        ii; [eapply transitive_closure_transitive]; eassumption).
  + specialize (H4 xl yr);
      remove_premise ltac:(
        ii; [eapply transitive_closure_transitive]; eassumption).
  + specialize (H6 xr yl);
      remove_premise ltac:(
        ii; [eapply transitive_closure_transitive]; eassumption).
  + specialize (H3 xl xr yl yr);
      remove_premise ltac:(
        ii; [eapply transitive_closure_transitive]; eassumption).
  + specialize (H3 xl xr yl yr);
      remove_premise ltac:(
        ii; [eapply transitive_closure_transitive]; eassumption).
  + eapply H3; ii; try eapply transitive_closure_transitive; eauto.
Defined.

Fixpoint type_denote t : Type :=
  match t with
  | tyreal => R
  | tytop => unit
  | tybot => False
  | tysum l r => type_denote l + type_denote r
  | typrod l r => type_denote l * type_denote r
  | l ~> r => type_denote l -> type_denote r
  end.

Fixpoint term_denote { A } : term A -> type_denote A -> Prop :=
  match A with
  | tytop => fun t _ => halt t
  | tybot => fun _ _ => False
  | tyreal => fun t r => eval_to t (tlit r)
  | tysum B C => fun t s => match s with
                        | inl dl => exists l, eval_to t (fleft_ l) /\ term_denote l dl
                        | inr dr => exists r, eval_to t (fright_ r) /\ term_denote r dr 
                        end
  | typrod B C => fun t p =>
                   exists l r, eval_to t (fmkprod__ l r) /\
                          term_denote l (fst p) /\
                          term_denote r (snd p)
  | B ~> C => fun t f => exists t', eval_to t t' /\
                           forall x y, term_denote x y -> term_denote (tapp t' x) (f y)  
  end.

Definition term_denote_halt { A } (t : term A) x : term_denote t x -> halt t.
  induction A; simpl in *; ii; try match_destruct; destruct_exists; ii; eauto.
Defined.

Definition term_denote_red { A } (l r : term A) x :
  red l r -> term_denote l x -> term_denote r x.
  destruct A; ii; simpl in *;
    repeat (
        destruct_exists; ii;
        use_red_trans_val;
        try match_destruct); eauto 6.
Defined.

Definition term_denote_trans { A } (l r : term A) x :
  transitive_closure red l r -> term_denote l x -> term_denote r x :=
  ltac:(induction 1; eauto using term_denote_red).

Definition term_denote_red_back { A } (l r : term A) x :
  red l r -> term_denote r x -> term_denote l x.
  destruct A; ii; simpl in *;
    repeat (destruct_exists; ii;
            try match_destruct); eauto 7.
Defined.

Hint Resolve term_denote_red_back.

Definition term_denote_trans_back { A } (l r : term A) x :
  transitive_closure red l r -> term_denote r x -> term_denote l x :=
  ltac:(induction 1; eauto).

Definition sem_eq_denote_rel { A } (l r : term A) :
  (forall x, sem_eq l r -> term_denote l x -> term_denote r x) /\
  (forall x, term_denote l x -> term_denote r x -> sem_eq l r).
  induction A; simpl in *; ii;
    repeat (
        try match_destruct;
        remove_premise eauto;
        destruct_exists; ii;
        use_trans_val_det;
        try Apply @vsum;
        try Apply @vprod;
        try Apply @app_eq;
        try match goal with
            | H : _ = _ |- _ => solve [inversion H]
            | H : tlit _ = tlit _ |- _ => invcs H                                      
            end;
        subst);
    eauto.
  + eapply H2; eauto.
  + econstructor; ii; try eassumption; eauto; [].
    eapply IHA1; try eapply H; ii; try eassumption; eauto.
  + exfalso; eapply H3; ii; try eassumption; eauto.
  + exfalso; eapply H5; ii; try eassumption; eauto.
  + econstructor; ii; try eassumption; eauto; [].
    eapply IHA2; try eapply H2; try eassumption; eauto.
  + eapply IHA1; eauto.
  + eapply IHA2; eauto.
  + destruct x; simpl in *; do 2 econstructor; ii; try eassumption; eauto.
    eapply IHA1; try eassumption; eapply H2; ii; try eassumption; eauto.
    eapply IHA2; try eassumption; eapply H2; ii; try eassumption; eauto.
  + eapply IHA1; eassumption.
  + eapply IHA2; eassumption.
  + econstructor; ii; try eassumption; [].
    specialize (H5 x0 y); ii.
    eapply IHA2; try eassumption; [].
    Deduct (term_denote_halt x0); simpl in *; destruct_exists; ii; [].
    eapply sem_eq_trans_back; try eapply transitive_closure_appx; try eassumption.
    eapply H2; ii.
    eapply IHA1; try eassumption;
      eapply term_denote_trans; eassumption.
  + admit.
Admitted.

Definition denote_sem_eq { A } (l r : term A) :
  forall x, term_denote l x -> term_denote r x -> sem_eq l r.
  induction A; simpl in *; ii;
    repeat (try match goal with
                | H : tlit _ = tlit _ |- _ => invcs H
                | H : _ = _ |- _ => solve [inversion H]
                end;
            try match_destruct;
            destruct_exists; ii;
            use_trans_val_det;
            try Apply @app_eq;
            subst);
    eauto.
  eapply sem_eq_trans; try eapply transitive_closure_appf; try eassumption; [].
  
  admit.
Admitted.

Definition sem_eq_refl { A } (x : term A) : val x -> sem_eq x x.
  induction x; ii;
    repeat (apply sem_eq_arr; eauto; ii; []);
  simpl in *; ii; cleanPS tauto; work; eauto.
  all: repeat
         (try match goal with
              | H : transitive_closure red _ _ |- _ =>
               dependent destruction H; []
              | H : red _ _ |- _=>
                dependent destruction H;
                solve[exfalso; Apply red_not_val; eauto] ||
                     (try solve [exfalso; Apply red_not_val; eauto]; [])
              | H : transitive_closure red ?x _ |- _ =>
                assert (val x) by eauto; use_trans_val_eq
              | H : tlit _ = tlit _ |- _ => invcs H
              | H : forall r : R, (transitive_closure red (tlit ?X) (tlit r) /\ _) <-> _ |- _ =>
                specialize (H X)
              | H : _ + _ |- _ => destruct H
              | H : _ = _ |- _ => solve [inversion H]
              end;
          try Apply @app_eq;
          try Apply @vsum;
          try Apply @vprod;
          repeat destruct_exists;
          ii;
          remove_premise eauto;
          subst;
          cleanPS tauto).
  all: eauto.
  all: try solve [eapply sem_eq_red_back; eauto].
  all: try (eapply sem_eq_red_back; eauto; []).
  + specialize (H6 a3 a); specialize (H11 H19 H0); remove_premise eauto.
    specialize (H18 a3 a); remove_premise eauto.
  + specialize (H15 b1 a); remove_premise eauto.
  + specialize (H13 a1 b); remove_premise eauto.
  + specialize (H10 b3 b); specialize (H12 H3 H2); remove_premise eauto.
    specialize (H18 b3 b); remove_premise eauto.
  + specialize (H4 H13 X2 H12 X); remove_premise eauto.
  + specialize (H4 H13 X2 H12 X); remove_premise eauto.
  + specialize (H10 H15 H9); specialize (H11 H14 H0); remove_premise eauto.
    specialize (H17 xl1 xr1); remove_premise eauto.
    destruct (classic (halt (tapp H15 xl1))).
    ++ simpl in *; remove_premise eauto; cleanPS tauto; destruct_exists; ii.
       specialize (H19 H13 H17); specialize (H11 xl1 xr1); ii.
       destruct (classic (halt (tapp H14 xl1))).
       +++ Deduct @sem_eq_halt; eauto; []; simpl in *; destruct_exists; ii.
           specialize (H19 H11 H18).
           assert (sem_eq H11 H18) by (eapply sem_eq_eval; simpl in *; ii; eassumption).
           remove_premise eauto.
           eapply sem_eq_trans_back;
             try eapply transitive_closure_appf;
             try eassumption; [].
           eapply sem_eq_trans_back;
             try eapply transitive_closure_appx;
             eassumption.
       +++ admit.
    ++ admit.
  + specialize (H10 H15 H9); specialize (H11 H14 H0); remove_premise eauto.
    specialize (H11 xl1 xr1); ii.
    destruct (classic (halt (tapp H14 xl1))).
    ++ Deduct @sem_eq_halt; eauto; []; simpl in *; destruct_exists; ii.
       specialize (H17 H11 H13).
       assert (sem_eq H11 H13) by (eapply sem_eq_eval; simpl in *; ii; eassumption).
       remove_premise eauto.
       eapply sem_eq_trans_back; try eapply transitive_closure_appx; eassumption.
    ++ admit.
  + specialize (H10 H12 H9); remove_premise eauto.
    specialize (H10 xl1 xr1); ii.
    destruct (classic (halt (tapp H12 xl1))).
    ++ pose proof (sem_eq_halt (tapp H12 xl1) (tapp H9 xr1));
         simpl in *; remove_premise eauto;
           destruct_exists; ii;
             use_trans_val_det; cleanPS tauto.
       specialize (H14 H10 H17); ii.
       specialize (H14 xl0 xr0); ii.
       eapply sem_eq_trans_back; try eapply transitive_closure_appf; eassumption.
    ++ admit.
  + specialize (H7 H9 H6); remove_premise eauto.
    specialize (H7 xl0 xr0); ii.
    destruct (classic (halt (tapp H9 xl0))).
    ++ pose proof (sem_eq_halt (tapp H9 xl0) (tapp H6 xr0)); simpl in *; remove_premise eauto;
         destruct_exists; ii.
       specialize (H11 H7 H14); remove_premise eauto.
       specialize (H11 xl0 xr0); ii.
       eapply sem_eq_trans_back; try eapply transitive_closure_appf; eassumption.
    ++ admit.
  + pose proof (H7 H9 H6); remove_premise eauto.
    admit. (*cannot prove*)
Admitted.

Hint Resolve sem_eq_refl.

Definition red_sem_eq { A } (x y : term A) : red x y -> sem_eq x y.
  induction A; simpl; ii; repeat destruct_exists; ii;
    use_red_trans_val; use_trans_val_trans; use_trans_val_eq;
      repeat (Apply @app_eq; ii; subst); discharge_app_eq; eauto.
Admitted.

Hint Resolve red_sem_eq.

Definition sem_eq_transitive { A } (x y z : term A) : sem_eq x y -> sem_eq y z -> sem_eq x z.
  induction A; simpl in *; ii; remove_premise eauto; repeat destruct_exists; ii;
    use_trans_val_det; cleanPS tauto; repeat Apply @vsum; repeat Apply @vprod;
      repeat
        match goal with
        | H : _ + _ |- _ => destruct H
        end;
      repeat destruct_exists;
      repeat (
          try Apply @app_eq;
          subst;
          try discharge_app_eq;
          ii);
      eauto.
  + eapply H3.
    eapply H2.
    eauto.
  + eapply H2.
    eapply H3.
    eauto.
    (*very similar to the first, but at most one can be solved with naive automation...*)
  + eapply IHA1.
    apply H0; ii; eauto.
    apply H2; ii; eauto.
  + exfalso.
    eapply H9; ii; try eassumption; eauto.
  + exfalso.
    eapply H6; ii; try eassumption; eauto.
  + eapply IHA2.
    eapply H3; ii; eauto.
    eapply H4; ii; eauto.
  +  eapply H6; ii; try eassumption; eauto.
  + eapply H5; ii; try eassumption; eauto.
  + eapply H8; ii; try eassumption; eauto.
  + eapply H9; ii; try eassumption; eauto.
  + eapply IHA1.
    eapply H2; ii; try eassumption; eauto.
    eapply H3; ii; try eassumption; eauto.
  + eapply IHA2.
    eapply H2; ii; try eassumption; eauto.
    eapply H3; ii; try eassumption; eauto.
  + eapply IHA2.
    eapply H2; ii; eassumption.
    eapply H3; ii; try eassumption; eauto.
Defined.

Definition trans_sem_eq { A } (x y : term A) :
  transitive_closure red x y -> sem_eq x y.
  induction 1; eauto.
Admitted.

Class Gradient A :=
  {
    gcd : forall (gc : Term (tyreal ~> A)) (gd : Term (A ~> tyreal)), Prop;
    gcd_id : forall gc gd, gcd gc gd -> sem_eq (fB__ gd gc _ _) tI;
    gzro : Term A;
    gplus : Term (A ~> A ~> A);
    gplus_ : Term A -> Term (A ~> A) := fapp gplus;
    gplus__ : Term A -> Term A -> Term A := fun x => fapp (gplus_ x);
    gmult : Term (tyreal ~> A ~> A);
    gmult_ : Term tyreal -> Term (A ~> A) := fapp gmult;
    gmult__ : Term tyreal -> Term A -> Term A := fun x => fapp (gmult_ x)
  }.

Instance GUnit : Gradient tytop :=
  {
    gcd gc gd := False;
    gcd_id := ltac:(simpl in *; ii);
    gzro := ftt;
    gplus := fK_ (fK_ ftt);
    gmult := fK_ (fK_ ftt)
  }.

Instance GReal : Gradient tyreal :=
  {
    gcd gc gd := False;
    gcd_id := ltac:(simpl in *; ii);
    gzro := flit R0;
    gplus := fplus;
    gmult := fmult
  }.

Definition lift { repr Arg A } : repr A -> repr A + repr (Arg ~> A) := inl.
Definition var { repr A } { ftg : FTG repr } : repr A + repr (A ~> A) := inr fI.

Instance GProd A B { GA : Gradient A } { GB : Gradient B } : Gradient (typrod A B) :=
  {
    gcd gc gd := False;
    gcd_id := ltac:(simpl in *; ii);
    gzro := fapp (fapp fmkprod gzro) gzro;
    gplus := flam (flam (fmkprod__
                           (fapp (fapp (lift (lift gplus))
                                       (fzro_ (lift var)))
                                 (fzro_ var))
                           (fapp (fapp (lift (lift gplus))
                                       (ffst_ (lift var)))
                                 (ffst_ var))));
    gmult := flam (flam (fmkprod__
                           (fapp (fapp (lift (lift gmult))
                                       (lift var))
                                 (fzro_ var))
                           (fapp (fapp (lift (lift gmult))
                                       (lift var))
                                 (ffst_ var))))
  }.

Instance GRealArr A { GA : Gradient A } : Gradient (tyreal ~> A) :=
  {
    gcd gc gd := False;
    gcd_id := ltac:(simpl in *; ii);
    gzro := fK_ gzro;
    gplus :=
      let NR := Next _ tyreal in
      flam (flam  (flam
                     (fapp
                        (fapp (lift (lift (lift (gplus))))
                              (fapp (lift var) var))
                        (fapp (lift (lift var)) var))));
    gmult := flam (flam (fB__ var (fmult_ (lift var))))
  }.

Instance GProdArr A B C { GAC : Gradient (A ~> C) } { GBC : Gradient (B ~> C) }
         { GA : Gradient A } { GB : Gradient B } { GC : Gradient C } :
  Gradient (typrod A B ~> C) :=
  {
    gcd gc gd := False;
    gcd_id := ltac:(simpl in *; ii);
    gzro := fK_ gzro;
    gmult :=
      flam (flam (fB__ var (lift (fapp (lift gmult) var))));
    gplus :=
      let abcac : Term ((typrod A B ~> C) ~> (A ~> C)) :=
          (fC__ fB (fC__ fmkprod gzro)) in
      let abcbc : Term ((typrod A B ~> C) ~> (B ~> C)) :=
          (fC__ fB (fmkprod_ gzro)) in
      let NABCL := Next Term (typrod A B ~> C) in
      let NABCR := Next _ (typrod A B ~> C) (orig := NABCL) in
      let NAB := Next _ (typrod A B) (orig := NABCR) in
      flam (flam (flam
                    (fapp (fapp
                             (lift (lift (lift gplus)))
                             (fapp (fapp
                                      (fapp
                                         (lift (lift (lift gplus)))
                                         (fapp
                                            (lift (lift (lift abcac)))
                                            (lift (lift var))))
                                      (fapp (lift (lift (lift abcac))) (lift var)))
                                   (fzro_ var)))
                          (fapp (fapp (fapp
                                         (lift (lift (lift gplus)))
                                         (fapp
                                            (lift (lift (lift abcbc)))
                                            (lift (lift var))))
                                      (fapp
                                         (lift (lift (lift abcbc)))
                                         (lift var)))
                                (ffst_ var)))))
  }.

Fixpoint with_grad G A :=
  match A with
  | tyreal => typrod tyreal G
  | tytop => tytop
  | tybot => tybot
  | tysum L R => tysum (with_grad G L) (with_grad G R)
  | typrod L R => typrod (with_grad G L) (with_grad G R)
  | L ~> R => (with_grad G L) ~> (with_grad G R)
  end.

Variable tdiff : forall { G A } { grad : Gradient G }, term A -> term (with_grad G A).

Variable text : forall { G A } { grad : Gradient G }, term (with_grad G A) -> term A.

Fixpoint toTerm { A : type } (t : term A) : Term A :=
  match t in term A' return Term A' with
  | tapp f x => fapp (toTerm f) (toTerm x)
  | ttt => ftt
  | texf => fexf
  | tlit r => flit r
  | tplus => fplus
  | tminus => fminus
  | tmult => fmult
  | tdiv => fdiv
  | tleft => fleft
  | tright => fright
  | tsummatch => fsummatch
  | tmkprod => fmkprod
  | tzro => fzro
  | tfst => ffst
  | tS => fS
  | tK => fK
  | tI => fI
  | tB => fB
  | tC => fC
  | tW => fW
  | tY => fY
  end.

Fixpoint drel { G } { T : type } { GA : Gradient G } : term T -> Prop :=
  match T with
  | tytop => fun _ => True
  | tybot => fun _ => True
  | tyreal => fun _ => True
  | tysum _ _ => fun t => (forall t', eval_to t (tapp tleft t') -> drel t') /\
                      (forall t', eval_to t (tapp tright t') -> drel t')
  | typrod _ _ => fun t => forall l r, eval_to t (tapp (tapp tmkprod l) r) -> drel l /\ drel r
  | A ~> B => fun f =>
               (forall x, rel x -> rel (tapp f x)) /\
               (forall (EQ : A ~> B = tyreal ~> tyreal)
                  (gc : Term (tyreal ~> G))
                  (gd : Term (G ~> tyreal)),
                   gcd gc gd ->
                   forall df,
                     term_denote
                       (fB__
                          (fB__
                             (fB__ gd ffst _ _)
                             (tdiff
                                (eq_rect (A ~> B) term f (tyreal ~> tyreal) EQ) :
                                term (typrod tyreal G ~> typrod tyreal G)))
                          (fC__ tmkprod (tapp (gc _ _) (tlit R0))))
                       df ->
                     forall r (x : (derivable_pt df r)), 
                       term_denote
                         (tapp (eq_rect (A ~> B) term f (tyreal ~> tyreal) EQ) (tlit r))
                         (derive_pt _ r x))
  end.

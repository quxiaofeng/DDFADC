Require Export Rel CoqUtil.Fix.

Definition Z_or_val { ty } :
  forall (x : term ty), hasZ x \/ halt x.
  intros x.
  pose proof (rel_hold ty x).
  destruct (hasZ_dec x); ii.
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
    fZ { A B } : repr (((A ~> B) ~> (A ~> B)) ~> (A ~> B));
    fZ_ { A B } : _ := fapp (@fZ A B);
    fZ__ { A B } f : _ := fapp (@fZ_ A B f)
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
    fZ A B := tZ
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
    fZ A B := inl fZ
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
    fZ A B := fun _ _ => fZ
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

Ltac discharge_app_eq :=
  repeat
    match goal with
    | H : tapp _ _ = tapp _ _ |- _ => solve [inversion H]
    end.

Definition sem_eq_arr { A B } fl fr :
  val fl -> val fr ->
  (forall xl xr, sem_eq xl xr -> val xl -> val xr -> sem_eq (@tapp A B fl xl) (tapp fr xr)) ->
  sem_eq fl fr.
  simpl in *; unfold eval_to; ii; use_trans_val_eq; eauto.
Defined.

Definition sem_eq_eval_back { A } (x y x' y' : term A) :
  eval_to x x' -> eval_to y y' -> sem_eq x' y' -> sem_eq x y.
  destruct A; simpl in *; unfold eval_to;
    ii; remove_premise eauto; repeat destruct_exists; ii;
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
        unfold eval_to in *;
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
  destruct A; simpl in *; unfold eval_to;
    ii; remove_premise eauto; repeat destruct_exists; ii;
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
        unfold eval_to in *;
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
  ltac:(induction A; simpl in *; unfold eval_to; ii; destruct_exists; ii; eauto; work).

Definition sem_eq_symm { A } (x y : term A) : sem_eq x y -> sem_eq y x.
  induction A; simpl; unfold eval_to; ii; remove_premise eauto; repeat destruct_exists; ii;
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
        unfold eval_to in *;
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
        unfold eval_to in *;
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

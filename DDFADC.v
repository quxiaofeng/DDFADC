Require Export SemEq.

Definition with_bot := option.

Fixpoint type_denote_par_only_val (t : type) : Type :=
  match t with
  | tyreal => R
  | tytop => unit
  | tybot => False
  | tysum l r => (type_denote_par_only_val l + type_denote_par_only_val r)%type
  | typrod l r => (type_denote_par_only_val l * type_denote_par_only_val r)%type
  | l ~> r => type_denote_par_only_val l -> with_bot (type_denote_par_only_val r)
  end.

Definition type_denote_par t := with_bot (type_denote_par_only_val t).

Fixpoint term_denote_par_os { A } : term A -> type_denote_par A -> Prop :=
  match A with
  | tytop => fun t d =>
              match d with
              | Some tt => halt t
              | None => ~ halt t
              end
  | tybot => fun t d =>
              match d with
              | Some f => False_rect Prop f
              | None => True
              end
  | tyreal => fun t d =>
               match d with
               | Some r => eval_to t (tlit r)
               | None => ~ halt t
               end
  | tysum _ _ => fun t d =>
                  match d with
                  | Some (inl dl) =>
                    exists tl, eval_to t (tapp tleft tl) /\ term_denote_par_os tl (Some dl)
                  | Some (inr dr) =>
                    exists tr, eval_to t (tapp tright tr) /\ term_denote_par_os tr (Some dr)
                  | None => ~ halt t
                  end
  | typrod _ _ => fun t d =>
                   match d with
                   | Some (dl, dr) =>
                     exists tl tr, eval_to t (tapp (tapp tmkprod tl) tr) /\
                              term_denote_par_os tl (Some dl) /\
                              term_denote_par_os tr (Some dr)
                   | None => ~ halt t
                   end
  | _ ~> _ => fun t d =>
               match d with
               | Some df =>
                 exists tf, eval_to t tf /\
                       forall tx dx,
                         term_denote_par_os tx (Some dx) ->
                         term_denote_par_os (tapp tf tx) (df dx)
               | None => ~ halt t
               end
  end. (*refactor the trivial None case*)

Definition term_denote_par_os_halt { A } (t : term A) d :
  term_denote_par_os t (Some d) -> halt t.
  destruct A; simpl in *; repeat (destruct_exists; repeat match_destruct; ii); eauto.
Defined.

Definition term_denote_par_os_not_halt { A } (t : term A) :
  term_denote_par_os t None -> ~ halt t.
  destruct A; simpl in *; repeat (destruct_exists; repeat match_destruct; ii);
    unfold eval_to in *; ii; work; eauto.
Defined.

Fixpoint term_denote_par { A } (t : term A) : type_denote_par A -> Prop :=
  let auto_resolve := LEq in
  match t with
  | tapp f x => (fun td => exists f' x',
                    term_denote_par f f' /\ term_denote_par x x' /\
                    match f', x' with
                    | Some f', Some x' => eq td (f' x')
                    | _, _ => eq td None
                    end)
  | ttt => eq (Some tt)
  | texf => eq (Some (fun _ => None))
  | tlit x => eq (Some x)
  | tplus => eq (Some (fun l => Some (fun r => Some (Rplus l r))))
  | tminus => eq (Some (fun l => Some (fun r => Some (Rminus l r))))
  | tmult => eq (Some (fun l => Some (fun r => Some (Rmult l r))))
  | tdiv => eq (Some (fun l => Some (fun r => Some (Rdiv l r))))
  | tleft => eq (Some (fun l => Some (inl l)))
  | tright => eq (Some (fun r => Some (inr r)))
  | tsummatch => eq (Some (fun a => Some (fun b => Some (fun c =>
                                                    match a with
                                                    | inl l => b l
                                                    | inr r => c r
                                                    end))))
  | tmkprod => eq (Some (fun l => Some (fun r => Some (l, r))))
  | tzro => eq (Some (fun p => Some (fst p)))
  | tfst => eq (Some (fun p => Some (snd p)))
  | tS => eq (Some (fun f => Some (fun x => Some (fun arg =>
                                             match f arg, x arg with
                                             | Some f', Some x' => f' x'
                                             | _, _ => None
                                             end))))
  | tK => eq (Some (fun a => Some (fun b => Some a)))
  | tI => eq (Some Some)
  | tB => eq (Some (fun f => Some (fun g => Some (fun x => match g x with
                                                 | Some x' => f x'
                                                 | _ => None
                                                 end))))
  | tC => eq (Some (fun f => Some (fun a => Some (fun b => match f b with
                                                 | Some f' => f' a
                                                 | _ => None
                                                 end))))
  | tW => eq (Some (fun f => Some (fun x => match f x with
                                     | Some f' => f' x
                                     | _ => None
                                     end)))
  | tZ => (fun td =>
            match td with
            | Some Z => forall f,
                match Z f with
                | Some ZF => is_fixpoint (fun x => match f x with
                                               | Some fx => fx
                                               | None => (fun _ => None)
                                               end) ZF : Prop (*should be least fix point*)
                | None => False
                end
            | None => False
            end)
  end.

Definition term_denote_par_exists { A } (t : term A) : exists d, term_denote_par t d.
  induction t; simpl in *; destruct_exists; eauto.
  + exists (match IHt1, IHt2 with
       | Some f, Some x => f x
       | _, _ => None
       end); exists IHt1; exists IHt2; ii; repeat match_destruct; ii.
  + admit. (*it is wrong definition anyway, dont bother proofing it*)
Admitted.

Definition term_denote_par_os_exists { A } (t : term A) : exists d, term_denote_par_os t d.
  induction t; simpl in *;
    repeat (destruct_exists;
            repeat match_destruct;
            ii);
    eauto.
Admitted.

Ltac to_false L :=
  match goal with
  | |- ?G => let H := fresh in try (assert (H : ~ G) by L; clear H; exfalso)
  end.

Require Export FunctionalExtensionality.

Goal forall A t dl dr, @term_denote_par A t dl -> @term_denote_par A t dr -> dl = dr.
  induction t; repeat (simpl in *; ii; destruct_exists; repeat match_destruct; subst);
    repeat
      match goal with
      | H : term_denote_par ?t ?x, H1 : term_denote_par ?t ?y |- _ =>
        (specialize (IHt1 _ _ H H1); invcs IHt1) ||
                                                 (specialize (IHt2 _ _ H H1); invcs IHt2)
      end; ii.
  admit (*case Z*).
Admitted.

Goal forall A t dl dr, @term_denote_par_os A t dl -> @term_denote_par_os A t dr -> dl = dr.
  induction A;
    repeat (
        simpl in *;
        ii;
        repeat match_destruct;
        use_trans_val_det;
        unfold eval_to in *;
        repeat
          match goal with
          | H : tlit _ = tlit _ |- _ => invcs H
          | H : _ = _ |- _ => solve [inversion H]
          end;
        to_false discriminate;
        destruct_exists;
        repeat Apply @app_eq;
        subst);
    eauto.
  specialize (IHA1 H0 (Some t1) (Some t0)); ii; invcs H8; ii.
  specialize (IHA2 H0 (Some t1) (Some t0)); ii; invcs H8; ii.
  specialize (IHA1 H0 (Some t2) (Some t0)); specialize (IHA2 H1 (Some t3) (Some t1)); ii;
    invcs H12; invcs H; ii.
  admit.
Admitted.

Definition eval_to_f { A B } (f g : term (A ~> B)) x :
  val (tapp g x) -> eval_to f g -> eval_to (tapp f x) (tapp g x).
  unfold eval_to; ii; work.
  eapply transitive_closure_transitive; try eapply transitive_closure_appf; eauto.
Defined.

Hint Resolve eval_to_f.

Definition eval_to_x { A B } (f : term (A ~> B)) x y :
  val (tapp f y) -> eval_to x y -> eval_to (tapp f x) (tapp f y).
  unfold eval_to; ii; work.
  eapply transitive_closure_transitive; try eapply transitive_closure_appx; eauto.
Defined.

Hint Resolve eval_to_x.

Definition term_denote_par_os_trans_back { A } t t' d :
  transitive_closure red t t' -> @term_denote_par_os A t' d -> @term_denote_par_os A t d.
  destruct A;
    repeat (simpl in *;
            ii;
            repeat match_destruct;
            unfold eval_to in *;
            destruct_exists;
            use_trans_val_trans);
    (econstructor; econstructor + idtac) + idtac;
    ii; try eapply transitive_closure_transitive; try eassumption; solve [eauto].
Defined.

Definition term_denote_par_os_trans { A } t t' d :
  transitive_closure red t t' -> @term_denote_par_os A t d -> @term_denote_par_os A t' d.
  destruct A;
    repeat (simpl in *;
            ii;
            repeat match_destruct;
            unfold eval_to in *;
            destruct_exists;
            use_trans_val_trans);
    eauto;
    try
      match goal with
      | H : _ -> False |- _ => apply H
      end;
    try ((econstructor; econstructor + idtac) + idtac;
         ii; try eapply transitive_closure_transitive; try eassumption; solve [eauto]).
Defined.

Goal forall A t d, @term_denote_par A t d -> @term_denote_par_os A t d.
  induction t; simpl in *;
    repeat (
        destruct_exists;
        repeat match_destruct;
        ii; subst;
        try
          match goal with
          | |- exists _, _ => econstructor; ii; [solve[eauto]|]
          end);
    eauto.
  specialize (IHt1 (Some t)); ii; destruct_exists; ii.
  assert (term_denote_par_os (tapp H0 t2) (t t0)) by eauto.
  admit.
  admit.
  admit.
  econstructor; ii; solve [eauto].
  all:
    try (unfold eval_to in *; ii; eauto; [];
         eapply transitive_closure_transitive;
         try eapply transitive_closure_appx; try eassumption; solve [eauto]).
  Deduct @term_denote_par_os_halt; unfold halt, eval_to in *; destruct_exists; ii.
  econstructor; ii.
  eapply eval_to_x.
Admitted.

Goal forall A t d, @term_denote_par_os A t d -> @term_denote_par A t d.
  induction t; simpl in *;
    repeat (ii;
            unfold eval_to in *;
            repeat match_destruct;
            to_false discriminate;
            destruct_exists;
            repeat
              match goal with
              | |- Some _ = Some _ => apply f_equal
              | H : tlit _ = tlit _ |- _ => invcs H
              end;
            repeat ext;
            use_trans_val_eq_with eauto); eauto.
  (*pose proof (term_denote_par_exists t1);
    pose proof (term_denote_par_exists t2);
    destruct_exists;
    do 2 econstructor; ii; try eassumption; [];
      specialize (IHt1 H0); specialize (IHt2 H1); ii.
  repeat match_destruct; ii.
  admit.
  admit.
  admit.*)
  admit.
  + specialize (H3 (tlit H1) H1); remove_premise eauto.
    match_destruct; try (exfalso; solve [eauto]); [].
    destruct_exists; ii.
    apply f_equal; ext.
    specialize (H7 (tlit H6) H6); remove_premise eauto.
    use_trans_val_eq_with eauto.
    match_destruct; ii; try (exfalso; solve [eauto]); [].
    use_trans_val_eq_with eauto.
    dependent destruction H13.
    dependent destruction H9; try (Apply red_not_val; exfalso; solve [eauto]); [].
    use_trans_val_eq_with eauto.
    invcs H15; ii.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + destruct (t H1) eqn:?.
    apply f_equal; ext.
    match_destruct.
    admit.
    admit.
    admit.
  + admit.
  + admit.
Admitted.

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
Admitted.

Definition term_denote_trans { A } (l r : term A) x :
  transitive_closure red l r -> term_denote l x -> term_denote r x :=
  ltac:(induction 1; eauto using term_denote_red).

Definition term_denote_red_back { A } (l r : term A) x :
  red l r -> term_denote r x -> term_denote l x.
  destruct A; ii; simpl in *;
    repeat (destruct_exists; ii;
            try match_destruct); eauto 7.
Admitted.

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
        unfold eval_to in *;
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
    Deduct (term_denote_halt x0); simpl in *; destruct_exists; unfold eval_to in *; ii; [].
    eapply sem_eq_trans_back; try eapply transitive_closure_appx; try eassumption.
    eapply H2; ii; eauto.
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
            unfold eval_to in *;
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
          unfold eval_to in *;
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
       +++ Deduct @sem_eq_halt; eauto; [];
             simpl in *; unfold eval_to in *; destruct_exists; ii.
           specialize (H19 H11 H18).
           assert (sem_eq H11 H18) by
               (eapply sem_eq_eval; simpl in *; ii; unfold eval_to; ii; eassumption).
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
    ++ Deduct @sem_eq_halt; eauto; []; simpl in *; unfold eval_to in *; destruct_exists; ii.
       specialize (H17 H11 H13).
       assert (sem_eq H11 H13) by
           (eapply sem_eq_eval; simpl in *; unfold eval_to; ii; eassumption).
       remove_premise eauto.
       eapply sem_eq_trans_back; try eapply transitive_closure_appx; eassumption.
    ++ admit.
  + specialize (H10 H12 H9); remove_premise eauto.
    specialize (H10 xl1 xr1); ii.
    destruct (classic (halt (tapp H12 xl1))).
    ++ pose proof (sem_eq_halt (tapp H12 xl1) (tapp H9 xr1));
         simpl in *; unfold eval_to in *; remove_premise eauto;
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
    cleanPS tauto;
      simpl in *; unfold eval_to in *;
        repeat
          match goal with
          | H : _ + _ |- _ => destruct H
          end;
        repeat (
            try Apply @vsum;
            try Apply @vprod;
            try Apply @app_eq;
            destruct_exists;
            subst;
            try discharge_app_eq;
            ii;
            use_trans_val_det);
        cleanPS tauto; eauto.
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
  + eapply H6; ii; try eassumption; eauto.
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
  | tZ => fZ
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

From Coq Require List NArith.
From mathcomp Require eqtype.
From Wasm Require memory host opsem properties.

Module AuthCallContext.
Import List NArith eqtype memory host opsem properties.
Import AuthEntry AuthTraps AuthOuter.
Import ListNotations.
Local Open Scope list_scope.

Section Invariants.
Context {hf : host_function_class} {mem : Memory} (h : @host hf mem).
Local Notation state := (host_state -> store_record -> frame ->
                         list administrative_instruction -> Prop).

(** A body can bytecode-branch out of its surrounding label or return out
    of its frame. Both exits must be excluded by the invariant. *)
Record nonreturning (P : state) : Prop := {
  nr_step : forall hs s f es hs' s' f' es', P hs s f es ->
    @reduce hf mem h hs s f es hs' s' f' es' -> P hs' s' f' es';
  nr_values : forall hs s f es, P hs s f es -> const_list es = true -> False;
  nr_branch : forall hs s f es k (lh : lholed k) vs, P hs s f es ->
    const_list vs = true -> lfill lh (vs ++ [AI_basic (BI_br (N.of_nat k))]) = es -> False;
  nr_return : forall hs s f es k (lh : lholed k) vs, P hs s f es ->
    const_list vs = true -> lfill lh (vs ++ [AI_basic BI_return]) = es -> False;
  nr_tail : forall hs s f es k (lh : lholed k) vs a, P hs s f es ->
    const_list vs = true -> lfill lh (vs ++ [AI_return_invoke a]) = es -> False
}.

Definition protected (Q : state) : state := fun hs s _ es =>
  code_status es = active_trap \/
  exists n f body, es = [AI_frame n f body] /\ Q hs s f body.

Ltac impossible_exit E :=
  let F := fresh "active" in pose proof (f_equal entry_first E) as F;
  revert F; entry_simpl_first; discriminate.

Ltac trapped_exit T E :=
  rewrite <- E, status_fill, status_const_prefix in T;
  try discriminate; try assumption;
  try (rewrite status_const_prefix by assumption; discriminate).

Lemma exit_nonempty {A} (vs : list A) (op : A) : vs ++ [op] <> [].
Proof. intro E. apply app_eq_nil in E as [_ E]. discriminate. Qed.

Ltac protected_exit :=
  intros * [T|[n [inner [body [-> Qbody]]]]] V E;
  [solve [trapped_exit T E] |
   let Nonempty := fresh "Nonempty" in
   match type of E with lfill _ ?xs = _ =>
     assert (Nonempty : xs <> []) by apply exit_nonempty
   end;
   destruct (singleton_frame_context _ _ _ [] _ _ _ Nonempty E) as [Bad _];
   impossible_exit Bad].

Lemma protected_nonreturning (Q : state)
    (closed : forall hs s f es hs' s' f' es', Q hs s f es ->
      @reduce hf mem h hs s f es hs' s' f' es' -> Q hs' s' f' es')
    (values : forall hs s f es, Q hs s f es -> const_list es = true -> False)
    (returns : forall hs s f es k (lh : lholed k) vs, Q hs s f es ->
      const_list vs = true -> lfill lh (vs ++ [AI_basic BI_return]) = es -> False)
    (tails : forall hs s f es k (lh : lholed k) vs a, Q hs s f es ->
      const_list vs = true -> lfill lh (vs ++ [AI_return_invoke a]) = es -> False) :
  nonreturning (protected Q).
Proof.
  constructor.
  - intros * [T|[n [inner [body [-> Qbody]]]]] R.
    + left. eapply (proj2 (status_reduce h _ _ _ _ _ _ _ _ R)); exact T.
    + destruct (step_outer h Q closed values returns tails _ _ _ _ _ _ _ _ R
                  n inner body Logic.eq_refl Qbody) as [->|Inside]; [left; reflexivity|right; exact Inside].
  - intros * [T|[n [inner [body [-> Qbody]]]]] V.
    + rewrite status_const in T by exact V. discriminate.
    + discriminate.
  - protected_exit.
  - protected_exit.
  - protected_exit.
Qed.

(** Inverting the public label context that focuses a singleton label gives
    either the label itself or a step in its body. *)
Lemma singleton_label_context k (lh : lholed k) es next n cont inner :
  es <> [] -> lfill lh es = [AI_label n cont inner] ->
  (es = [AI_label n cont inner] /\ lfill lh next = next) \/
  exists j (sub : lholed j), lfill sub es = inner /\
    lfill lh next = [AI_label n cont (lfill sub next)].
Proof.
  intros Nonempty E. destruct lh as [vs suffix|k vs arity target sub suffix];
    simpl in E |- *; repeat rewrite cat_app in *;
    destruct vs as [|v vs]; simpl in E |- *.
  - left. destruct es as [|e es]; [contradiction|]. injection E as A B.
    apply app_eq_nil in B as [-> ->]. rewrite app_nil_r. subst e; auto.
  - injection E as A B. apply app_eq_nil in B as [_ B].
    apply app_eq_nil in B as [B _]. contradiction.
  - injection E as <- <- A ->. right. exists k, sub; auto.
  - injection E as A B. apply app_eq_nil in B as [_ B]. discriminate.
Qed.

Definition labeled (P : state) : state := fun hs s f es =>
  code_status es = active_trap \/
  exists n cont inner, es = [AI_label n cont inner] /\ P hs s f inner.

Section Label.
Variable P : state.
Variable valid : nonreturning P.

Lemma simple_label es es' : reduce_simple es es' ->
  forall hs s f n cont inner, es = [AI_label n cont inner] ->
    P hs s f inner -> labeled P hs s f es'.
Proof.
  intro Step. destruct Step; intros hs0 s0 fr ar con body Eq Safe;
    try solve [try subst ves; impossible_exit Eq].
  - inversion Eq; subst. exfalso. eapply nr_values; eauto.
  - left; reflexivity.
  - inversion Eq; subst. exfalso. eapply nr_branch; eauto.
  - left; reflexivity.
Qed.

Lemma step_label hs s f es hs' s' f' es' :
  @reduce hf mem h hs s f es hs' s' f' es' ->
  forall n cont inner, es = [AI_label n cont inner] ->
    P hs s f inner -> labeled P hs' s' f' es'.
Proof.
  intro Step. induction Step; intros ar con body Eq Safe;
    try solve [try subst ves; impossible_exit Eq].
  - eapply simple_label; eauto.
  - subst les les'. destruct (singleton_label_context _ _ _ es' _ _ _
        (reduce_not_nil Step) Eq) as [[Source ->]|[j [sub [<- ->]]]].
    + eapply IHStep; eauto.
    + right. repeat eexists. eapply nr_step; [exact valid|exact Safe|].
      eapply r_label; eauto.
Qed.

Ltac labeled_exit field :=
  intros * [T|[label_arity [con [body [-> Inside]]]]] V E;
  [solve [trapped_exit T E] |
   let Nonempty := fresh "Nonempty" in
   match type of E with lfill _ ?xs = _ =>
     assert (Nonempty : xs <> []) by apply exit_nonempty
   end;
   destruct (singleton_label_context _ _ _ [] _ _ _ Nonempty E)
     as [[Bad _]|[j [sub [Focus _]]]]; [impossible_exit Bad|eapply field; eauto]].

Lemma label_frame_no_results hs s caller n fr arity cont inner hs' s' caller' results :
  P hs s fr inner ->
  ~ @reduce_trans hf mem h (hs,s,caller,[AI_frame n fr [AI_label arity cont inner]])
                            (hs',s',caller',v_to_e_list results).
Proof.
  intro Safe. apply (frame_no_results h (labeled P)).
  - intros * [T|[ar [con [body [-> Inside]]]]] Step.
    + left; eapply (proj2 (status_reduce h _ _ _ _ _ _ _ _ Step)); exact T.
    + eapply step_label; eauto.
  - intros * [T|[ar [con [body [-> Inside]]]]] V.
    + rewrite status_const in T by exact V. discriminate.
    + discriminate.
  - labeled_exit nr_return.
  - labeled_exit nr_tail.
  - right. eauto 8.
Qed.
End Label.
End Invariants.
End AuthCallContext.

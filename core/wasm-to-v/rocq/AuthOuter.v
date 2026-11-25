From Coq Require List Relations.Relation_Operators Relations.Operators_Properties.
From mathcomp Require eqtype.
From Wasm Require memory host opsem properties.

Module AuthOuter.
Import List Relation_Operators Operators_Properties.
Import eqtype.
Import memory host opsem properties.
Import AuthEntry AuthTraps.
Import ListNotations.
Local Open Scope list_scope.

Section OuterFrame.
Context {hf : host_function_class} {mem : Memory} (h : @host hf mem).
Variable P : host_state -> store_record -> frame -> list administrative_instruction -> Prop.
Hypothesis closed_step : forall hs s f es hs' s' f' es',
  P hs s f es -> @reduce hf mem h hs s f es hs' s' f' es' -> P hs' s' f' es'.
Hypothesis no_values : forall hs s f es, P hs s f es -> const_list es = true -> False.
Hypothesis no_return : forall hs s f es k (lh : lholed k) vs,
  P hs s f es -> const_list vs = true -> lfill lh (vs ++ [AI_basic BI_return]) = es -> False.
Hypothesis no_tail : forall hs s f es k (lh : lholed k) vs a,
  P hs s f es -> const_list vs = true -> lfill lh (vs ++ [AI_return_invoke a]) = es -> False.

Definition outer_state hs s es := es = [AI_trap] \/
  exists n f inner, es = [AI_frame n f inner] /\ P hs s f inner.

Lemma singleton_frame_context k (lh : lholed k) es next n f inner :
  es <> [] -> lfill lh es = [AI_frame n f inner] ->
  es = [AI_frame n f inner] /\ lfill lh next = next.
Proof.
  intros Nonempty E. destruct lh as [vs suffix|k vs arity cont lh suffix].
  - simpl in E |- *. repeat rewrite cat_app in *.
    destruct vs as [|v vs]; simpl in E |- *.
    + destruct es as [|e es]; [contradiction|]. injection E as A B.
      apply app_eq_nil in B as [-> ->]. rewrite app_nil_r. subst e. split; reflexivity.
    + injection E as A B. apply app_eq_nil in B as [_ B].
      apply app_eq_nil in B as [B _]. contradiction.
  - simpl in E. repeat rewrite cat_app in E.
    destruct vs as [|v vs]; simpl in E; [discriminate|].
    injection E as A B. apply app_eq_nil in B as [_ B]. discriminate.
Qed.

Ltac outer_impossible E :=
  let F := fresh "first" in pose proof (f_equal entry_first E) as F;
  revert F; entry_simpl_first; discriminate.

Lemma simple_outer es es' : reduce_simple es es' ->
  forall hs s n f body, es = [AI_frame n f body] -> P hs s f body -> outer_state hs s es'.
Proof.
  intro Step. destruct Step; intros hs0 s0 ar fr body Eq Safe;
    try solve [try subst ves; outer_impossible Eq].
  - inversion Eq; subst. exfalso. eapply no_values; eauto.
  - left; reflexivity.
  - inversion Eq; subst. exfalso. eapply no_return; eauto.
  - left; reflexivity.
Qed.

Lemma step_outer hs s caller es hs' s' caller' es' :
  @reduce hf mem h hs s caller es hs' s' caller' es' ->
  forall n fr body, es = [AI_frame n fr body] -> P hs s fr body -> outer_state hs' s' es'.
Proof.
  intro Step. induction Step; intros ar fr body Eq Safe;
    try solve [try subst ves; outer_impossible Eq].
  - eapply simple_outer; eauto.
  - inversion Eq; subst. exfalso. eapply no_tail; eauto.
  - subst les les'. destruct (singleton_frame_context _ _ _ es' _ _ _
        (reduce_not_nil Step) Eq) as [Source ->]. eapply IHStep; eauto.
  - inversion Eq; subst. right. repeat eexists. eapply closed_step; eauto.
Qed.

Lemma frame_no_results hs s caller n fr inner hs' s' caller' results :
  P hs s fr inner ->
  ~ @reduce_trans hf mem h (hs,s,caller,[AI_frame n fr inner])
                            (hs',s',caller',v_to_e_list results).
Proof.
  intros Safe Run. apply clos_rt_rt1n in Run.
  remember (hs,s,caller,[AI_frame n fr inner]) as start eqn:E.
  remember (hs',s',caller',v_to_e_list results) as stop eqn:F.
  assert (Init : outer_state hs s [AI_frame n fr inner]) by (right; eauto 6).
  clear Safe.
  assert (forall hs0 s0 f0 es0, start = (hs0,s0,f0,es0) ->
       outer_state hs0 s0 es0 -> False) as Impossible.
  { clear E Init. revert F. induction Run as [x|x y z Step Rest IH]; intro F.
    - intros hs0 s0 f0 es0 Ex St. rewrite Ex in F. inversion F; subst.
      destruct St as [Eq|[ar [fr0 [body [Eq _]]]]]; apply (f_equal entry_first) in Eq;
        rewrite entry_first_values in Eq; discriminate.
    - intros hs0 s0 f0 es0 Ex St. subst x. destruct y as [[[hy sy] fy] ey].
      destruct St as [->|[ar [fr0 [body [-> Inside]]]]].
      + apply (trapped_no_results h hs0 s0 f0 [AI_trap] hs' s' caller' results Logic.eq_refl).
        rewrite <- F. apply clos_rt1n_rt. econstructor; eauto.
      + eapply IH; [exact F|reflexivity|]. eapply step_outer; eauto. }
  eapply Impossible; eauto.
Qed.
End OuterFrame.
End AuthOuter.

From Coq Require List Bool Lia.
From mathcomp Require eqtype.
From Wasm Require memory host opsem properties.

Module AuthEntry.
Import List Bool Lia.
Import eqtype.
Import memory host opsem properties.
Import ListNotations.
Local Open Scope list_scope.

(** The first non-value instruction of a flat operand stack. *)
Fixpoint entry_first (code : list administrative_instruction) : option administrative_instruction :=
  match code with
  | nil => None
  | e :: es => if is_const e then entry_first es else Some e
  end.

Lemma entry_first_app xs ys :
  entry_first (xs ++ ys) =
  match entry_first xs with None => entry_first ys | Some e => Some e end.
Proof.
  induction xs as [|x xs IH]; cbn [app entry_first]; auto.
  destruct (is_const x); auto.
Qed.

Lemma entry_first_value v : is_const (v_to_e v) = true.
Proof. unfold is_const. rewrite v2e2v. reflexivity. Qed.

Lemma entry_first_const xs : const_list xs = true -> entry_first xs = None.
Proof.
  induction xs as [|x xs IH]; cbn [const_list forallb entry_first]; auto.
  intro H. apply andb_true_iff in H as [Hx Hxs]. rewrite Hx. auto.
Qed.

Lemma entry_first_values xs : entry_first (v_to_e_list xs) = None.
Proof. apply entry_first_const, v_to_e_const. Qed.

Lemma entry_values_app xs ys :
  v_to_e_list (xs ++ ys) = v_to_e_list xs ++ v_to_e_list ys.
Proof. symmetry. apply v_to_e_cat. Qed.

Ltac entry_simpl_first :=
  repeat first [
    progress rewrite cat_app
  | progress rewrite entry_first_app
  | progress rewrite entry_first_values
  | match goal with H : is_true (const_list ?xs) |- context[entry_first ?xs] =>
        progress rewrite (entry_first_const xs H) end
  | match goal with H : const_list ?xs = true |- context[entry_first ?xs] =>
        progress rewrite (entry_first_const xs H) end
  | progress cbn [entry_first]
  | progress rewrite entry_first_value
  ].

Ltac entry_other_op :=
  let candidate := fresh "candidate" in let hyp := fresh "active" in
  split; [eexists; entry_simpl_first; reflexivity |
          intros candidate hyp; exfalso; revert hyp; entry_simpl_first; discriminate].

Lemma entry_simple_first es es' : reduce_simple es es' ->
  (exists op, entry_first es = Some op) /\
  (forall addr, entry_first es <> Some (AI_invoke addr)).
Proof.
  intros R; destruct R; try solve [entry_other_op].
  match goal with H : lfill _ _ = _ |- _ => rewrite <- H end.
  destruct lh; cbn [lfill]; entry_other_op.
Qed.

Section Semantics.
Context {hf : host_function_class} {mem : Memory} {h : @host hf mem}.

(** The three primitive invocation rules, with their administrative equalities
    normalized and their stack context left out. *)
Inductive entry_direct : host_state -> store_record -> frame -> funcaddr -> list value ->
                         host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
| entry_native : forall hs s f a args ts rs inst mf defaults,
    lookup_N (s_funcs s) a = Some (FC_func_native (Tf ts rs) inst mf) ->
    length args = length ts ->
    default_vals (modfunc_locals mf) = Some defaults ->
    entry_direct hs s f a args hs s f
      [AI_frame (length rs) (Build_frame (args ++ defaults) inst)
          [AI_label (length rs) [] (to_e_list (modfunc_body mf))]]
| entry_host_value : forall hs s f a args ts rs handle hs' s' result,
    lookup_N (s_funcs s) a = Some (FC_func_host (Tf ts rs) handle) ->
    length args = length ts ->
    @host_application hf mem h hs s (Tf ts rs) handle args hs' (Some (s', result)) ->
    entry_direct hs s f a args hs' s' f (result_to_stack result)
| entry_host_diverge : forall hs s f a args ts rs handle hs',
    lookup_N (s_funcs s) a = Some (FC_func_host (Tf ts rs) handle) ->
    length args = length ts ->
    @host_application hf mem h hs s (Tf ts rs) handle args hs' None ->
    entry_direct hs s f a args hs' s f [AI_trap].

(** Induction on public reduction also handles arbitrarily nested [r_label]
    derivations. Every step has an active instruction, so the suffix of a
    sequence context cannot supply an earlier active instruction. *)
Lemma entry_step_class hs s f es hs' s' f' es' :
  @reduce hf mem h hs s f es hs' s' f' es' ->
  (exists op, entry_first es = Some op) /\
  forall addr, entry_first es = Some (AI_invoke addr) ->
    exists prefix actuals tail out,
      es = v_to_e_list (prefix ++ actuals) ++ AI_invoke addr :: tail /\
      es' = v_to_e_list prefix ++ out ++ tail /\
      entry_direct hs s f addr actuals hs' s' f' out.
Proof.
  intro R; induction R; try solve [entry_other_op].
  - destruct (entry_simple_first _ _ H) as [active other].
    split; [exact active|]. intros a eq. exfalso. exact (other a eq).
  - subst. split; [eexists; entry_simpl_first; reflexivity|].
    intros ax E; revert E; entry_simpl_first; intro E; inversion E; subst.
    exists [], vs, [], [AI_frame (length ts2)
      (Build_frame (vs ++ defaults) inst)
      [AI_label (length ts2) [] (to_e_list es)]].
    repeat split; try reflexivity. eapply entry_native with (ts := ts1) (mf := Build_module_func x ts es); eauto using eq_sym.
  - subst. split; [eexists; entry_simpl_first; reflexivity|].
    intros ax E; revert E; entry_simpl_first; intro E; inversion E; subst.
    exists [], vcs, [], (result_to_stack r).
    split; [reflexivity|]. split; [cbn; rewrite app_nil_r; reflexivity|].
    eapply entry_host_value; eauto using eq_sym.
  - subst. split; [eexists; entry_simpl_first; reflexivity|].
    intros ax E; revert E; entry_simpl_first; intro E; inversion E; subst.
    exists [], vcs, [], [AI_trap]. repeat split; try reflexivity.
    eapply entry_host_diverge; eauto using eq_sym.
  - subst les les'. destruct lh as [lvs les | k lvs n cont lh les].
    + cbn [lfill]. repeat rewrite cat_app.
      destruct IHR as [[op Active] IH].
      repeat rewrite entry_first_app. rewrite entry_first_values, Active.
      split; [eauto|]. intros a Eq. inversion Eq; subst op.
      destruct (IH a Active) as [pre [args [tail [out [Src [Dst Step]]]]]].
      exists (lvs ++ pre), args, (tail ++ les), out.
      rewrite Src, Dst. repeat rewrite entry_values_app.
      repeat rewrite <- app_assoc. repeat split; auto.
    + cbn [lfill]. entry_other_op.
Qed.

Lemma entry_invoke_step hs s f args a tail hs' s' f' es' :
  @reduce hf mem h hs s f (v_to_e_list args ++ AI_invoke a :: tail) hs' s' f' es' ->
  exists prefix actuals out,
    args = prefix ++ actuals /\
    es' = v_to_e_list prefix ++ out ++ tail /\
    entry_direct hs s f a actuals hs' s' f' out.
Proof.
  intro R. destruct (entry_step_class _ _ _ _ _ _ _ _ R) as [_ classify].
  assert (Active : entry_first (v_to_e_list args ++ AI_invoke a :: tail) = Some (AI_invoke a)).
  { rewrite entry_first_app, entry_first_values. reflexivity. }
  destruct (classify a Active) as [pre [vs [rest [out [Src [Dst Direct]]]]]].
  apply const_list_concat_inv in Src as [Vals [_ Tail]];
    try apply v_to_e_const; try discriminate.
  apply v_to_e_inj in Vals. subst rest.
  exists pre, vs, out. auto.
Qed.

Lemma entry_direct_native hs s f a actuals hs' s' f' out :
  entry_direct hs s f a actuals hs' s' f' out ->
  forall ts rs inst mf,
  lookup_N (s_funcs s) a = Some (FC_func_native (Tf ts rs) inst mf) ->
  exists defaults,
    length actuals = length ts /\ default_vals (modfunc_locals mf) = Some defaults /\
    hs' = hs /\ s' = s /\ f' = f /\
    out = [AI_frame (length rs) (Build_frame (actuals ++ defaults) inst)
                    [AI_label (length rs) [] (to_e_list (modfunc_body mf))]].
Proof.
  intro D. destruct D; intros xt xr xi xm Look; rewrite H in Look; inversion Look; subst.
  exists defaults. repeat split; assumption.
Qed.

(** At a host-to-guest entry with the declared arity, no values can be left
    below the arguments consumed by WasmCert's native invocation rule. *)
Lemma entry_native_exact hs s f args a ts rs inst mf hs' s' f' es' :
  lookup_N (s_funcs s) a = Some (FC_func_native (Tf ts rs) inst mf) ->
  length args = length ts ->
  @reduce hf mem h hs s f (v_to_e_list args ++ [AI_invoke a]) hs' s' f' es' ->
  exists defaults,
    default_vals (modfunc_locals mf) = Some defaults /\
    hs' = hs /\ s' = s /\ f' = f /\
    es' = [AI_frame (length rs) (Build_frame (args ++ defaults) inst)
                     [AI_label (length rs) [] (to_e_list (modfunc_body mf))]].
Proof.
  intros Lookup Arity R.
  destruct (entry_invoke_step _ _ _ _ _ _ _ _ _ _ R) as [pre [vs [out [Args [Dest Direct]]]]].
  destruct (entry_direct_native _ _ _ _ _ _ _ _ _ Direct _ _ _ _ Lookup)
    as [defs [Len [Def [Hs [Store [Frame Out]]]]]].
  subst args. rewrite length_app in Arity.
  destruct pre; cbn in Arity; [|lia].
  subst. exists defs. repeat split; auto.
Qed.
End Semantics.
End AuthEntry.

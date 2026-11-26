From Coq Require List NArith Bool.
From Wasm Require memory host opsem properties.

Module AuthForward.
Import List NArith Bool.
Import memory host opsem properties.
Import AuthEntry.
Import ListNotations.
Local Open Scope list_scope.

Inductive operand :=
| from_local : N -> operand
| from_num : value_num -> operand.

Definition operand_code op :=
  match op with from_local i => BI_local_get i | from_num v => BI_const_num v end.

Definition wrapper_code ops callee := map operand_code ops ++ [BI_call callee].

(** A missing local cannot step. Its arbitrary denotation only makes the
    symbolic list total, and is never used by a successful local.get step. *)
Definition operand_value (f : frame) fallback op :=
  match op with
  | from_local i =>
      match lookup_N (f_locs f) i with Some v => v | None => fallback end
  | from_num v => VAL_num v
  end.

Lemma forwards_owner ops f owner outer_slot inner_slot :
  nth_error ops inner_slot = Some (from_local outer_slot) ->
  lookup_N (f_locs f) outer_slot = Some owner ->
  nth_error (map (operand_value f owner) ops) inner_slot = Some owner.
Proof. intros Sel Own. rewrite List.nth_error_map, Sel. cbn [option_map operand_value]. now rewrite Own. Qed.

Inductive flat_op := load_local : N -> flat_op | call_function : N -> flat_op.
Definition flat_instruction op := AI_basic
  (match op with load_local i => BI_local_get i | call_function i => BI_call i end).

Definition flat_result (f : frame) op : option administrative_instruction :=
  match op with
  | load_local i => option_map v_to_e (lookup_N (f_locs f) i)
  | call_function i => option_map AI_invoke (lookup_N (inst_funcs (f_inst f)) i)
  end.

Ltac forward_other :=
  try match goal with H : ?vs = v_to_e_list _ |- _ => is_var vs; subst vs end;
  intros [idx | idx] E; revert E; entry_simpl_first; discriminate.

Lemma simple_other xs ys : reduce_simple xs ys ->
  forall op, entry_first xs <> Some (flat_instruction op).
Proof.
  intro R; destruct R; try solve [forward_other].
  match goal with H : lfill _ _ = _ |- _ => rewrite <- H end.
  destruct lh; cbn [lfill]; forward_other.
Qed.

Section Steps.
Context {hf : host_function_class} {mem : Memory} {h : @host hf mem}.

Lemma flat_step_class hs s f xs hs' s' f' ys :
  @reduce hf mem h hs s f xs hs' s' f' ys ->
  forall op, entry_first xs = Some (flat_instruction op) ->
    exists pre tail out, xs = v_to_e_list pre ++ flat_instruction op :: tail /\
      ys = v_to_e_list pre ++ out :: tail /\ flat_result f op = Some out /\
      hs' = hs /\ s' = s /\ f' = f.
Proof.
  intro R; induction R; try solve [forward_other].
  - intros op E. exfalso; exact (simple_other _ _ H op E).
  - intros [ix|ix] E; inversion E; subst.
    exists [], [], (AI_invoke a). cbn [flat_result]. rewrite H. repeat split.
  - intros [ix|ix] E; inversion E; subst.
    exists [], [], (v_to_e v). cbn [flat_result]. rewrite H. repeat split.
  - subst les les'. destruct lh as [lvs les | k lvs n cont lh les].
    + cbn [lfill]. repeat rewrite cat_app.
      intros op E. destruct (entry_step_class _ _ _ _ _ _ _ _ R) as [[head Active] _].
      repeat rewrite entry_first_app in E. rewrite entry_first_values, Active in E.
      inversion E; subst head.
      destruct (IHR op Active) as [pre [tail [out [Src [Dst Facts]]]]].
      exists (lvs ++ pre), (tail ++ les), out.
      rewrite Src, Dst, entry_values_app. repeat rewrite <- app_assoc.
      repeat split; tauto.
    + cbn [lfill]. forward_other.
Qed.

Lemma flat_step hs s f pre op tail hs' s' f' ys :
  @reduce hf mem h hs s f (v_to_e_list pre ++ flat_instruction op :: tail) hs' s' f' ys ->
  exists out, flat_result f op = Some out /\ ys = v_to_e_list pre ++ out :: tail /\
    hs' = hs /\ s' = s /\ f' = f.
Proof.
  intro R. assert (E : entry_first (v_to_e_list pre ++ flat_instruction op :: tail) = Some (flat_instruction op)).
  { rewrite entry_first_app, entry_first_values. now destruct op. }
  destruct (flat_step_class _ _ _ _ _ _ _ _ R op E)
    as [vs [more [out [Src [Dst Facts]]]]].
  apply const_list_concat_inv in Src as [Stack [_ Tail]];
    try apply v_to_e_const; try (destruct op; discriminate).
  rewrite <- Stack, <- Tail in Dst. exists out. tauto.
Qed.
End Steps.

Definition remaining stack ops callee :=
  v_to_e_list stack ++ to_e_list (wrapper_code ops callee).

Inductive pending (f : frame) (fallback : value) (callee addr : N) (actuals : list value) :
    list administrative_instruction -> Prop :=
| pending_operands : forall stack ops,
    stack ++ map (operand_value f fallback) ops = actuals ->
    pending f fallback callee addr actuals (remaining stack ops callee)
| pending_invocation :
    pending f fallback callee addr actuals (v_to_e_list actuals ++ [AI_invoke addr]).

Lemma remaining_num stack n rest callee :
  remaining stack (from_num n :: rest) callee =
  remaining (stack ++ [VAL_num n]) rest callee.
Proof. unfold remaining, wrapper_code. rewrite entry_values_app, <- app_assoc. reflexivity. Qed.

Lemma pending_start f fallback callee addr ops :
  pending f fallback callee addr (map (operand_value f fallback) ops)
    (to_e_list (wrapper_code ops callee)).
Proof. apply (pending_operands _ _ _ _ _ [] ops). reflexivity. Qed.

Section Progress.
Context {hf : host_function_class} {mem : Memory} {h : @host hf mem}.

Lemma operands_step hs s f fallback callee addr actuals ops :
  lookup_N (inst_funcs (f_inst f)) callee = Some addr ->
  forall stack hs' s' f' ys,
    stack ++ map (operand_value f fallback) ops = actuals ->
    @reduce hf mem h hs s f (remaining stack ops callee) hs' s' f' ys ->
    hs' = hs /\ s' = s /\ f' = f /\ pending f fallback callee addr actuals ys.
Proof.
  intro Lookup. induction ops as [|[i|n] ops IH]; intros stack hs' s' f' ys Args R.
  - cbn in Args. rewrite app_nil_r in Args. subst actuals.
    destruct (flat_step hs s f stack (call_function callee) [] _ _ _ _ R)
      as [out [Effect [Dest Facts]]]. cbn [flat_result] in Effect.
    rewrite Lookup in Effect. injection Effect as <-. subst ys.
    intuition constructor.
  - destruct (flat_step hs s f stack (load_local i) (to_e_list (wrapper_code ops callee)) _ _ _ _ R)
      as [out [Effect [Dest Facts]]]. cbn [flat_result] in Effect.
    destruct (lookup_N (f_locs f) i) as [v|] eqn:Local; try discriminate.
    injection Effect as <-. subst ys.
    assert (Next : pending f fallback callee addr actuals
                    (remaining (stack ++ [v]) ops callee)).
    { constructor. rewrite <- app_assoc. cbn in Args. rewrite Local in Args. exact Args. }
    unfold remaining in Next. rewrite entry_values_app, <- app_assoc in Next. tauto.
  - rewrite remaining_num in R. eapply IH; [|exact R].
    rewrite <- app_assoc. exact Args.
Qed.

Lemma pending_step hs s f fallback callee addr actuals ts rs inst body es hs' s' f' next :
  lookup_N (inst_funcs (f_inst f)) callee = Some addr ->
  lookup_N (s_funcs s) addr = Some (FC_func_native (Tf ts rs) inst body) ->
  length actuals = length ts ->
  pending f fallback callee addr actuals es ->
  @reduce hf mem h hs s f es hs' s' f' next ->
  hs' = hs /\ s' = s /\ f' = f /\
  (pending f fallback callee addr actuals next \/
   exists defaults, default_vals (modfunc_locals body) = Some defaults /\
     next = [AI_frame (length rs) (Build_frame (actuals ++ defaults) inst)
               [AI_label (length rs) [] (to_e_list (modfunc_body body))]]).
Proof.
  intros Lookup Target Arity P R. destruct P as [stack ops Args |].
  - destruct (operands_step _ _ _ _ _ _ _ _ Lookup _ _ _ _ _ Args R) as [? [? [? ?]]]. auto.
  - destruct (entry_native_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Target Arity R)
      as [defs [D [? [? [? Next]]]]]. repeat split; try assumption. right; eauto.
Qed.
End Progress.

Definition forward_head e :=
  match e with AI_basic (BI_local_get _) | AI_basic (BI_call _) | AI_invoke _ => True | _ => False end.

Lemma pending_head f fallback callee addr actuals es :
  pending f fallback callee addr actuals es ->
  exists e, entry_first es = Some e /\ forward_head e.
Proof.
  intros [stack ops A|].
  - clear A. revert stack. induction ops as [|[i|n] ops IH]; intro stack.
    + exists (AI_basic (BI_call callee)). unfold remaining. rewrite entry_first_app, entry_first_values. split; [reflexivity|exact I].
    + exists (AI_basic (BI_local_get i)). unfold remaining. rewrite entry_first_app, entry_first_values. split; [reflexivity|exact I].
    + rewrite remaining_num. apply IH.
  - exists (AI_invoke addr). rewrite entry_first_app, entry_first_values. split; [reflexivity|exact I].
Qed.

Lemma pending_no_values f fallback callee addr actuals es :
  pending f fallback callee addr actuals es -> const_list es = true -> False.
Proof. intros P C. destruct (pending_head _ _ _ _ _ _ P) as [e [E _]].
  rewrite (entry_first_const es C) in E; discriminate. Qed.

Lemma pending_no_exit f fallback callee addr actuals es k (lh : lholed k) vs e :
  pending f fallback callee addr actuals es -> const_list vs = true ->
  is_const e = false -> ~ forward_head e -> lfill lh (vs ++ [e]) = es -> False.
Proof.
  intros P C Nonconst NoHead <-. destruct (pending_head _ _ _ _ _ _ P) as [head [E H]].
  destruct lh; cbn [lfill] in E; repeat rewrite cat_app in E;
    repeat rewrite entry_first_app in E; rewrite entry_first_values in E.
  - rewrite (entry_first_const vs C) in E. cbn [entry_first] in E. rewrite Nonconst in E.
    inversion E; subst; contradiction.
  - inversion E; subst. exact H.
Qed.
End AuthForward.

From Coq Require List Relations.Relation_Operators Relations.Operators_Properties.
From mathcomp Require ssrbool.
From Wasm Require memory datatypes host opsem properties.

Module AuthTraps.
Import List Relation_Operators Operators_Properties.
Import ssrbool.
Import memory datatypes host opsem properties.
Import ListNotations.
Local Open Scope list_scope.

(** Follow the active instruction through labels and frames. An unreachable
    instruction has the same terminal consequence as a trap. *)
Inductive redex_status := only_values | active_trap | active_other.

Definition nested_status x :=
  match x with only_values => active_other | _ => x end.

Fixpoint scan_status {A} (tag : A -> redex_status) (xs : list A) :=
  match xs with
  | [] => only_values
  | x :: tail =>
    match tag x with only_values => scan_status tag tail | k => k end
  end.

Fixpoint instruction_status (e : administrative_instruction) : redex_status :=
  match e with
  | AI_trap | AI_basic BI_unreachable => active_trap
  | AI_label _ _ inner | AI_frame _ _ inner =>
      nested_status (scan_status instruction_status inner)
  | _ => if is_const e then only_values else active_other
  end.

Definition code_status := scan_status instruction_status.

Lemma code_status_value v : instruction_status (v_to_e v) = only_values.
Proof. destruct v as [v|v|[r|a|e]]; reflexivity. Qed.

Lemma status_const_value e : is_const e = true -> instruction_status e = only_values.
Proof.
  intro H. apply is_const_exists in H as [v Hv]. subst. apply code_status_value.
Qed.

Lemma status_const_prefix vs tail : const_list vs = true ->
  code_status (List.app vs tail) = code_status tail.
Proof.
  induction vs as [|v vs IH]; intro H; [reflexivity|].
  apply Bool.andb_true_iff in H as [A B].
  change (match instruction_status v with
    | only_values => code_status (vs ++ tail) | k => k end = code_status tail).
  rewrite (status_const_value _ A). apply IH. exact B.
Qed.

Lemma status_value_prefix vs tail :
  code_status (List.app (v_to_e_list vs) tail) = code_status tail.
Proof. apply status_const_prefix, v_to_e_const. Qed.

Lemma status_const vs : const_list vs = true -> code_status vs = only_values.
Proof.
  intro H. rewrite <- (app_nil_r vs). apply (status_const_prefix vs [] H).
Qed.

Lemma status_append es tail : code_status es <> only_values ->
  code_status (List.app es tail) = code_status es.
Proof.
  induction es as [|e es IH]; intro H; [contradiction H; reflexivity|].
  unfold code_status in *; cbn [app scan_status] in *.
  destruct (instruction_status e); auto.
Qed.

Lemma status_fill k (lh : lholed k) es : code_status es <> only_values ->
  code_status (lfill lh es) = code_status es.
Proof.
  intro H. induction lh as [vs tail | k vs n cont lh IHlh l1]; cbn [lfill]; repeat rewrite cat_app; rewrite status_value_prefix.
  - apply status_append. exact H.
  - change (match nested_status (code_status (lfill lh es)) with
            | only_values => code_status l1 | active_trap => active_trap | active_other => active_other end = code_status es).
    rewrite IHlh. destruct (code_status es); cbn; congruence.
Qed.

Definition status_step es es' :=
  code_status es <> only_values /\
  (code_status es = active_trap -> code_status es' = active_trap).

Lemma status_label n cont inner tail :
  code_status (AI_label n cont inner :: tail) = nested_status (code_status inner).
Proof.
  change (match nested_status (code_status inner) with
          | only_values => code_status tail | k => k end = nested_status (code_status inner)).
  destruct (code_status inner); reflexivity.
Qed.

Lemma status_frame n f inner tail :
  code_status (AI_frame n f inner :: tail) = nested_status (code_status inner).
Proof.
  change (match nested_status (code_status inner) with
          | only_values => code_status tail | k => k end = nested_status (code_status inner)).
  destruct (code_status inner); reflexivity.
Qed.

Lemma status_frame_step n f f' es es' :
  status_step es es' -> status_step [AI_frame n f es] [AI_frame n f' es'].
Proof.
  intros [A B]. unfold status_step. repeat rewrite status_frame.
  destruct (code_status es); simpl in *; split; try discriminate; try congruence.
  intros _. rewrite (B eq_refl). reflexivity.
Qed.

Ltac status_normalize :=
  repeat first [rewrite cat_app | rewrite status_label | rewrite status_frame
    | rewrite status_value_prefix | rewrite status_const_prefix by assumption
    | rewrite status_const by assumption
    | rewrite status_fill by (try rewrite status_const_prefix by assumption; discriminate)
    | progress cbn [code_status scan_status] | rewrite code_status_value].

Ltac base_status :=
  unfold status_step; split; status_normalize; try discriminate; try (intros _; reflexivity).
Lemma status_underfill k (lh : lholed k) es es' :
  status_step es es' -> status_step (lfill lh es) (lfill lh es').
Proof.
  intros [H T]. unfold status_step.
  rewrite (status_fill k lh es H). split; [exact H|].
  intro A. specialize (T A). rewrite status_fill; congruence.
Qed.

Lemma status_simple es es' : reduce_simple es es' -> status_step es es'.
Proof.
  intro H; destruct H;
  try solve [base_status].
  all: subst.
  all: try solve [base_status].
Qed.

Section Generic.
Context {hf : host_function_class} {mem : Memory} (h : @host hf mem).

Lemma status_reduce hs s f es hs' s' f' es' :
  @reduce hf mem h hs s f es hs' s' f' es' -> status_step es es'.
Proof.
  intro H; induction H;
  try solve [base_status].
  all: subst.
  all: try solve [apply status_simple; assumption | apply status_underfill; assumption | apply status_frame_step; assumption].
  all: try solve [base_status].
Qed.

Lemma trapped_execution hs s f es hs' s' f' es' :
  @reduce_trans hf mem h (hs,s,f,es) (hs',s',f',es') ->
  code_status es = active_trap -> code_status es' = active_trap.
Proof.
  remember (hs,s,f,es) as start. remember (hs',s',f',es') as finish.
  intro run. revert hs s f es hs' s' f' es' Heqstart Heqfinish.
  induction run as [x y step|x|x y z run1 IH1 run2 IH2].
  - intros * -> ->. apply (proj2 (status_reduce _ _ _ _ _ _ _ _ step)).
  - intros * -> Eq; inversion Eq; auto.
  - intros * -> ->. destruct y as [[[hsm sm] fm] em].
    intro H. eapply IH2; try reflexivity. eapply IH1; eauto.
Qed.

Lemma trapped_no_results hs s f es hs' s' f' results :
  code_status es = active_trap ->
  ~ @reduce_trans hf mem h (hs,s,f,es) (hs',s',f',v_to_e_list results).
Proof.
  intros H run. apply trapped_execution in run; [|exact H].
  rewrite status_const in run; [discriminate | apply v_to_e_const].
Qed.
End Generic.
End AuthTraps.

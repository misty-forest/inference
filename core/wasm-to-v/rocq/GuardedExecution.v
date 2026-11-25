From Coq Require List NArith Bool Lia.
From mathcomp Require ssreflect eqtype seq ssrbool.
From Wasm Require properties.

Module GuardedExecution.
Import List NArith Bool Lia.
Import ssreflect eqtype seq ssrbool.
Import properties.
Import ListNotations.

Section Scanner.
Context {hf : host_function_class} {mem : Memory}.
Variable arg callee addr : N.
Variable owner : value.
Definition monotone (p : bool -> Prop) := p false -> p true.
Definition lift_unknown p (h : monotone p) b : p false -> p b :=
  match b return p false -> p b with true => h | false => fun x => x end.
Definition owned (v : value) : bool := eq_op v owner.

(** [top = true] identifies the owner at the top of the operand stack.
    [branch = true] permits a branch to depth zero. A protected block accepting
    such a branch must have a guarded continuation. The outer function label
    may instead establish that its body cannot leave through that label. *)
Fixpoint scan_one (e : administrative_instruction) (branch : bool)
    (next : bool -> Prop) (top : bool) {struct e} : Prop :=
  match e_to_v_opt e with
  | Some v => next (owned v)
  | None =>
    match e with
    | AI_trap | AI_basic BI_unreachable => True
    | AI_basic (BI_local_get i) => next (N.eqb i arg)
    | AI_basic (BI_local_set i) | AI_basic (BI_local_tee i) => i <> arg /\ next false
    | AI_basic (BI_global_get _) | AI_basic (BI_global_set _) |
      AI_basic (BI_binop _ _) | AI_basic (BI_relop _ _) | AI_basic (BI_load _ _ _) => next false
    | AI_basic (BI_call i) => (top = true /\ i = callee) \/ next false
    | AI_invoke a => (top = true /\ a = addr) \/ next false
    | AI_basic (BI_br i) => branch = true /\ i = 0%N
    | AI_basic (BI_br_if i) => branch = true /\ i = 0%N /\ next false
    | AI_basic (BI_block _ body) => guarded_prefix arg callee true body /\ next false
    | AI_label _ cont body => cont = [] /\
        (List.fold_right (fun i k => scan_one i false k) (fun _ => False) body false \/
         (List.fold_right (fun i k => scan_one i true k) (fun _ => False) body false /\ next false))
    | AI_frame _ _ _ => next false
    | _ => False
    end
  end.
Definition scan (es : list administrative_instruction) b k :=
  List.fold_right (fun i k => scan_one i b k) k es.
Lemma scan_app xs ys b k t : scan (List.app xs ys) b k t = scan xs b (scan ys b k) t.
Proof. unfold scan. now rewrite List.fold_right_app. Qed.
Lemma scan_value v xs b k t : scan (v_to_e v :: xs) b k t = scan xs b k (owned v).
Proof. change (scan_one (v_to_e v) b (scan xs b k) t = scan xs b k (owned v)). destruct v as [n|w|[r|a|a]]; reflexivity. Qed.
Lemma scan_one_val v b k t : scan_one (v_to_e v) b k t = k (owned v).
Proof. destruct v as [n|w|[r|a|a]]; reflexivity. Qed.
Lemma scan_one_ref r b k t : scan_one (vref_to_e r) b k t = k (owned (VAL_ref r)).
Proof. destruct r; reflexivity. Qed.
Lemma scan_values vs b k t : scan (v_to_e_list vs) b k t = k (List.fold_left (fun _ v => owned v) vs t).
Proof. revert t. induction vs as [|v vs IH]; intro t; [reflexivity|]. change (scan (v_to_e v :: v_to_e_list vs) b k t = k (List.fold_left (fun _ v => owned v) vs (owned v))). rewrite scan_value. apply IH. Qed.
Lemma scan_mono xs b k : monotone k -> monotone (scan xs b k).
Proof. unfold monotone. intro H. destruct xs as [|e xs]; [exact H|].
  change (scan_one e b (scan xs b k) false -> scan_one e b (scan xs b k) true).
  destruct e as [op| | | | | | | ]; try destruct op; simpl; intuition discriminate.
Qed.
Lemma certified b body : guarded_prefix arg callee b body ->
  forall k t, monotone k -> scan (to_e_list body) b k t.
Proof.
 intro G. induction G; intros k t M.
 - cbn [to_e_list scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map map]. rewrite N.eqb_refl. by left.
 - destruct op; simpl in H; try discriminate; cbn [to_e_list scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map map];
   try solve [apply IHG; exact M | right; apply IHG; exact M | split; [apply Bool.negb_true_iff in H; apply N.eqb_neq; exact H|apply IHG; exact M]].
 - repeat split; auto.
 - cbn [to_e_list scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map map]. split; auto.
Qed.

Lemma scan_no_values vs b t : ~ scan (v_to_e_list vs) b (fun _ => False) t.
Proof. rewrite scan_values. auto. Qed.
Lemma scan_no_exit d (lh : lholed d) vs e b k t :
  const_list vs -> (e = AI_basic BI_return \/ exists a, e = AI_return_invoke a) ->
  ~ scan (lfill lh (List.app vs [e])) b k t.
Proof.
 intros C E. apply const_es_exists in C as [vv ->]. revert b k t.
 induction lh as [pre post|d pre n c lh IH post]; intros b k t;
 cbn [lfill]; repeat rewrite cat_app; repeat first [rewrite scan_app|rewrite scan_values].
 - destruct E as [->|[a ->]]; cbn [scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map]; tauto.
 - cbn [scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map]; intros [_ [H|[H _]]]; eapply IH; exact H.
Qed.
Lemma scan_br_origin d (lh : lholed d) vs i b k t :
  const_list vs -> scan (lfill lh (List.app vs [AI_basic (BI_br i)])) b k t ->
  i = 0%N /\ (d = O -> b = true).
Proof.
 intro C. apply const_es_exists in C as [vv ->]. revert b k t.
 induction lh as [pre post|d pre n c lh IH post]; intros b k t;
 cbn [lfill]; repeat rewrite cat_app; repeat first [rewrite scan_app|rewrite scan_values].
 - cbn [scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map]. tauto.
 - cbn [scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map].
   intros [_ [G|[G _]]]; destruct (IH _ _ _ G) as [I D]; split; auto; discriminate.
Qed.
Lemma scan_br_exits d (lh:lholed d) vs : const_list vs ->
  ~ scan (lfill lh (List.app vs [AI_basic (BI_br (N.of_nat d))])) false (fun _ => False) false.
Proof. intros V G. apply (scan_br_origin _ _ _ _ _ _ _ V) in G as [I D].
 assert (d = 0)%nat by lia. specialize (D H). discriminate.
Qed.
Lemma entry_label n body : guarded_prefix arg callee false body ->
  scan [AI_label n [] (to_e_list body)] false (fun _ => False) false.
Proof. intro C. split; [reflexivity|left]. apply certified; auto. unfold monotone; auto. Qed.
Lemma under_context d (lh : lholed d) xs ys (ok : Prop) :
  (forall b k t, monotone k -> scan xs b k t -> ok /\ scan ys b k t) ->
  forall b k t, monotone k -> scan (lfill lh xs) b k t -> ok /\ scan (lfill lh ys) b k t.
Proof.
 intro A. induction lh as [pre post|d pre n c lh IH post]; intros b k t M;
 cbn [lfill]; repeat rewrite cat_app; repeat first [rewrite scan_app|rewrite scan_values].
 - apply A. now apply scan_mono.
 - cbn [scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map]. intros [C [G|[G K]]].
   + destruct (IH false (fun _ => False) false (fun x => x) G) as [O G']. auto.
   + destruct (IH true (fun _ => False) false (fun x => x) G) as [O G']. auto.
Qed.
Definition frame_ok (f : frame) := lookup_N (f_locs f) arg = Some owner /\
                                    lookup_N (inst_funcs (f_inst f)) callee = Some addr.
Lemma owned_refl : owned owner = true. Proof. unfold owned. apply eq_refl. Qed.
Lemma owned_true v : owned v = true -> v = owner. Proof. exact /eqP. Qed.
Lemma set_other (xs:list value) (x d:value) (i n:nat) :
  i <> n -> (i < List.length xs)%nat -> List.nth_error (set_nth d xs i x) n = List.nth_error xs n.
Proof. revert i n. induction xs as [|a xs IH]; intros [|i] [|n] D L; simpl in *; try lia; try reflexivity.
 apply IH; lia.
Qed.
Ltac normalize_constants := repeat match goal with
  | C : is_true (const_list ?vs) |- _ => is_var vs; let vv := fresh "stack" in let E := fresh in destruct (const_es_exists C) as [vv E]; subst vs
  end.
Ltac normalize_scan :=
  repeat rewrite cat_app in *;
  repeat first [rewrite scan_app in *|rewrite scan_values in *|rewrite scan_value in *];
  cbn [scan List.fold_right scan_one e_to_v_opt e_to_vref_opt option_map v_to_e vref_to_e] in *;
  repeat first [rewrite scan_app|rewrite scan_values|rewrite scan_one_val|rewrite scan_one_ref].
Lemma simple_sound xs ys : reduce_simple xs ys ->
  forall b k t, monotone k -> scan xs b k t -> scan ys b k t.
Proof.
 intro R. destruct R; intros b k t0 M; normalize_constants; normalize_scan;
 try solve [intuition | intros; eapply lift_unknown; eauto | tauto].
 all: try solve [intros [X [Y K]]; eapply lift_unknown; eauto].
 all: try solve [intros [_ [G|[G _]]]; exfalso; eapply scan_no_values; exact G].
 all: try solve [intros [CE [G|[_ K0]]]; subst es;
   [match goal with E : lfill _ _ = _ |- _ => rewrite <- E in G end; exfalso; eapply scan_br_exits; [apply v_to_e_const|exact G]
    |eapply lift_unknown; eauto]].
Qed.
Variable h : @host hf mem.
Variable auth : host_function.
Hypothesis denies : forall hs s ty hs' s' vals,
 ~ @host_application hf mem h hs s ty auth [owner] hs' (Some (s', result_values vals)).
Definition bound (s : store_record) := lookup_N (s_funcs s) addr =
  Some (FC_func_host (Tf [T_num T_i64] [T_num T_i64]) auth).
Lemma step_sound hs s f xs hs' s' f' ys : @reduce hf mem h hs s f xs hs' s' f' ys ->
  bound s -> frame_ok f -> forall b k t, monotone k -> scan xs b k t -> frame_ok f' /\ scan ys b k t.
Proof.
 intro R. induction R; intros Bind F branchflag K top M;
 try solve [intro G; split; [exact F|eapply simple_sound; eauto]].
 all: try subst ves; try subst cl; normalize_constants; normalize_scan;
 try solve [tauto | intro G; split; [exact F|eapply lift_unknown; eauto]].
 - intros [G T]. split; [exact F|]. split; [reflexivity|right]. split; [|exact T].
   change (scan (List.app (v_to_e_list stack) (to_e_list es)) true (fun _ => False) false).
   rewrite scan_app scan_values. apply certified; [exact G|unfold monotone; auto].
 - intro G. contradiction.
 - (* Resolve the direct call in the same module instance. *)
   intros [[T E]|G]; split; try exact F.
   + left. split; [exact T|]. destruct F. subst. congruence.
   + right. exact G.
 - (* A native helper receives its own locals. *)
   intros [[T E]|G]; [subst; unfold bound in Bind; congruence|auto].
 - (* A value-returning host step at the bound address consumed exactly one operand. *)
   intro G. split; [exact F|]. destruct r as [vals|]; cbn [result_to_stack]; [|exact I].
   rewrite scan_values. destruct G as [[T E]|G]; [|eapply lift_unknown; eauto].
   subst. unfold bound in Bind.
   match goal with H : lookup_N _ _ = Some (FC_func_host _ _) |- _ =>
     rewrite Bind in H; inversion H; subst end.
   destruct vcs as [|v [|w tail]]; simpl in *; try congruence.
   apply owned_true in T. subst v. exfalso. eapply denies; eauto.
 - intro G. split; [exact F|right; exact G].
 - intro G. split; [exact F|]. destruct (N.eqb_spec j arg) as [->|D].
   + destruct F. assert (v = owner) by congruence. subst v. now rewrite owned_refl.
   + eapply lift_unknown; eauto.
 - intros [D G]. split; [|exact (lift_unknown K M top G)].
   unfold frame_ok in *. destruct F as [Loc Cal]. split.
   + unfold lookup_N in *. rewrite H1. apply eq_trans with (y:=List.nth_error (f_locs f) (N.to_nat arg)); [|exact Loc].
     apply set_other; [intro E; apply D; apply N2Nat.inj; exact E|].
     move/ssrnat.ltP in H0. exact H0.
   + rewrite H. exact Cal.
 - subst les les'. eapply under_context. intros b' k' t' mono G. eapply IHR; eauto. exact M.
Qed.
End Scanner.
End GuardedExecution.

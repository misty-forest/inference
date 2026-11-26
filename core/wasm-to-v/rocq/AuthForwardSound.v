From Coq Require List String NArith.
From mathcomp Require eqtype ssrbool.
From Wasm Require memory host operations opsem properties instantiation_spec.

Module AuthForwardSound.
Import List String NArith eqtype ssrbool.
Import memory host operations opsem properties instantiation_spec.
Import AuthForward AuthCallContext GuardedExecution.
Import ListNotations.
Local Open Scope list_scope.

(** Wasm appends default-initialized locals after the call arguments. *)
Lemma argument_local (args defaults : list value) slot owner :
  nth_error args slot = Some owner ->
  lookup_N (args ++ defaults) (N.of_nat slot) = Some owner.
Proof.
  intro Own. unfold lookup_N. rewrite Nat2N.id, nth_error_app1; [exact Own|].
  apply nth_error_Some. congruence.
Qed.

(** A finite derivation follows the same owner through zero or more native
    calls. Each forwarding constructor links its target to the next body. *)
Inductive body_guard (m : module) : nat -> N -> module_func -> Prop :=
| direct : forall slot auth body,
    guarded_prefix (N.of_nat slot) auth false (modfunc_body body) ->
    body_guard m slot auth body
| forwarded : forall slot auth body ops target position params results helper,
    modfunc_body body = wrapper_code ops target ->
    nth_error ops position = Some (from_local (N.of_nat slot)) ->
    AuthResolve.resolve_native m target = Some (Tf params results, helper) ->
    List.length ops = List.length params ->
    body_guard m position auth helper ->
    body_guard m slot auth body.

Section Execution.
Context {hf : host_function_class} {mem : Memory} (base : @host hf mem).
Variable auth : host_function.
Variable owner : value.
Let h := SorobanAuthorization.denying base auth owner.

(** A body invariant starts in any frame of this module whose selected local
    holds the owner. This quantification lets each call use the actual
    arguments and default locals supplied by Wasm's native invocation rule. *)
Lemma body_invariant m before deployed live imports fr init
    (I : @instantiate hf mem base before m imports (deployed,fr,init))
    (Ext : store_extension deployed live = true)
    slot auth_index body (Guard : body_guard m slot auth_index body) :
  forall auth_addr,
    lookup_N (inst_funcs (f_inst fr)) auth_index = Some auth_addr ->
    bound auth_addr auth live ->
    exists P, nonreturning h P /\
      forall hs f, f_inst f = f_inst fr ->
        lookup_N (f_locs f) (N.of_nat slot) = Some owner ->
        P hs live f (to_e_list (modfunc_body body)).
Proof.
  induction Guard as [slot auth_index body Direct|
    slot auth_index body ops target pos params results helper Code Selected Native Arity Chain IH];
    intros auth_addr AuthIndex Host.
  - exists (fun (_ : @host_state hf mem h) s f es =>
      bound auth_addr auth s /\ frame_ok (N.of_nat slot) auth_index auth_addr owner f /\
      scan (N.of_nat slot) auth_index auth_addr owner es false (fun _ => False) false).
    split.
    + constructor.
      * intros h0 s0 f0 es h1 s1 f1 next [B [F G]] R. split.
        -- exact (AuthStore.auth_reduce_lookup _ _ _ _ _ _ _ _ R _ _ B).
        -- eapply step_sound with (h := h); try exact R; try exact B; try exact F; try exact G.
           ++ exact (SorobanAuthorization.denied_success base auth owner).
           ++ unfold monotone. auto.
      * intros h0 s0 f0 es [_ [_ G]] V. destruct (const_es_exists V) as [vs ->].
        eapply scan_no_values. exact G.
      * intros h0 s0 f0 es k lh vs [_ [_ G]] V <-. eapply scan_br_exits; eauto.
      * intros h0 s0 f0 es k lh vs [_ [_ G]] V <-. eapply scan_no_exit; [exact V|left; reflexivity|exact G].
      * intros h0 s0 f0 es k lh vs a [_ [_ G]] V <-. eapply scan_no_exit; [exact V|right; eauto|exact G].
    + intros hs f Inst Own. split; [exact Host|]. split.
      * split; [exact Own|now rewrite Inst].
      * apply certified; [exact Direct|unfold monotone; auto].
  - destruct (AuthResolve.native_resolved base _ _ _ _ _ _ _ _ _ _ Native I Ext)
      as [addr [Index Target]].
    destruct (IH auth_addr AuthIndex Host) as [Q [Safe Start]].
    pose proof (protected_labeled_nonreturning h Q Safe) as InsideSafe.
    exists (fun hs s f es =>
      (s = live /\ f_inst f = f_inst fr /\
       lookup_N (f_locs f) (N.of_nat slot) = Some owner /\
       pending f owner target addr (map (operand_value f owner) ops) es) \/
      protected h (labeled h Q) hs s f es).
    split.
    + constructor.
      * intros h0 s0 f0 es h1 s1 f1 next [[-> [Inst [Own Before]]]|Inside] R.
        -- assert (Lookup : lookup_N (inst_funcs (f_inst f0)) target = Some addr)
             by now rewrite Inst.
           assert (Len : List.length (map (operand_value f0 owner) ops) = List.length params)
             by now rewrite List.length_map.
           destruct (@pending_step hf mem h h0 live f0 owner target addr _ params results (f_inst fr)
             helper es h1 s1 f1 next Lookup Target Len Before R)
             as [_ [-> [-> [Next|[ds [_ ->]]]]]].
           ++ left; auto.
           ++ right. right. do 3 eexists. split; [reflexivity|].
              right. do 3 eexists. split; [reflexivity|].
              apply Start; [reflexivity|]. apply argument_local.
              eapply forwards_owner; eauto.
        -- right. eapply nr_step; [exact InsideSafe|exact Inside|exact R].
      * intros h0 s0 f0 es [[_ [_ [_ Before]]]|Inside] V.
        -- eapply pending_no_values; eauto.
        -- eapply nr_values with (h := h); eauto.
      * intros h0 s0 f0 es k lh vs [[_ [_ [_ Before]]]|Inside] V E.
        -- eapply pending_no_exit; [exact Before|exact V| | |exact E]; cbn; tauto.
        -- eapply nr_branch with (h := h); eauto.
      * intros h0 s0 f0 es k lh vs [[_ [_ [_ Before]]]|Inside] V E.
        -- eapply pending_no_exit; [exact Before|exact V| | |exact E]; cbn; tauto.
        -- eapply nr_return with (h := h); eauto.
      * intros h0 s0 f0 es k lh vs a [[_ [_ [_ Before]]]|Inside] V E.
        -- eapply pending_no_exit; [exact Before|exact V| | |exact E]; cbn; tauto.
        -- eapply nr_tail with (h := h); eauto.
    + intros hs f Inst Own. left. repeat split; try assumption. rewrite Code. apply pending_start.
Qed.
End Execution.

Theorem certificate_body_sound (m : module) (entry : string) (slot : nat)
    (auth_index absolute : N) (native_index : nat) (ts rs : list value_type)
    (body : module_func) :
    AuthResolve.resolve_static m entry auth_index =
      Some (absolute,native_index,Tf ts rs,body,Tf [T_num T_i64] [T_num T_i64]) ->
    body_guard m slot auth_index body ->
    requires_auth m entry slot.
Proof.
  intros Static Guard hf mem base before deployed live imports fr init auth address
    args owner hs hs' after caller caller' vals I Ext Bind Export Args Own Run.
  destruct (AuthResolve.auth_resolved base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Static I Ext Bind Export) as [auth_addr [Entry [AuthIndex Host]]].
  destruct Args as [cl [ts' [rs' [Lookup [Ty Len]]]]]. rewrite Entry in Lookup.
  injection Lookup as <-. change (Tf ts rs = Tf ts' rs') in Ty. inversion Ty; subst ts' rs'.
  set (h := SorobanAuthorization.denying base auth owner).
  destruct (AuthInvocation.native_invocation_reaches_frame h
      _ _ _ _ _ _ _ _ _ _ _ _ _ Entry Len Run) as [defs [_ Tail]].
  destruct (body_invariant base auth owner _ _ _ _ _ _ _ I Ext
      _ _ _ Guard auth_addr AuthIndex Host) as [P [Safe Start]].
  eapply (label_frame_no_results h P Safe); [|exact Tail].
  apply Start; [reflexivity|]. apply argument_local. exact Own.
Qed.

Theorem forward_auth_sound (m : module) (entry : string) (slot : nat)
    (auth_index absolute : N) (native_index : nat) (ts rs : list value_type)
    (wrapper : module_func) (operands : list operand) (helper_index : N)
    (helper_slot : nat) (helper_params helper_results : list value_type)
    (helper : module_func) :
    AuthResolve.resolve_static m entry auth_index =
      Some (absolute,native_index,Tf ts rs,wrapper,Tf [T_num T_i64] [T_num T_i64]) ->
    modfunc_body wrapper = wrapper_code operands helper_index ->
    nth_error operands helper_slot = Some (from_local (N.of_nat slot)) ->
    List.length operands = List.length helper_params ->
    AuthResolve.resolve_native m helper_index = Some (Tf helper_params helper_results,helper) ->
    guarded_prefix (N.of_nat helper_slot) auth_index false (modfunc_body helper) ->
    requires_auth m entry slot.
Proof.
  intros Static Code Selected Arity Native Guard.
  eapply certificate_body_sound; [exact Static|].
  eapply forwarded; [exact Code|exact Selected|exact Native|exact Arity|].
  apply direct. exact Guard.
Qed.
End AuthForwardSound.

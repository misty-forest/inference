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

(** Before the call the wrapper only reads locals and pushes constants. After
    the call the nested helper frame maintains the guarded execution invariant. *)
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
  intros Static Code Selected Arity Native Guard hf mem base before deployed live imports
    fr init auth address args owner hs hs' after caller caller' vals I Ext Bind Export Args Own Run.
  destruct (AuthResolve.auth_resolved base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Static I Ext Bind Export) as [auth_addr [Wrapper [AuthIndex Host]]].
  destruct (AuthResolve.native_resolved base _ _ _ _ _ _ _ _ _ _ Native I Ext)
    as [helper_addr [HelperIndex Target]].
  destruct Args as [cl [ts' [rs' [Lookup [Ty Len]]]]]. rewrite Wrapper in Lookup.
  injection Lookup as <-. change (Tf ts rs = Tf ts' rs') in Ty. inversion Ty; subst ts' rs'.
  set (h := SorobanAuthorization.denying base auth owner).
  destruct (AuthInvocation.native_invocation_reaches_frame h
      _ _ _ _ _ _ _ _ _ _ _ _ _ Wrapper Len Run) as [defs [_ Tail]].
  set (wrapper_frame := Build_frame (args ++ defs) (f_inst fr)).
  set (actuals := map (operand_value wrapper_frame owner) operands).
  assert (ActualOwner : nth_error actuals helper_slot = Some owner).
  { eapply forwards_owner; [exact Selected|]. apply argument_local. exact Own. }
  assert (ActualArity : List.length actuals = List.length helper_params).
  { unfold actuals. now rewrite List.length_map. }
  set (Q := fun (_ : @host_state hf mem h) (s : store_record) (f : frame)
                (es : list administrative_instruction) =>
    bound auth_addr auth s /\ frame_ok (N.of_nat helper_slot) auth_index auth_addr owner f /\
    scan (N.of_nat helper_slot) auth_index auth_addr owner es false (fun _ => False) false).
  assert (HelperSafe : nonreturning h (protected h Q)).
  { apply protected_nonreturning.
    - intros h0 s0 f0 es h1 s1 f1 next [B [F G]] R. split.
      + eapply AuthStore.auth_reduce_lookup; eauto.
      + eapply step_sound; try exact R; try exact B; try exact F; try exact G.
        * exact (SorobanAuthorization.denied_success base auth owner).
        * unfold monotone. auto.
    - intros h0 s0 f0 es [_ [_ G]] V.
      destruct (const_es_exists V) as [vs ->]. eapply scan_no_values. exact G.
    - intros h0 s0 f0 es k lh vs [_ [_ G]] V <-.
      eapply scan_no_exit; [exact V|left; reflexivity|exact G].
    - intros h0 s0 f0 es k lh vs a [_ [_ G]] V <-.
      eapply scan_no_exit; [exact V|right; eauto|exact G]. }
  set (P := fun (h0 : @host_state hf mem h) (s : store_record) (f : frame) es =>
    (s = live /\ f = wrapper_frame /\ pending wrapper_frame owner helper_index helper_addr actuals es) \/
    protected h Q h0 s f es).
  eapply (label_frame_no_results h P); [| |exact Tail].
  - constructor.
    + intros h0 s0 f0 es h1 s1 f1 next [[-> [-> Before]]|Inside] R.
      * destruct (pending_step h0 live wrapper_frame owner helper_index helper_addr actuals
            helper_params helper_results (f_inst fr) helper es h1 s1 f1 next
            HelperIndex Target ActualArity Before R) as [_ [-> [-> [Next|[ds [_ ->]]]]]].
        -- left. auto.
        -- right. right. do 3 eexists. split; [reflexivity|].
           split; [exact Host|]. split; [split|].
           ++ apply argument_local. exact ActualOwner.
           ++ exact AuthIndex.
           ++ apply entry_label. exact Guard.
      * right. eapply nr_step; [exact HelperSafe|exact Inside|exact R].
    + intros h0 s0 f0 es [[_ [_ Before]]|Inside] V.
      * eapply pending_no_values; eauto.
      * eapply nr_values; eauto.
    + intros h0 s0 f0 es k lh vs [[_ [_ Before]]|Inside] V E.
      * eapply pending_no_exit; [exact Before|exact V| | |exact E]; cbn; tauto.
      * eapply nr_branch; eauto.
    + intros h0 s0 f0 es k lh vs [[_ [_ Before]]|Inside] V E.
      * eapply pending_no_exit; [exact Before|exact V| | |exact E]; cbn; tauto.
      * eapply nr_return; eauto.
    + intros h0 s0 f0 es k lh vs a [[_ [_ Before]]|Inside] V E.
      * eapply pending_no_exit; [exact Before|exact V| | |exact E]; cbn; tauto.
      * eapply nr_tail; eauto.
  - left. split; [reflexivity|]. split; [reflexivity|]. rewrite Code. apply pending_start.
Qed.
End AuthForwardSound.

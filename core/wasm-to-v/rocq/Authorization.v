
(** Operational interpretation of an export-level authorization requirement.
    WasmCert host applications are atomic. This monitor observes applications
    made in this guest invocation; the internals of a cross-contract host
    call are not guest steps of this invocation. *)
From Wasm Require Import memory host operations opsem instantiation_spec.
Module SorobanAuthorization.
Section Semantics.
Context {hf : host_function_class} {mem : Memory} (base : @host hf mem).

(** Remove precisely a successful require_auth(owner) transition. Keep the
    original host state, stores, traps, divergence and all unrelated calls. *)
Definition denying (auth : host_function) (owner : value) : @host hf mem.
Proof.
  refine {| host_state := @host_state hf mem base;
            host_application := fun hs s ty h args hs' out =>
              @host_application hf mem base hs s ty h args hs' out /\
              ~ (h = auth /\ args = [owner] /\
                 exists after values, out = Some (after, result_values values)) |}.
  - intros until r. intros [step _]. eapply host_application_extension; exact step.
  - intros until r. intros [step _] typed. eapply host_application_typing; eauto.
  - intros until r. intros typed [step _]. eapply host_application_respect; eauto.
Defined.

Lemma original_application auth owner hs s ty h args hs' out :
  @host_application hf mem (denying auth owner) hs s ty h args hs' out ->
  @host_application hf mem base hs s ty h args hs' out.
Proof. intros [original _]. exact original. Qed.

Lemma denied_success auth owner hs s ty hs' after values :
  ~ @host_application hf mem (denying auth owner)
        hs s ty auth [owner] hs' (Some (after, result_values values)).
Proof.
  intros [_ excluded]. apply excluded. repeat split; eauto.
Qed.

Lemma unrelated_application auth owner hs s ty h args hs' out :
  (h <> auth \/ args <> [owner]) ->
  @host_application hf mem base hs s ty h args hs' out ->
  @host_application hf mem (denying auth owner) hs s ty h args hs' out.
Proof.
  intros other step. split; [exact step |].
  intros [same [same_args _]]. destruct other; contradiction.
Qed.

(** Forgetting the monitor gives a genuine run of the underlying host. *)
Lemma preserves_step auth owner hs s f es hs' s' f' es' :
  @reduce hf mem (denying auth owner) hs s f es hs' s' f' es' ->
  @reduce hf mem base hs s f es hs' s' f' es'.
Proof.
  intro step. induction step; solve [econstructor; eauto using original_application].
Qed.

Lemma preserves_execution auth owner start finish :
  @reduce_trans hf mem (denying auth owner) start finish ->
  @reduce_trans hf mem base start finish.
Proof.
  intro run. induction run as [x y step | x | x y z r1 ih1 r2 ih2].
  - apply Relation_Operators.rt_step.
    destruct x as [[[hs s] f] es], y as [[[hs' s'] f'] es'].
    eapply preserves_step. exact step.
  - apply Relation_Operators.rt_refl.
  - eapply Relation_Operators.rt_trans; eassumption.
Qed.

(** All imports with the Soroban auth name must resolve to the distinguished
    host handle. A module can omit the import: the condition then imposes no
    restriction and the no-bypass obligation still applies. *)
Definition binds_auth (m : module) (imports : list extern_value)
    (s : store_record) (auth : host_function) : Prop :=
  forall i type_index,
    nth_error (mod_imports m) i =
      Some {| imp_module := list_byte_of_string "a";
              imp_name := list_byte_of_string "0"; imp_desc := MID_func type_index |} ->
    exists address ty, nth_error imports i = Some (EV_func address) /\
       lookup_N (s_funcs s) address = Some (FC_func_host ty auth).

(** An exported call supplies exactly the parameters of its resolved closure.
    Extra operands in a Wasm evaluation context belong to the caller. *)
Definition entry_arguments (live : store_record) (address : funcaddr)
    (args : list value) : Prop :=
  exists callee params results,
    lookup_N (s_funcs live) address = Some callee /\
    cl_type callee = Tf params results /\
    List.length args = List.length params.

Definition no_bypass (m : module) (entry : string) (slot : nat) : Prop :=
  forall before deployed live imports instance_frame init_code auth address
         args owner hs hs' after caller caller' results,
    @instantiate hf mem base before m imports (deployed, instance_frame, init_code) ->
    store_extension deployed live = true ->
    binds_auth m imports live auth ->
    In {| exportinst_name := list_byte_of_string entry; exportinst_val := EV_func address |}
       (inst_exports (f_inst instance_frame)) ->
    entry_arguments live address args ->
    nth_error args slot = Some owner ->
    ~ @reduce_trans hf mem (denying auth owner)
        (hs, live, caller, List.app (v_to_e_list args) [AI_invoke address])
        (hs', after, caller', v_to_e_list results).
End Semantics.
End SorobanAuthorization.

Definition requires_auth (m : module) (entry : string) (slot : nat) : Prop :=
  forall hf mem (soroban : @host hf mem),
    SorobanAuthorization.no_bypass soroban m entry slot.

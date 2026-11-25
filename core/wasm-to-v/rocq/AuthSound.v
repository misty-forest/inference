From Coq Require List String NArith Bool
  Relations.Relation_Operators Relations.Operators_Properties.
From mathcomp Require eqtype ssrbool.
From Wasm Require memory host operations opsem properties instantiation_spec.

Module AuthSound.
Import List String NArith Bool Relation_Operators Operators_Properties.
Import eqtype ssrbool.
Import memory host operations opsem properties instantiation_spec.
Import AuthInvocation AuthOuter AuthStore.
Import ListNotations.
Local Open Scope list_scope.

Import GuardedExecution.

(** The execution argument uses only three facts from Wasm instantiation.
    The resolver supplies them for the module and export being certified. *)
Lemma auth_sound_from_link (m : module) (entry : string) (slot : nat)
    (callee : N) (ts rs : list value_type) (body : module_func)
    (link : forall hf mem (base : @host hf mem) before deployed live imports
                   fr init auth address,
       @instantiate hf mem base before m imports (deployed,fr,init) ->
       store_extension deployed live = true ->
       SorobanAuthorization.binds_auth m imports live auth ->
       In {|exportinst_name := list_byte_of_string entry; exportinst_val := EV_func address|}
          (inst_exports (f_inst fr)) ->
       exists addr,
         lookup_N (s_funcs live) address = Some (FC_func_native (Tf ts rs) (f_inst fr) body) /\
         lookup_N (inst_funcs (f_inst fr)) callee = Some addr /\
         lookup_N (s_funcs live) addr = Some (FC_func_host (Tf [T_num T_i64] [T_num T_i64]) auth)) :
    guarded_prefix (N.of_nat slot) callee false (modfunc_body body) ->
    requires_auth m entry slot.
Proof.
  intros Guard hf mem base before deployed live imports fr init auth address args owner
         hs hs' after caller caller' vals I Ext Bind Export Args Own Run.
  destruct (link hf mem base _ _ _ _ _ _ _ _ I Ext Bind Export)
    as [addr [Native [Call Host]]].
  destruct Args as [cl [ts' [rs' [Look [Ty Len]]]]]. rewrite Native in Look.
  injection Look as <-. change (Tf ts rs = Tf ts' rs') in Ty. inversion Ty; subst ts' rs'.
  set (h := SorobanAuthorization.denying base auth owner).
  destruct (native_invocation_reaches_frame h
      _ _ _ _ _ _ _ _ _ _ _ _ _ Native Len Run) as [defs [_ Tail]].
  set (P := fun (_ : @host_state hf mem h) (s : store_record) (f : frame)
                   (es : list administrative_instruction) =>
     bound addr auth s /\ frame_ok (N.of_nat slot) callee addr owner f /\
     scan (N.of_nat slot) callee addr owner es false (fun _ => False) false).
  eapply (frame_no_results h P); [| | | | |exact Tail].
  - intros h0 s0 f0 es h1 s1 f1 next [B [F G]] R. split.
    + eapply auth_reduce_lookup; eauto.
    + eapply step_sound; try exact R; try exact B; try exact F; try exact G.
      * exact (SorobanAuthorization.denied_success base auth owner).
      * unfold monotone. auto.
  - intros h0 s0 f0 es [_ [_ G]] V.
    destruct (const_es_exists V) as [vs ->]. eapply scan_no_values. exact G.
  - intros h0 s0 f0 es k lh vs [_ [_ G]] V <-.
    eapply scan_no_exit; [exact V|left; reflexivity|exact G].
  - intros h0 s0 f0 es k lh vs a [_ [_ G]] V <-.
    eapply scan_no_exit; [exact V|right; eauto|exact G].
  - split; [exact Host|]. split; [split|].
    + unfold lookup_N. cbn [f_locs]. rewrite Nat2N.id.
      rewrite List.nth_error_app1; [exact Own|apply List.nth_error_Some; congruence].
    + exact Call.
    + apply entry_label. exact Guard.
Qed.



Theorem resolved_auth_sound (m : module) (entry : string) (slot : nat)
    (callee absolute : N) (native_index : nat) (ts rs : list value_type)
    (body : module_func) :
    AuthResolve.resolve_static m entry callee =
      Some (absolute,native_index,Tf ts rs,body,Tf [T_num T_i64] [T_num T_i64]) ->
    guarded_prefix (N.of_nat slot) callee false (modfunc_body body) ->
    requires_auth m entry slot.
Proof.
  intros Static Guard. eapply auth_sound_from_link; [|exact Guard].
  intros hf mem base before deployed live imports fr init auth address I Ext Bind Export.
  eapply AuthResolve.auth_resolved; [exact Static|exact I|exact Ext|exact Bind|exact Export].
Qed.

Ltac prove_resolved_auth_at index :=
  eapply resolved_auth_sound with (callee := index);
    [vm_compute; reflexivity | prove_prefix].

(** Multiple aliases of the same Soroban host import are tried independently.
    Each candidate is checked against the export, the import signature and
    the call prefix in the generated WasmCert module. *)
Ltac prove_requires_auth :=
  lazymatch goal with
  | |- requires_auth ?m _ _ =>
    let number := eval vm_compute in (List.length (mod_imports m)) in
    let rec search count :=
      lazymatch count with
      | O => fail 0 "No certified require_auth call on the requested argument"
      | S ?remaining =>
        let i := eval vm_compute in (N.of_nat remaining) in
        first [solve [prove_resolved_auth_at i] | search remaining]
      end in
    search number
  end.
End AuthSound.

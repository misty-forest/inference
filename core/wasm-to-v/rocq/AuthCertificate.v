From Coq Require List String NArith.
From Wasm Require bytes datatypes.

Module AuthCertificate.
Import List String NArith bytes datatypes AuthForward.
Import ListNotations.
Local Open Scope list_scope.

(** Static witnesses live in the generated certificate. The same witness
    chooses the operational theorem, so the two checks cannot disagree on
    which helper receives the protected argument. *)
Inductive body_guard (m : module) (slot : nat) (auth : N) (body : module_func) : Prop :=
| direct :
    guarded_prefix (N.of_nat slot) auth false (modfunc_body body) ->
    body_guard m slot auth body
| forwarded : forall ops target position params results helper,
    modfunc_body body = wrapper_code ops target ->
    nth_error ops position = Some (from_local (N.of_nat slot)) ->
    AuthResolve.resolve_native m target = Some (Tf params results, helper) ->
    List.length ops = List.length params ->
    guarded_prefix (N.of_nat position) auth false (modfunc_body helper) ->
    body_guard m slot auth body.

Definition certificate (m : module) (entry : string) (slot : nat) : Prop :=
  exists auth absolute native params results body,
    AuthResolve.resolve_static m entry auth =
      Some (absolute, native, Tf params results, body, Tf [T_num T_i64] [T_num T_i64]) /\
    body_guard m slot auth body.

Theorem sound m entry slot : certificate m entry slot -> requires_auth m entry slot.
Proof.
  intros [auth [absolute [native [params [results [body [Link Guard]]]]]]].
  destruct Guard.
  - eapply AuthSound.resolved_auth_sound; eassumption.
  - eapply AuthForwardSound.forward_auth_sound; eassumption.
Qed.

Fixpoint forwarding_call (code : list basic_instruction) : option (list operand * N) :=
  match code with
  | [BI_call target] => Some ([], target)
  | BI_local_get arg :: tail =>
      option_map (fun '(args, target) => (from_local arg :: args, target)) (forwarding_call tail)
  | BI_const_num v :: tail =>
      option_map (fun '(args, target) => (from_num v :: args, target)) (forwarding_call tail)
  | _ => None
  end.

(** Every guessed index is checked against the original module in Gallina.
    Multiple occurrences of the owner or aliases of the auth import are OK. *)
Ltac choose_index count check :=
  lazymatch count with
  | O => fail 0 "No supported authorization guard for this argument"
  | S ?smaller => first [solve [check smaller] | choose_index smaller check]
  end.

Ltac prove_body :=
  first [apply direct; prove_prefix |
    lazymatch goal with
    | |- body_guard ?m ?slot ?auth ?body =>
      let shape := eval vm_compute in (forwarding_call (modfunc_body body)) in
      lazymatch shape with
      | Some (?actuals, ?destination) =>
        let count := eval compute in (List.length actuals) in
        let at_position pos :=
          eapply forwarded with (ops := actuals) (target := destination) (position := pos);
            [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | prove_prefix] in
        choose_index count at_position
      end
    end].

Ltac prove_certificate :=
  lazymatch goal with
  | |- certificate ?m ?entry ?slot =>
    let count := eval vm_compute in (List.length (mod_imports m)) in
    let at_import i :=
      let index := eval compute in (N.of_nat i) in
      let present := eval vm_compute in (AuthResolve.auth_import_type_index m index) in
      lazymatch present with
      | Some _ => exists index; do 5 eexists; split; [vm_compute; reflexivity | prove_body]
      end in
    choose_index count at_import
  end.
End AuthCertificate.

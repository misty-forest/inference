From Coq Require List String NArith.
From Wasm Require bytes datatypes.

Module AuthCertificate.
Import List String NArith bytes datatypes AuthForward AuthForwardSound.
Import ListNotations.
Local Open Scope list_scope.

Definition certificate (m : module) (entry : string) (slot : nat) : Prop :=
  exists auth absolute native params results body,
    AuthResolve.resolve_static m entry auth =
      Some (absolute, native, Tf params results, body, Tf [T_num T_i64] [T_num T_i64]) /\
    body_guard m slot auth body.

Theorem sound m entry slot : certificate m entry slot -> requires_auth m entry slot.
Proof.
  intros [auth [absolute [native [params [results [body [Link Guard]]]]]]].
  eapply certificate_body_sound; eassumption.
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

(** A repeated target on this path is a cycle: forwarding bodies have one
    unconditional successor. A cycle supplies no evidence of authorization. *)
Ltac prove_body_path seen :=
  first [apply direct; prove_prefix |
    lazymatch goal with
    | |- body_guard ?m ?slot ?auth ?body =>
      let shape := eval vm_compute in (forwarding_call (modfunc_body body)) in
      lazymatch shape with
      | Some (?actuals, ?destination) =>
        let repeated := eval vm_compute in (existsb (N.eqb destination) seen) in
        lazymatch repeated with
        | false =>
          let visited := constr:(destination :: seen) in
          let count := eval compute in (List.length actuals) in
          let at_position pos :=
            eapply forwarded with (ops := actuals) (target := destination) (position := pos);
              [reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | prove_body_path visited] in
          choose_index count at_position
        | true => fail 0 "Cycle in forwarded authorization calls"
        end
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
      | Some _ => exists index; do 5 eexists; split; [vm_compute; reflexivity | prove_body_path (@nil N)]
      end in
    first [choose_index count at_import |
           fail 1 "Cannot certify authorization of the original argument along a supported call chain"]
  end.
End AuthCertificate.

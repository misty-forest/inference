(** A structural certificate over the WasmCert module emitted by infc.
    The prefix may trap or diverge. A branch crossing the guard is accepted
    only when its target continuation starts with unreachable. *)
Require Import List String BinNat.
From Wasm Require Import bytes datatypes.
Import ListNotations.

Definition prefix_instruction (arg : N) (op : basic_instruction) : bool :=
  match op with
  | BI_local_set i | BI_local_tee i => negb (N.eqb i arg)
  | BI_local_get _ | BI_global_get _ | BI_global_set _
  | BI_const_num _ | BI_binop _ _ | BI_relop _ _ | BI_load _ _ _
  | BI_call _ => true
  | _ => false
  end.

Inductive guarded_prefix (arg callee : N) : bool -> list basic_instruction -> Prop :=
| guard_here : forall trapped tail,
    guarded_prefix arg callee trapped (BI_local_get arg :: BI_call callee :: tail)
| guard_step : forall trapped op tail, prefix_instruction arg op = true ->
    guarded_prefix arg callee trapped tail -> guarded_prefix arg callee trapped (op :: tail)
| guard_branch_to_trap : forall tail, guarded_prefix arg callee true tail ->
    guarded_prefix arg callee true (BI_br_if 0%N :: tail)
| guard_block : forall trapped bt body tail, guarded_prefix arg callee true body ->
    guarded_prefix arg callee trapped (BI_block bt body :: BI_unreachable :: tail).

Definition function_imports (m : module) :=
  List.filter (fun i => match imp_desc i with MID_func _ => true | _ => false end) (mod_imports m).

(** Enumerate pairs in function-index order, including only function imports. *)
Definition indexed {A : Type} (xs : list A) :=
  List.combine (List.seq 0 (List.length xs)) xs.

Definition has_call_guard (m : module) (entry : string) (arg : N)
    (provider field : string) : Prop :=
  exists absolute import_index import_type f,
    In {| modexp_name := list_byte_of_string entry; modexp_desc := MED_func absolute |} (mod_exports m) /\
    In (import_index, {| imp_module := list_byte_of_string provider;
                         imp_name := list_byte_of_string field;
                         imp_desc := MID_func import_type |}) (indexed (function_imports m)) /\
    nth_error (mod_types m) (N.to_nat import_type) =
      Some (Tf [T_num T_i64] [T_num T_i64]) /\
    (List.length (function_imports m) <= N.to_nat absolute)%nat /\
    nth_error (mod_funcs m) (N.to_nat absolute - List.length (function_imports m)) = Some f /\
    (exists params results, nth_error (mod_types m) (N.to_nat (modfunc_type f)) = Some (Tf params results)
                         /\ nth_error params (N.to_nat arg) = Some (T_num T_i64)) /\
    guarded_prefix arg (N.of_nat import_index) false (modfunc_body f).

Ltac find_member := first [left; reflexivity | right; find_member].
Ltac prove_prefix :=
  first [apply guard_here
        |apply guard_branch_to_trap; prove_prefix
        |apply guard_block; prove_prefix
        |apply guard_step; [reflexivity | prove_prefix]].

Local Ltac construct_call_guard :=
  unfold has_call_guard; do 4 eexists;
  split; [find_member |];
  split; [find_member |];
  split; [reflexivity |];
  split; [vm_compute; repeat constructor |];
  split; [reflexivity |];
  split; [do 2 eexists; split; reflexivity | prove_prefix].

Ltac prove_call_guard :=
  first [solve [construct_call_guard]
        | fail 1 "Cannot certify a direct call guard on the requested argument in this export"].

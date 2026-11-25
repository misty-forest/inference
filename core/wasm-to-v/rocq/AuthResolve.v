From Coq Require List String NArith PeanoNat Lia.
From mathcomp Require eqtype ssrbool.
From Wasm Require memory host operations opsem instantiation_spec instantiation_properties.

Module AuthResolve.
Import List String NArith PeanoNat Lia.
Import eqtype ssrbool.
Import memory host operations opsem instantiation_spec instantiation_properties.

Import ListNotations.

Section Link.
Context {hf : host_function_class} {mem : Memory} (base : @host hf mem).

Lemma module_typed_imports m ims es :
  module_typing m ims es ->
  exists c, tc_types c = mod_types m /\
    Forall2 (module_import_typing c) (mod_imports m) ims.
Proof.
  destruct m. intros [fts [tts [mts [gts [rts [dts H]]]]]].
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ [_ [I _]]]]]]]]]].
  eexists. split. 2: exact I. reflexivity.
Qed.

Lemma function_subtypes sigs actual :
  Forall2 import_subtyping actual (map ET_func sigs) ->
  actual = map ET_func sigs.
Proof.
  revert actual. induction sigs as [|t ts IH]; intros actual H;
    inversion H as [|actual_t y xs ys Rel Rest]; subst; auto.
  destruct actual_t; try discriminate.
  change (is_true (f == t)) in Rel. apply (elimT eqP) in Rel. subst f.
  cbn. f_equal. apply IH. exact Rest.
Qed.

Lemma function_import_addresses (s : store_record) sigs vs :
  Forall2 (external_typing s) vs (map ET_func sigs) ->
  exists addresses, vs = map EV_func addresses /\
    Forall2 (fun a t => ext_func_typing s a = Some t) addresses sigs.
Proof.
  revert vs. induction sigs as [|t ts IH]; intros vs H;
    inversion H as [|v y xs ys Rel Rest]; subst.
  - exists []. split; constructor.
  - destruct (IH _ Rest) as [addrs [-> Typed]].
    destruct v as [a|a|a|a]; unfold external_typing, ext_typing in Rel;
      match type of Rel with context[option_map _ ?q] => destruct q eqn:Q end;
      try discriminate.
    injection Rel as ->. exists (a :: addrs). split; [reflexivity|].
    constructor; assumption.
Qed.

Lemma mapped_addresses addrs : ext_funcs (map EV_func addrs) = addrs.
Proof. induction addrs as [|a xs IH]; cbn; congruence. Qed.

(** Allocating tables, memories, globals, elements and data preserves the
    function vector built by the first allocation phase. *)
Lemma allocation_functions s m imports gv rv deployed inst :
  @alloc_module hf mem s m imports gv rv (deployed,inst) ->
  List.length gv = List.length (mod_globals m) ->
  List.length rv = List.length (mod_elems m) ->
  inst_types inst = mod_types m /\
  inst_funcs inst = List.app (ext_funcs imports)
    (iota_N (List.length (s_funcs s)) (List.length (mod_funcs m))) /\
  inst_exports inst = map (get_exportinst inst) (mod_exports m) /\
  s_funcs deployed = List.app (s_funcs s) (map (fun mf => gen_func_instance mf inst) (mod_funcs m)).
Proof.
  unfold alloc_module.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Af.
  destruct (alloc_tabs _ _) as [s2 its] eqn:At.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Am.
  destruct (alloc_globs _ _ _) as [s4 igs] eqn:Ag.
  destruct (alloc_elems _ _ _) as [s5 ies] eqn:Ae.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Ad.
  intros [-> [Types [Funcs [_ [_ [_ [_ [_ Exps]]]]]]]] Lg Le.
  apply alloc_func_iota_N in Af as [I [F1 _]].
  apply alloc_table_iota_N in At as [_ [F2 _]].
  apply alloc_mem_iota_N in Am as [_ [F3 _]].
  apply alloc_global_iota_N in Ag as [_ [F4 _]]; [|exact Lg].
  apply alloc_elem_iota_N in Ae as [_ [F5 _]]; [|exact Le].
  apply alloc_data_iota_N in Ad as [_ [F6 _]].
  subst ifs. repeat split; try assumption.
  rewrite <- F6, <- F5, <- F4, <- F3, <- F2. exact F1.
Qed.

(** Read the type of every function import in order. This resolver accepts
    modules whose imports all occupy the function index space. *)
Fixpoint function_signatures types (imps : list module_import) : option (list function_type) :=
  match imps with
  | [] => Some []
  | imp :: tail =>
      match imp_desc imp with
      | MID_func type_index =>
          match lookup_N types type_index, function_signatures types tail with
          | Some sig, Some sigs => Some (sig :: sigs)
          | _, _ => None
          end
      | _ => None
      end
  end.

Definition named_function_export (m : module) (entry : string) : option N :=
  match filter (fun x => modexp_name x == list_byte_of_string entry) (mod_exports m) with
  | [e] => match modexp_desc e with MED_func n => Some n | _ => None end
  | _ => None
  end.

Definition auth_import_type_index (m : module) (ai : N) : option N :=
  match lookup_N (mod_imports m) ai with
  | Some imp =>
      match imp_desc imp with
      | MID_func ti =>
          if (imp_module imp == list_byte_of_string "a") && (imp_name imp == list_byte_of_string "0")
          then Some ti else None
      | _ => None
      end
  | None => None
  end.

Definition resolve_static (m : module) (entry : string) (auth_index : N)
    : option (N * nat * function_type * module_func * function_type) :=
  match function_signatures (mod_types m) (mod_imports m),
        named_function_export m entry, auth_import_type_index m auth_index with
  | Some sigs, Some absolute, Some _ =>
      let offset := List.length sigs in
      let n := N.to_nat absolute in
      if Nat.leb offset n then
        let native_index := n - offset in
        match nth_error (mod_funcs m) native_index, lookup_N sigs auth_index with
        | Some body, Some auth_type =>
            match lookup_N (mod_types m) (modfunc_type body) with
            | Some entry_type => Some (absolute,native_index,entry_type,body,auth_type)
            | None => None
            end
        | _, _ => None
        end
      else None
  | _, _, _ => None
  end.


Lemma signature_agreement c imps ims sigs :
  Forall2 (fun i t => module_import_typing c i t) imps ims ->
  function_signatures (tc_types c) imps = Some sigs ->
  ims = map ET_func sigs.
Proof.
  intros Typed. revert sigs.
  induction Typed as [|i t is ts T Rest IH]; intros sigs Read.
  - cbn in Read. injection Read as <-. reflexivity.
  - destruct i as [p q [idx|idx|idx|idx]]; cbn [function_signatures imp_desc] in Read; try discriminate.
    destruct (lookup_N (tc_types c) idx) as [ft|] eqn:F; try discriminate.
    destruct (function_signatures (tc_types c) is) as [tail|] eqn:R; try discriminate.
    injection Read as <-.
    unfold module_import_typing, module_import_desc_typing in T.
    cbn [imp_desc] in T. rewrite F in T. apply (elimT eqP) in T.
    injection T as <-. cbn. f_equal. apply IH. reflexivity.
Qed.

Lemma auth_import_selected m ai ti :
  auth_import_type_index m ai = Some ti ->
  lookup_N (mod_imports m) ai = Some
    {| imp_module := list_byte_of_string "a"; imp_name := list_byte_of_string "0";
       imp_desc := MID_func ti |}.
Proof.
  unfold auth_import_type_index.
  destruct (lookup_N (mod_imports m) ai) as [[p q [idx|idx|idx|idx]]|]; try discriminate.
  cbn [imp_desc imp_module imp_name]. destruct ((p == list_byte_of_string "a") && (q == list_byte_of_string "0")) eqn:Nms; try discriminate.
  apply (elimT andP) in Nms as [P Q]. apply (elimT eqP) in P. apply (elimT eqP) in Q.
  subst p q. intros E. now injection E as ->.
Qed.

Lemma export_selected m entry absolute inst address :
  named_function_export m entry = Some absolute ->
  In {|exportinst_name := list_byte_of_string entry; exportinst_val := EV_func address|}
    (map (get_exportinst inst) (mod_exports m)) ->
  address = nth (N.to_nat absolute) (inst_funcs inst) 0%N.
Proof.
  intros S I. apply in_map_iff in I as [exp [Eq Member]].
  assert (Name : modexp_name exp = list_byte_of_string entry).
  { exact (f_equal exportinst_name Eq). }
  assert (Selected : In exp (filter (fun e => modexp_name e == list_byte_of_string entry) (mod_exports m))).
  { apply filter_In. split; [exact Member|]. apply (introT eqP). exact Name. }
  unfold named_function_export in S.
  destruct (filter _ _) as [|chosen [|duplicate tail]]; try discriminate.
  destruct Selected as [<-|[]]. destruct chosen as [nm [idx|idx|idx|idx]]; try discriminate.
  cbn in S. injection S as ->. symmetry. unfold get_exportinst, export_get_v_ext in Eq. cbn [modexp_desc modexp_name] in Eq. injection Eq. intros X _. rewrite nat_bin in X. exact X.
Qed.

Theorem auth_resolved (m : module) (entry : string) (auth_index absolute : N) (native_index : nat)
    (entry_type : function_type) (body : module_func) (auth_type : function_type)
    before deployed live imports frame init_code auth address :
  resolve_static m entry auth_index = Some (absolute,native_index,entry_type,body,auth_type) ->
  @instantiate hf mem base before m imports (deployed,frame,init_code) ->
  store_extension deployed live = true ->
  SorobanAuthorization.binds_auth m imports live auth ->
  In {| exportinst_name := list_byte_of_string entry;
        exportinst_val := EV_func address |} (inst_exports (f_inst frame)) ->
  exists addrAuth,
    lookup_N (s_funcs live) address = Some (FC_func_native entry_type (f_inst frame) body) /\
    lookup_N (inst_funcs (f_inst frame)) auth_index = Some addrAuth /\
    lookup_N (s_funcs live) addrAuth = Some (FC_func_host auth_type auth).
Proof.
  unfold resolve_static. intros Static.
  destruct (function_signatures (mod_types m) (mod_imports m)) as [sigs|] eqn:Signatures; try discriminate.
  destruct (named_function_export m entry) as [idx|] eqn:ExportIndex; try discriminate.
  destruct (auth_import_type_index m auth_index) as [ti|] eqn:AuthImport; try discriminate.
  destruct (Nat.leb (List.length sigs) (N.to_nat idx)) eqn:Native; try discriminate.
  apply Nat.leb_le in Native.
  destruct (nth_error (mod_funcs m) (N.to_nat idx - List.length sigs)) as [code|] eqn:Body; try discriminate.
  destruct (lookup_N sigs auth_index) as [at_|] eqn:AuthType; try discriminate.
  destruct (lookup_N (mod_types m) (modfunc_type code)) as [ft|] eqn:FT; try discriminate.
  injection Static as Eidx Ei Eft Ebody Eat. subst absolute native_index entry_type body auth_type.
  set (k := (N.to_nat idx - List.length sigs)%nat) in *.
  intros [ims [its [es [hs [inst [gv [rv [Mt [Vt [Sub [Alloc [G [E [-> _]]]]]]]]]]]]]] Live Bind Export.
  cbn [f_inst] in *.
  apply module_typed_imports in Mt as [c [TypesC ImportsC]].
  rewrite <- TypesC in Signatures.
  apply (signature_agreement _ _ _ _ ImportsC) in Signatures. subst ims.
  apply function_subtypes in Sub. subst its.
  destruct (function_import_addresses _ _ _ Vt) as [addrs [-> Typed]].
  pose proof (List.Forall2_length Typed) as Laddrs.
  destruct (allocation_functions _ _ _ _ _ _ _ Alloc) as [Types [Funcs [Exports Store]]].
  { symmetry. exact (List.Forall2_length G). }
  { symmetry. exact (List.Forall2_length E). }
  rewrite mapped_addresses in Funcs.
  apply auth_import_selected in AuthImport.
  destruct (Bind (N.to_nat auth_index) ti AuthImport) as [a [t [Imp Host]]].
  rewrite List.nth_error_map in Imp.
  destruct (nth_error addrs (N.to_nat auth_index)) as [a'|] eqn:A; try discriminate.
  injection Imp as Eqa. subst a'. exists a.
  assert (AddrAuth : lookup_N (inst_funcs inst) auth_index = Some a).
  { unfold lookup_N. rewrite Funcs, nth_error_app1; [exact A|].
    apply nth_error_Some. rewrite A. discriminate. }
  assert (AddrEntry : nth_error (inst_funcs inst) (N.to_nat idx) =
    Some (N.of_nat (List.length (s_funcs before) + k))).
  { rewrite Funcs, nth_error_app2, Laddrs; try lia.
    apply iota_N_lookup. apply (introT ssrnat.ltP).
    apply nth_error_Some. rewrite Body. discriminate. }
  rewrite Exports in Export.
  pose proof (export_selected _ _ _ _ _ ExportIndex Export) as Index.
  assert (EntryAddress : address = N.of_nat (List.length (s_funcs before) + k)).
  { transitivity (List.nth (N.to_nat idx) (inst_funcs inst) 0%N); [exact Index|].
    exact (List.nth_error_nth _ _ 0%N AddrEntry). }
  assert (Keep : forall j fi, lookup_N (s_funcs before) j = Some fi -> lookup_N (s_funcs live) j = Some fi).
  { intros j fi H. eapply store_extension_lookup_func; [exact Live|].
    rewrite Store. unfold lookup_N in *. rewrite nth_error_app1; [exact H|].
    apply nth_error_Some. rewrite H. discriminate. }
  split.
  - eapply store_extension_lookup_func; [exact Live|].
    rewrite EntryAddress, Store. unfold lookup_N. rewrite Nat2N.id, nth_error_app2; try lia.
    replace (List.length (s_funcs before) + k - List.length (s_funcs before))%nat with k by lia.
    rewrite List.nth_error_map, Body. cbn [option_map].
    unfold gen_func_instance. now rewrite Types, FT.
  - split; [exact AddrAuth|].
    assert (Ext : ext_func_typing before a = Some at_).
    { eapply (@Forall2_nth_error _ _ (fun j ft => ext_func_typing before j = Some ft)); [exact Typed|exact A|exact AuthType]. }
    unfold ext_func_typing in Ext.
    destruct (lookup_N (s_funcs before) a) as [fi|] eqn:Before; try discriminate.
    apply Keep in Before. rewrite Host in Before. injection Before as <-.
    cbn in Ext. injection Ext as ->. exact Host.
Qed.
End Link.
End AuthResolve.

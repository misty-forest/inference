From Coq Require List String NArith Bool
  Relations.Relation_Operators Relations.Operators_Properties.
From mathcomp Require eqtype ssrbool.
From Wasm Require memory host operations opsem properties instantiation_spec.

Module AuthInvocation.
Import List String NArith Bool Relation_Operators Operators_Properties.
Import eqtype ssrbool.
Import memory host operations opsem properties instantiation_spec.
Import ListNotations.
Local Open Scope list_scope.

(** A terminating top-level invocation must perform a first reduction. This
    uses the actual WasmCert closure and also covers zero returned values. *)
Section Invocation.
Context {hf : host_function_class} {mem : Memory} (h : @host hf mem).

Lemma invoke_success_first hs s f args a hs' s' f' vals :
  @reduce_trans hf mem h (hs,s,f,v_to_e_list args ++ [AI_invoke a])
                         (hs',s',f',v_to_e_list vals) ->
  exists h1 s1 f1 es1,
    @reduce hf mem h hs s f (v_to_e_list args ++ [AI_invoke a]) h1 s1 f1 es1 /\
    @reduce_trans hf mem h (h1,s1,f1,es1) (hs',s',f',v_to_e_list vals).
Proof.
  intro Run. apply clos_rt_rt1n in Run.
  remember (hs,s,f,v_to_e_list args ++ [AI_invoke a]) as start eqn:E.
  remember (hs',s',f',v_to_e_list vals) as finish eqn:F.
  destruct Run as [|y z Step Tail].
  - rewrite E in F. injection F as _ _ _ Code.
    apply (f_equal const_list) in Code. rewrite v_to_e_const in Code.
    unfold const_list in Code. rewrite forallb_app in Code.
    rewrite andb_false_r in Code. discriminate.
  - subst start z. destruct y as [[[hy sy] fy] ey]. exists hy,sy,fy,ey.
    split; [exact Step|apply clos_rt1n_rt; exact Tail].
Qed.
End Invocation.

(** The actual guest body carries the guard consumed by the operational proof. *)


Import AuthEntry.
Section NativeEntry.
Context {hf : host_function_class} {mem : Memory} (h : @host hf mem).

Lemma native_invocation_reaches_frame hs s caller args a ts rs inst mf hs' s' caller' vals :
  lookup_N (s_funcs s) a = Some (FC_func_native (Tf ts rs) inst mf) ->
  List.length args = List.length ts ->
  @reduce_trans hf mem h (hs,s,caller,v_to_e_list args ++ [AI_invoke a])
                         (hs',s',caller',v_to_e_list vals) ->
  exists defaults, default_vals (modfunc_locals mf) = Some defaults /\
    @reduce_trans hf mem h
      (hs,s,caller,[AI_frame (List.length rs) (Build_frame (args ++ defaults) inst)
          [AI_label (List.length rs) [] (to_e_list (modfunc_body mf))]])
      (hs',s',caller',v_to_e_list vals).
Proof.
  intros Look Len Run.
  destruct (invoke_success_first h _ _ _ _ _ _ _ _ _ Run)
    as [h1 [s1 [f1 [es1 [Step Tail]]]]].
  destruct (entry_native_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Look Len Step)
    as [defs [D [-> [-> [-> ->]]]]]. now exists defs.
Qed.
End NativeEntry.
End AuthInvocation.

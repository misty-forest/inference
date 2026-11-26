From Wasm Require host opsem properties tactic.

Module AuthStore.
Import host opsem properties tactic.
Section Execution.
Context `{ho : host}.

Lemma auth_reduce_lookup hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  forall a callee, lookup_N (s_funcs s) a = Some callee ->
                   lookup_N (s_funcs s') a = Some callee.
Proof.
  intros step. induction step; intros address callee known; try exact known;
    try solve [eauto using store_extension_lookup_func, host_application_extension].
  all: unfold_store_operations; remove_bools_options; subst; try exact known; eauto.
Qed.
End Execution.
End AuthStore.

theory Wasm_Big_Step_Equiv imports "Wasm_Big_Step" begin

definition reduce_trans where
  "reduce_trans i \<equiv> (\<lambda>(s,vs,es) (s',vs',es'). \<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>)^**"

lemma reduce_trans_app:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s'';vs'';es''\<rparr>"
          "reduce_trans i (s'',vs'',es'') (s',vs',es')"
  shows "reduce_trans i (s,vs,es) (s',vs',es')"
proof -
  have 1:"(\<lambda>(s,vs,es) (s',vs',es'). \<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>) (s,vs,es) (s'',vs'',es'')"
    using assms
    by auto
  thus ?thesis
    using assms converse_rtranclp_into_rtranclp
    unfolding reduce_trans_def
    by (metis (no_types, lifting))
qed

lemma reduce_trans_app_end:
  assumes "\<lparr>s'';vs'';es''\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
          "reduce_trans i (s,vs,es) (s'',vs'',es'')"
  shows "reduce_trans i (s,vs,es) (s',vs',es')"
proof -
  have 1:"(\<lambda>(s,vs,es) (s',vs',es'). \<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>) (s'',vs'',es'') (s',vs',es')"
    using assms
    by auto
  thus ?thesis
    using assms 
    unfolding reduce_trans_def
    by (simp add: rtranclp.rtrancl_into_rtrancl)
qed
thm rtranclp_induct

lemma reduce_trans_L0:
  assumes "reduce_trans i (s,vs,es) (s',vs',es')"
  shows "reduce_trans i (s,vs,($$*ves)@es@es_f) (s',vs',($$*ves)@es'@es_f)"
  using assms
  unfolding reduce_trans_def
proof (induction "(s',vs',es')" arbitrary: s' vs' es' rule: rtranclp_induct)
  case base
  thus ?case
    by (auto split: prod.splits)
next
  case (step y)
  obtain s'' vs'' es'' where y_is:"y = (s'', vs'',es'')"
    by (cases y) blast
  hence "reduce_trans i (s,vs,($$*ves)@es@es_f) (s'',vs'',($$*ves)@es''@es_f)"
    using step(3)
    unfolding reduce_trans_def
    by simp
  moreover
  have "\<lparr>s'';vs'';es''\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
    using step(2) y_is
    by blast
  hence "\<lparr>s'';vs'';($$*ves)@es''@es_f\<rparr> \<leadsto>_i \<lparr>s';vs';($$*ves)@es'@es_f\<rparr>"
    using progress_L0 is_const_list
    by fastforce
  ultimately
  show ?case
    using y_is reduce_trans_app_end reduce_trans_def
    by auto
qed

lemma reduce_trans_label:
  assumes "reduce_trans i (s,vs,es) (s',vs',es')"
  shows "reduce_trans i (s,vs,[Label n les es]) (s',vs',[Label n les es'])"
  using assms
  unfolding reduce_trans_def
proof (induction "(s',vs',es')" arbitrary: s' vs' es' rule: rtranclp_induct)
  case base
  thus ?case
    by auto
next
  case (step y)
  obtain s'' vs'' es'' where y_is:"y = (s'', vs'',es'')"
    by (cases y) blast
  hence "reduce_trans i (s,vs,[Label n les es]) (s'',vs'',[Label n les es''])"
    using step(3)
    unfolding reduce_trans_def
    by simp
  moreover
  have 1:"\<lparr>s'';vs'';es''\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
    using step(2) y_is
    by blast
  have "\<lparr>s'';vs'';[Label n les es'']\<rparr> \<leadsto>_i \<lparr>s';vs';[Label n les es']\<rparr>"
    using reduce.label[OF 1] Lfilled.intros(2)[of "[]" _ n les "LBase [] []" "[]" 0]
    apply simp
    apply (meson Lfilled_exact.L0 Lfilled_exact_imp_Lfilled const_list_def list_all_simps(2))
    done
  ultimately
  show ?case
    using y_is reduce_trans_app_end reduce_trans_def
    by auto
qed

lemma reduce_trans_local:
  assumes "reduce_trans j (s,vs,es) (s',vs',es')"
  shows "reduce_trans i (s,v0s,[Local n j vs es]) (s',v0s,[Local n j vs' es'])"
  using assms
  unfolding reduce_trans_def
proof (induction "(s',vs',es')" arbitrary: s' vs' es' rule: rtranclp_induct)
  case base
  thus ?case
    by auto
next
  case (step y)
  obtain s'' vs'' es'' where y_is:"y = (s'', vs'',es'')"
    by (cases y) blast
  hence "reduce_trans i (s,v0s,[Local n j vs es]) (s'',v0s,[Local n j vs'' es''])"
    using step(3)
    unfolding reduce_trans_def
    by simp
  moreover
  have 1:"\<lparr>s'';vs'';es''\<rparr> \<leadsto>_j \<lparr>s';vs';es'\<rparr>"
    using step(2) y_is
    by blast
  have "\<lparr>s'';v0s;[Local n j vs'' es'']\<rparr> \<leadsto>_i \<lparr>s';v0s;[Local n j vs' es']\<rparr>"
    using reduce.local[OF 1]
    by blast
  ultimately
  show ?case
    using y_is reduce_trans_app_end reduce_trans_def
    by auto
qed
 

lemma reduce_trans_compose:
  assumes "reduce_trans i (s,vs,es) (s'',vs'',es'')"
          "reduce_trans i (s'',vs'',es'') (s',vs',es')"
  shows "reduce_trans i (s,vs,es) (s',vs',es')"
  using assms
  unfolding reduce_trans_def
  by auto


lemma Wasm_Big_Step_Sound:
  assumes "((s,vs,es) \<Down>{(ls,r,i)} (s',vs',res))"
  shows "(res = RTrap \<longrightarrow> reduce_trans i (s,vs,es) (s',vs',[Trap])) \<and>
         (\<forall>rvs. (res = RValue rvs \<longrightarrow> reduce_trans i (s,vs,es) (s',vs',$$*rvs)))"
  using assms
proof (induction "(s,vs,es)" "(ls,r,i)" "(s',vs',res)" arbitrary: s vs vs' s' es res ls r i rule: reduce_to.induct)
  case (emp s vs)
  thus ?case
    unfolding reduce_trans_def
    by auto
next
  case (unop s vs v t op)
  thus ?case
    using reduce.basic[OF reduce_simple.unop]
    unfolding reduce_trans_def
    by auto
next
  case (binop_Some op v1 v2 v s vs t)
  thus ?case
    using reduce.basic[OF reduce_simple.binop_Some]
    unfolding reduce_trans_def
    by auto
next
  case (binop_None op v1 v2 s vs t)
  thus ?case
    using reduce.basic[OF reduce_simple.binop_None]
    unfolding reduce_trans_def
    by auto
next
  case (testop s vs v t op)
  thus ?case
    using reduce.basic[OF reduce_simple.testop]
    unfolding reduce_trans_def
    by auto
next
  case (relop s vs v1 v2 t op)
  thus ?case
    using reduce.basic[OF reduce_simple.relop]
    unfolding reduce_trans_def
    by auto
next
  case (convert_Some t1 v t2 sx v' s vs)
  thus ?case
    using reduce.basic[OF reduce_simple.convert_Some]
    unfolding reduce_trans_def
    by auto
next
  case (convert_None t1 v t2 sx s vs)
  thus ?case
    using reduce.basic[OF reduce_simple.convert_None]
    unfolding reduce_trans_def
    by auto
next
  case (reinterpret t1 v s vs t2)
  thus ?case
    using reduce.basic[OF reduce_simple.reinterpret]
    unfolding reduce_trans_def
    by auto
next
  case (unreachable s vs)
  thus ?case
    using reduce.basic[OF reduce_simple.unreachable]
    unfolding reduce_trans_def
    by auto
next
  case (nop s vs)
  thus ?case
    using reduce.basic[OF reduce_simple.nop]
    unfolding reduce_trans_def
    by auto
next
  case (drop s vs v)
  thus ?case
    using reduce.basic[OF reduce_simple.drop]
    unfolding reduce_trans_def
    by auto
next
  case (select_false n s vs v1 v2)
  thus ?case
    using reduce.basic[OF reduce_simple.select_false]
    unfolding reduce_trans_def
    by auto
next
  case (select_true n s vs v1 v2)
  thus ?case
    using reduce.basic[OF reduce_simple.select_true]
    unfolding reduce_trans_def
    by auto
next
  case (block ves n t1s t2s m s vs es s' vs')
  thus ?case
    using reduce.basic[OF reduce_simple.block] reduce_trans_app
    by metis
next
  case (loop ves n t1s t2s m s vs es s' vs')
  thus ?case
    using reduce.basic[OF reduce_simple.loop] reduce_trans_app
    by metis
next
  case (if_false n ves s vs tf e2s s' vs' e1s)
  thus ?case
    using progress_L0_left[OF reduce.basic[OF reduce_simple.if_false]] reduce_trans_app
    by metis
next
  case (if_true n ves s vs tf e1s s' vs' e2s)
  thus ?case
    using progress_L0_left[OF reduce.basic[OF reduce_simple.if_true]] reduce_trans_app
    by metis
next
  case (br vcs n k s vs)
  thus ?case
    by auto
next
  case (br_if_false n s vs k)
  thus ?case
    using reduce.basic[OF reduce_simple.br_if_false]
    unfolding reduce_trans_def
    by auto
next
  case (br_if_true n ves s vs k s' vs')
  thus ?case
    using progress_L0_left[OF reduce.basic[OF reduce_simple.br_if_true]] reduce_trans_app
    by metis
next
  case (br_table ks c ves s vs s' vs' k)
  thus ?case
    using progress_L0_left[OF reduce.basic[OF reduce_simple.br_table]] reduce_trans_app
    by metis
next
  case (br_table_length ks c ves s vs k s' vs')
  thus ?case
    using progress_L0_left[OF reduce.basic[OF reduce_simple.br_table_length]] reduce_trans_app
    by metis
next
  case (return vcs r s vs)
  thus ?case
    by auto
next
  case (get_local vi j s v vs)
  thus ?case
    using reduce.get_local
    unfolding reduce_trans_def
    by auto
next
  case (set_local vi j s v vs v')
  thus ?case
    using reduce.set_local
    unfolding reduce_trans_def
    by auto
next
  case (tee_local v s vs i s' vs')
  thus ?case
    using reduce.basic[OF reduce_simple.tee_local] reduce_trans_app
    by metis
next
  case (get_global s vs j)
  thus ?case
    using reduce.get_global
    unfolding reduce_trans_def
    by auto
next
  case (set_global s j v s' vs)
  thus ?case
    using reduce.set_global
    unfolding reduce_trans_def
    by auto
next
  case (load_Some s j m k off t bs vs a)
  thus ?case
    using reduce.load_Some
    unfolding reduce_trans_def
    by auto
next
  case (load_None s j m k off t vs a)
  thus ?case
    using reduce.load_None
    unfolding reduce_trans_def
    by auto
next
  case (load_packed_Some s j m sx k off tp t bs vs a)
  thus ?case
    using reduce.load_packed_Some
    unfolding reduce_trans_def
    by auto
next
  case (load_packed_None s j m sx k off tp t vs a)
  thus ?case
    using reduce.load_packed_None
    unfolding reduce_trans_def
    by auto
next
  case (store_Some t v s j m k off mem' vs a)
  thus ?case
    using reduce.store_Some
    unfolding reduce_trans_def
    by auto
next
  case (store_None t v s j m k off vs a)
  thus ?case
    using reduce.store_None
    unfolding reduce_trans_def
    by auto
next
  case (store_packed_Some t v s j m k off tp mem' vs a)
  thus ?case
    using reduce.store_packed_Some
    unfolding reduce_trans_def
    by auto
next
  case (store_packed_None t v s j m k off tp vs a)
  thus ?case
    using reduce.store_packed_None
    unfolding reduce_trans_def
    by auto
next
  case (current_memory s j m n vs)
  thus ?case
    using reduce.current_memory
    unfolding reduce_trans_def
    by auto
next
  case (grow_memory s j m n c mem' vs)
  thus ?case
    using reduce.grow_memory
    unfolding reduce_trans_def
    by auto
next
  case (grow_memory_fail s j m n vs c)
  thus ?case
    using reduce.grow_memory_fail
    unfolding reduce_trans_def
    by auto
next
  case (call ves s vs j s' vs')
  thus ?case
    using progress_L0_left[OF reduce.call] reduce_trans_app
    by metis
next
  case (call_indirect_Some s c cl j tf ves vs s' vs')
  thus ?case
    using progress_L0_left[OF reduce.call_indirect_Some] reduce_trans_app
    by metis
next
  case (call_indirect_None s c cl j vs)
  thus ?case
    using reduce.call_indirect_None
    unfolding reduce_trans_def
    by auto
next
  case (callcl_native cl j t1s t2s ts es ves vcs n k m zs s vs s' vs')
  thus ?case
    using reduce.callcl_native reduce_trans_app
    by metis
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs)
  thus ?case
    using reduce.callcl_host_Some
    unfolding reduce_trans_def
    by auto
next
  case (callcl_host_None cl t1s t2s f ves vcs n m s vs)
  thus ?case
    using reduce.callcl_host_None
    unfolding reduce_trans_def
    by auto
next
  case (const_value s vs es s' vs' res ves)
  hence 1:"reduce_trans i (s, vs, es) (s', vs', $$* res)"
    by simp
  show ?case
    using reduce_trans_L0[OF 1, of ves "[]"]
    by simp
next
  case (label_value s vs es n ls r i s' vs' res les)
  hence 1:"reduce_trans i (s, vs, es)  (s', vs',$$* res)"
    by fastforce
  have "\<lparr>s'; vs'; [Label n les ($$* res)]\<rparr> \<leadsto>_i \<lparr>s'; vs'; $$* res \<rparr>"
    using reduce.basic[OF reduce_simple.label_const] is_const_list
    by fastforce
  thus ?case
    using reduce_trans_label[OF 1, of n les] reduce_trans_app_end
    by blast
next
  case (local_value s lls es n j s' lls' res vs)
  hence 1:"reduce_trans j (s, lls, es) (s', lls', $$* res)"
    by simp
  have "reduce_trans i (s, vs, [Local n j lls es]) (s', vs, [Local n j lls' ($$* res)])"
    using reduce_trans_local[OF 1]
    by blast
  moreover
  have "\<lparr>s'; vs; [Local n j lls' ($$* res)]\<rparr> \<leadsto>_i \<lparr>s'; vs; ($$* res)\<rparr>"
    using reduce.basic[OF reduce_simple.local_const] is_const_list
    by fastforce
  ultimately
  show ?case
    using reduce_trans_app_end
    by blast
next
  case (seq_value s vs es s'' vs'' res'' es' s' vs' res')
  hence 1:"reduce_trans i (s, vs, es) (s'', vs'', $$* res'')"
    by simp
  show ?case
  proof (cases res')
    case (RValue x1)
    hence "reduce_trans i (s'', vs'', ($$* res'') @ es') (s', vs', $$* x1)"
      using seq_value
      by simp
    moreover
    have "reduce_trans i (s, vs, es@es') (s'', vs'', ($$* res'')@es')"
      using reduce_trans_L0[OF 1, of "[]"]
      by fastforce
    ultimately
    show ?thesis
      using RValue reduce_trans_compose
      by blast
  next
    case RTrap
    hence "reduce_trans i (s'', vs'', ($$* res'') @ es') (s', vs', [Trap])"
      using seq_value
      by simp
    moreover
    have "reduce_trans i (s, vs, es@es') (s'', vs'', ($$* res'')@es')"
      using reduce_trans_L0[OF 1, of "[]"]
      by fastforce
    ultimately
    show ?thesis
      using RTrap reduce_trans_compose
      by blast
  qed auto
next
  case (seq_nonvalue1 ves s vs es s' vs' res')
  thus ?case
  proof (cases res')
    case RTrap
    hence 1:"reduce_trans i (s, vs, es) (s', vs', [Trap])"
      using seq_nonvalue1
      by simp
    hence "reduce_trans i (s, vs, ves@es) (s', vs', ves@[Trap])"
      using reduce_trans_L0[OF 1, of _ "[]"]  e_type_const_conv_vs[OF seq_nonvalue1(1)]
      by fastforce
    moreover
    have "\<lparr>s';vs';ves@[Trap]\<rparr> \<leadsto>_i \<lparr>s';vs';[Trap]\<rparr>"
      using seq_nonvalue1 reduce.basic[OF reduce_simple.trap] RTrap
      apply simp
      apply (metis Lfilled.intros(1) append_Nil2 self_append_conv2)
      done
    ultimately
    show ?thesis
      using RTrap reduce_trans_app_end
      by auto
  qed auto
next
  case (seq_nonvalue2 s vs es s' vs' res es')
  thus ?case
  proof (cases res)
    case RTrap
    hence 1:"reduce_trans i (s, vs, es) (s', vs', [Trap])"
      using seq_nonvalue2
      by simp
    hence "reduce_trans i (s, vs, es@es') (s', vs', [Trap]@es')"
      using reduce_trans_L0[OF 1, of "[]"]
      by fastforce
    moreover
    have "Lfilled 0 (LBase [] es') [Trap] ([Trap]@es')"
      using seq_nonvalue2(4)
      by (metis Lfilled.L0 const_list_def list_all_simps(2) self_append_conv2)
    hence "\<lparr>s';vs';[Trap]@es'\<rparr> \<leadsto>_i \<lparr>s'; vs'; [Trap]\<rparr>"
      using reduce.basic[OF reduce_simple.trap] seq_nonvalue2(4)
      by auto
    ultimately
    show ?thesis
      using RTrap reduce_trans_app_end
      by auto
  qed auto
next
  case (label_trap s vs es n ls r i s' vs' les)
  hence 1:"reduce_trans i (s, vs, es) (s', vs', [Trap])"
    by simp
  have "reduce_trans i (s, vs, [Label n les es]) (s', vs', [Label n les [Trap]])"
    using reduce_trans_label[OF 1]
    by blast
  moreover
  have "\<lparr>s'; vs'; [Label n les [Trap]]\<rparr> \<leadsto>_i \<lparr>s'; vs'; [Trap]\<rparr>"
    using reduce.basic[OF reduce_simple.label_trap]
    by blast
  ultimately
  show ?case
    using reduce_trans_app_end
    by blast
next
  case (local_trap s lls es n j s' lls' vs)
  hence 1:"reduce_trans j (s, lls, es) (s', lls', [Trap])"
    by simp
  have "reduce_trans i (s, vs, [Local n j lls es]) (s', vs, [Local n j lls' [Trap]])"
    using reduce_trans_local[OF 1]
    by blast
  moreover
  have "\<lparr>s'; vs; [Local n j lls' [Trap]]\<rparr> \<leadsto>_i \<lparr>s'; vs; [Trap]\<rparr>"
    using reduce.basic[OF reduce_simple.local_trap] is_const_list
    by fastforce
  ultimately
  show ?case
    using reduce_trans_app_end
    by blast
next
  case (label_break_suc s vs es n s' vs' bn bvs les)
  thus ?case
    by auto
next
  case (label_break_nil s vs es n ls r s'' vs'' bvs les s' vs' res)
  thus ?case sorry
next
  case (label_return s vs es n s' vs' rvs les)
  thus ?case
    by auto
next
  case (local_return s lls es n j s' lls' rvs vs)
  thus ?case sorry
qed

end
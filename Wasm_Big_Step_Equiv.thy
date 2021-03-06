theory Wasm_Big_Step_Equiv imports "Wasm_Big_Step" begin

lemma lfilled_label_forward_helper:
  assumes "Lfilled na lholed es lfes"
          "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  shows "\<exists>lfes'. Lfilled na lholed es' lfes' \<and> \<lparr>s;vs;[Label n les lfes]\<rparr> \<leadsto>_i \<lparr>s';vs';[Label n les lfes']\<rparr>"
proof -
  obtain lfes' where "Lfilled na lholed es' lfes'"
    using assms(1) progress_LN2
    by blast
  thus ?thesis
    using reduce.label assms(1,2) progress_label
    by metis
qed

lemma lfilled_label_forward_helper_trans:
  assumes "Lfilled na lholed es lfes"
          "reduce_trans i (s,vs,es) (s',vs',es')"
  shows "\<exists>lfes'. Lfilled na lholed es' lfes' \<and> reduce_trans i (s,vs,lfes) (s',vs',lfes')"
proof -
  obtain lfes' where "Lfilled na lholed es' lfes'"
    using assms(1) progress_LN2
    by blast
  thus ?thesis
    using assms(1,2) reduce_trans_lfilled
    by blast
qed

lemma lfilled_local_forward_helper:
  assumes "Lfilled na lholed es lfes"
          "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  shows "\<exists>lfes'. Lfilled na lholed es' lfes' \<and> \<lparr>s;v0s;[Local n i vs lfes]\<rparr> \<leadsto>_j \<lparr>s';v0s;[Local n i vs' lfes']\<rparr>"
proof -
  obtain lfes' where "Lfilled na lholed es' lfes'"
    using assms(1) progress_LN2
    by blast
  thus ?thesis
    using reduce.label assms(1,2) reduce.local
    by metis
qed

lemma reduce_to_imp_reduce_trans:
  assumes "((s,vs,es) \<Down>{(ls,r,i)} (s',vs',res))"
  shows "(res = RTrap \<longrightarrow> reduce_trans i (s,vs,es) (s',vs',[Trap])) \<and>
         (\<forall>rvs. (res = RValue rvs \<longrightarrow> reduce_trans i (s,vs,es) (s',vs',$$*rvs))) \<and>
         (\<forall>n rvs lholed lfes les. (res = RBreak n rvs \<longrightarrow> (Lfilled n lholed es lfes \<longrightarrow> (ls!n = length rvs \<and> reduce_trans i (s,vs,[Label (ls!n) les lfes]) (s',vs',($$*rvs)@les))))) \<and>
         (\<forall>n rvs lholed lfes j v0s. (res = RReturn rvs \<longrightarrow> (Lfilled n lholed es lfes \<longrightarrow> (r = Some (length rvs) \<and> reduce_trans j (s,v0s,[Local (length rvs) i vs lfes]) (s',v0s,$$*rvs)))))"
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
  case (block ves n t1s t2s m s vs es s' vs' res)
  have 1:"\<lparr>s;vs;ves @ [$Block (t1s _> t2s) es]\<rparr> \<leadsto>_ i \<lparr>s;vs;[Label m [] (ves @ ($* es))]\<rparr>"
    using reduce.basic[OF reduce_simple.block[OF block(1,2,3,4)]]
    by blast
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app block(6)
      by simp
  next
    case (RBreak k rvs)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app block(6)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app block(6)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app block(6)
      by simp
  qed
next
  case (loop ves n t1s t2s m s vs es s' vs' res)
  have 1:"\<lparr>s;vs;ves @ [$Loop (t1s _> t2s) es]\<rparr> \<leadsto>_ i \<lparr>s;vs;[Label n [$Loop (t1s _> t2s) es] (ves @ ($* es))]\<rparr>"
    using reduce.basic[OF reduce_simple.loop[OF loop(1,2,3,4)]]
    by blast
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app loop(6)
      by simp
  next
    case (RBreak k rvs)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app loop(6)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app loop(6)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app loop(6)
      by simp
  qed
next
  case (if_false n ves s vs tf e2s s' vs' res e1s)
  have 1:"\<lparr>s;vs;ves @ [$C ConstInt32 n, $If tf e1s e2s]\<rparr> \<leadsto>_ i \<lparr>s;vs;ves @ [$Block tf e2s]\<rparr>"
    using progress_L0_left[OF reduce.basic[OF reduce_simple.if_false[OF if_false(1)]]] if_false(2)
    by blast
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app if_false(4)
      by simp
  next
    case (RBreak k rvs)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app if_false(4)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app if_false(4)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app if_false(4)
      by simp
  qed
next
  case (if_true n ves s vs tf e1s s' vs' res e2s)
  have 1:"\<lparr>s;vs;ves @ [$C ConstInt32 n, $If tf e1s e2s]\<rparr> \<leadsto>_ i \<lparr>s;vs;ves @ [$Block tf e1s]\<rparr>"
    using progress_L0_left[OF reduce.basic[OF reduce_simple.if_true[OF if_true(1)]]] if_true(2)
    by blast
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app if_true(4)
      by simp
  next
    case (RBreak k rvs)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app if_true(4)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app if_true(4)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app if_true(4)
      by simp
  qed
next
  case (br vcs n ls k s vs r i)
  thus ?case
    using reduce.basic[OF reduce_simple.br, of "($$* vcs)" n] is_const_list
    by (fastforce simp add: reduce_trans_def)
next
  case (br_if_false n s vs k)
  thus ?case
    using reduce.basic[OF reduce_simple.br_if_false]
    unfolding reduce_trans_def
    by auto
next
  case (br_if_true n ves s vs k s' vs' res)
  have 1:"\<lparr>s;vs;ves @ [$C ConstInt32 n, $Br_if k]\<rparr> \<leadsto>_i \<lparr>s;vs;ves @ [$Br k]\<rparr>"
    using progress_L0_left[OF reduce.basic[OF reduce_simple.br_if_true]] br_if_true(1,2)
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app br_if_true
      by simp
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app br_if_true(4)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app br_if_true(4)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app br_if_true
      by simp
  qed
next
  case (br_table ks c ves s vs s' vs' res k)
  have 1:"\<lparr>s;vs;ves @ [$C ConstInt32 c, $Br_table ks k]\<rparr> \<leadsto>_i \<lparr>s;vs;ves @ [$Br (ks ! Wasm_Base_Defs.nat_of_int c)]\<rparr>"
    using progress_L0_left[OF reduce.basic[OF reduce_simple.br_table]] br_table(1,2)
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app br_table
      by simp
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app br_table(4)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app br_table(4)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app br_table
      by simp
  qed
next
  case (br_table_length ks c ves s vs k s' vs' res)
  have 1:"\<lparr>s;vs;ves @ [$C ConstInt32 c, $Br_table ks k]\<rparr> \<leadsto>_i \<lparr>s;vs;ves @ [$Br k]\<rparr>"
    using progress_L0_left[OF reduce.basic[OF reduce_simple.br_table_length]] br_table_length(1,2)
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app br_table_length
      by simp
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app br_table_length(4)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app br_table_length(4)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app br_table_length
      by simp
  qed
next
  case (return vcs r s vs)
  thus ?case
    using reduce.basic[OF reduce_simple.return, of "($$* vcs)"] is_const_list
    by (fastforce simp add: reduce_trans_def)
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
  case (tee_local v s vs j s' vs' res)
  have 1:"\<lparr>s;vs;[v, $Tee_local j]\<rparr> \<leadsto>_i \<lparr>s;vs;[v, v, $Set_local j]\<rparr>"
    using reduce.basic[OF reduce_simple.tee_local] tee_local(1,2)
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app tee_local
      by simp
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app tee_local(3)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app tee_local(3)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app tee_local(3)
      by simp
  qed
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
  case (call ves s vs i j ls r s' vs' res)
  have 1:"\<lparr>s;vs;ves @ [$Call j]\<rparr> \<leadsto>_i \<lparr>s;vs;ves @ [Invoke (sfunc s i j)]\<rparr>"
    using progress_L0_left[OF reduce.call] call(1)
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app call(3)
      by simp
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app call(3)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app call(3)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app call(3)
      by simp
  qed
next
  case (call_indirect_Some s i c cl j tf ves vs ls r s' vs' res)
  have 1:"\<lparr>s;vs;ves @ [$C ConstInt32 c, $Call_indirect j]\<rparr> \<leadsto>_i \<lparr>s;vs;ves @ [Invoke cl]\<rparr>"
    using progress_L0_left[OF reduce.call_indirect_Some] call_indirect_Some
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app call_indirect_Some(6)
      by simp
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app call_indirect_Some(6)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app call_indirect_Some(6)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app call_indirect_Some(6)
      by simp
  qed
next
  case (call_indirect_None s c cl j vs)
  thus ?case
    using reduce.call_indirect_None
    unfolding reduce_trans_def
    by auto
next
  case (invoke_native cl j t1s t2s ts es ves vcs n k m zs s vs ls r i s' vs' res)
  have 1:"\<lparr>s;vs;ves @ [Invoke cl]\<rparr> \<leadsto>_i \<lparr>s;vs;[Local m j (vcs @ zs) [$Block ([] _> t2s) es]]\<rparr>"
    using reduce.invoke_native[OF invoke_native(1,2,3,4,5,6,7)]
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    thus ?thesis
      using 1 reduce_trans_app invoke_native(9)
      by simp
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lfilled_label_forward_helper[OF _ 1] reduce_trans_app invoke_native(9)
      by simp metis
  next
    case (RReturn x3)
    thus ?thesis
      using lfilled_local_forward_helper[OF _ 1] reduce_trans_app invoke_native(9)
      by simp metis
  next
    case RTrap
    thus ?thesis
      using 1 reduce_trans_app invoke_native(9)
      by simp
  qed
next
  case (invoke_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs)
  thus ?case
    using reduce.invoke_host_Some
    unfolding reduce_trans_def
    by auto
next
  case (invoke_host_None cl t1s t2s f ves vcs n m s vs)
  thus ?case
    using reduce.invoke_host_None
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
  hence 0:"reduce_trans i (s, vs, es) (s'', vs'', $$* res'')"
    by simp
  have 1:"reduce_trans i (s, vs, es@es') (s'', vs'', ($$* res'')@es')"
    using reduce_trans_L0[OF 0, of "[]"]
    by fastforce
  show ?case
  proof (cases res')
    case (RValue x1)
    hence "reduce_trans i (s'', vs'', ($$* res'') @ es') (s', vs', $$* x1)"
      using seq_value
      by simp
    thus ?thesis
      using RValue reduce_trans_compose 1
      by blast
  next
    case (RBreak j vcs)
    thus ?thesis
      using 1 seq_value(4) lfilled_label_forward_helper_trans[OF _ 1]
      by simp (meson reduce_trans_compose reduce_trans_label)
  next
    case (RReturn x3)
    thus ?thesis
      using 1 seq_value(4) lfilled_label_forward_helper_trans[OF _ 1]
      by simp (meson reduce_trans_compose reduce_trans_local)
  next
    case RTrap
    hence "reduce_trans i (s'', vs'', ($$* res'') @ es') (s', vs', [Trap])"
      using seq_value
      by simp
    thus ?thesis
      using RTrap reduce_trans_compose 1
      by blast
  qed
next
  case (seq_nonvalue1 ves s vs es s' vs' res')
  thus ?case
  proof (cases res')
    case (RBreak j rvs)
    {
      fix lholed lfes
      assume "Lfilled j lholed (ves @ es) lfes"
      hence "\<exists>lholed'. Lfilled j lholed' es lfes"
        using lfilled_collapse1[OF _ seq_nonvalue1(1), of _ _ _ _ "0"]
        by simp
    }
    thus ?thesis
      using RBreak seq_nonvalue1(3)
      by simp blast
  next
    case (RReturn x3)
    {
      fix j lholed lfes
      assume "Lfilled j lholed (ves @ es) lfes"
      hence "\<exists>lholed'. Lfilled j lholed' es lfes"
        using lfilled_collapse1[OF _ seq_nonvalue1(1), of _ _ _ _ "0"]
        by simp
    }
    thus ?thesis
      using RReturn seq_nonvalue1(3)
      by simp blast
  next
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
    case (RBreak j rvs)
    {
      fix lholed lfes
      assume "Lfilled j lholed (es @ es') lfes"
      hence "\<exists>lholed'. Lfilled j lholed' es lfes"
        using lfilled_collapse2
        by simp
    }
    thus ?thesis
      using RBreak seq_nonvalue2(2)
      by simp blast
  next
    case (RReturn x3)
    {
      fix j lholed lfes
      assume "Lfilled j lholed (es @ es') lfes"
      hence "\<exists>lholed'. Lfilled j lholed' es lfes"
        using lfilled_collapse2
        by simp
    }
    thus ?thesis
      using RReturn seq_nonvalue2(2)
      by simp blast
  next
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
  case (label_break_suc s vs es n ls r i s' vs' bn bvs les)
  thus ?case
    using lfilled_collapse3
    by simp blast
next
  case (label_break_nil s vs es n ls r i s'' vs'' bvs vcs les s' vs' res)
  have 0:"reduce_trans i (s, vs, [Label n les es]) (s'', vs'', ($$* bvs) @ les)"
    using label_break_nil(2) Lfilled_exact.L0 Lfilled_exact_imp_Lfilled
    by simp blast
  hence 1:"reduce_trans i (s, vs, ($$* vcs) @ [Label n les es]) (s'', vs'', ($$*vcs @ bvs) @ les)"
    using reduce_trans_L0[OF 0, of vcs "[]"]
    by fastforce
  show ?case
  proof (cases res)
    case (RValue x1)
    hence "reduce_trans i (s'', vs'', ($$* vcs @ bvs) @ les) (s', vs', $$* x1)"
      using label_break_nil
      by simp
    thus ?thesis
      using RValue reduce_trans_compose 1
      by blast
  next
    case (RBreak j vcs)
    thus ?thesis
      using 1 label_break_nil(4) lfilled_label_forward_helper_trans[OF _ 1]
      by simp (meson reduce_trans_compose reduce_trans_label)
  next
    case (RReturn x3)
    thus ?thesis
      using 1 label_break_nil(4) lfilled_label_forward_helper_trans[OF _ 1]
      by simp (meson reduce_trans_compose reduce_trans_local)
  next
    case RTrap
    hence "reduce_trans i (s'', vs'', ($$* vcs @ bvs) @ les) (s', vs', [Trap])"
      using label_break_nil
      by simp
    thus ?thesis
      using RTrap reduce_trans_compose 1
      by blast
  qed
next
  case (label_return s vs es n ls r i s' vs' rvs les)
  thus ?case
    using lfilled_collapse3
    by simp blast
next
  case (local_return s lls es n j s' lls' rvs vs)
  thus ?case
    using Lfilled_exact.L0 Lfilled_exact_imp_Lfilled
    by simp blast
next
  case (trap s vs)
  thus ?case
    unfolding reduce_trans_def
    by simp
qed

lemma reduce_to_n_return_lfilled:
  assumes "Lfilled j lholed (($$*vcs) @ [$Return]) es"
          "length vcs = n"
  shows "((s,vs,es) \<Down>{(ls,Some n,i)} (s,vs,RReturn vcs))"
  using assms
proof (induction j lholed "(($$*vcs) @ [$Return])" es arbitrary: ls rule: Lfilled.induct)
  case (L0 vls lholed es')
  have "(s, vs, ($$* vcs) @ [$Return]) \<Down>{(ls, Some n, i)} (s, vs, RReturn vcs)"
    using reduce_to.return[OF L0(3)]
    by fastforce
  thus ?case
    using reduce_to_L0 L0
    by fastforce
next
  case (LN vls lholed nl es' l es'' k lfilledk)
  have 1:"(s, vs, [Label nl es' lfilledk]) \<Down>{(ls, Some n, i)} (s, vs, RReturn vcs)"
    using reduce_to.label_return[OF LN(4)] LN(5)
    by fastforce
  show ?case
    using reduce_to_L0[OF LN(1) 1]
    by fastforce
qed

lemma reduce_to_n_br_lfilled:
  assumes "Lfilled j lholed (($$*vcs) @ [$Br (k+j)]) es"
          "length vcs = n"
          "k < length ls"
          "ls!k = n"
  shows "((s,vs,es) \<Down>{(ls,r,i)} (s,vs,RBreak k vcs))"
  using assms
proof (induction j lholed "(($$*vcs) @ [$Br (k+j)])" es arbitrary: ls k rule: Lfilled.induct)
  case (L0 vls lholed es')
  hence "(s, vs, ($$* vcs) @ [$Br (k)]) \<Down>{(ls, r, i)} (s, vs, RBreak k vcs)"
    using reduce_to.br
    by fastforce
  thus ?case
    using reduce_to_L0 L0
    by fastforce
next
  case (LN vls lholed nl es' l es'' j lfilledk)
  have 0:"(s, vs, lfilledk) \<Down>{(nl#ls, r, i)} (s, vs, RBreak (Suc k) vcs)"
    using LN
    by fastforce
  have 1:"(s, vs, [Label nl es' lfilledk]) \<Down>{(ls, r, i)} (s, vs, RBreak k vcs)"
    using reduce_to.label_break_suc[OF 0]
    by fastforce
  show ?case
    using reduce_to_L0[OF LN(1) 1]
    by fastforce
qed

lemma reduce_to_n_lfilled_context:
  assumes "Lfilled k lholed es les"
          "(s, vs, les) \<Down>{(ls,r,i)} (s', vs', res)"
  shows "\<exists>ls' vcs s'' vs'' res' lholed. ((s, vs, (($$*vcs)@es)) \<Down>{(ls',r,i)} (s'', vs'', res')) \<and>
                                     Lfilled k lholed (($$*vcs)@es) les"
  using assms
proof (induction arbitrary: s' vs' res ls rule: Lfilled.induct)
  case (L0 ves lholed es' es)
  obtain k where k_is:"(s, vs, (ves @ es) @ es') \<Down>k{(ls,r,i)} (s', vs', res)"
    using reduce_to_imp_reduce_to_n[OF L0(3)]
    by fastforce
  have "\<exists>s'' vs'' res'. ((s, vs, ves @ es) \<Down>{(ls,r,i)} (s'', vs'', res'))"
    using reduce_to_n_app[OF k_is]
    by simp (metis reduce_to_n_imp_reduce_to)
  thus ?case
    using Lfilled.L0[of "[]" _ es' "ves @ es"] e_type_const_conv_vs[OF L0(1)]
    by (fastforce simp add: const_list_def)
next
  case (LN ves lholed n es' l es'' k es lfilledk)
  obtain k' where k_is:"((s, vs, (ves @  [Label n es' lfilledk]) @ es'') \<Down>k'{(ls,r,i)} (s', vs', res))"
    using LN reduce_to_imp_reduce_to_n
    by simp blast
  obtain s'' vs'' res' vcs' ls where 1:"((s, vs, ($$*vcs') @ [Label n es' lfilledk]) \<Down>k'{(ls,r,i)} (s'', vs'', res'))"
    using reduce_to_n_app[OF k_is] e_type_const_conv_vs[OF LN(1)]
    by fastforce
  hence "\<exists>ls' s'' vs'' res'. ((s, vs, lfilledk) \<Down>k'{(ls',r,i)} (s'', vs'', res'))"
    using reduce_to_n_label[OF 1(1)]
    by fastforce
  hence "\<exists>ls' vcs s'' vs'' res' lholed.
       ((s, vs, ($$* vcs) @ es) \<Down>{(ls', r, i)} (s'', vs'', res')) \<and>
       Lfilled k lholed (($$* vcs) @ es) lfilledk"
    using LN(4) reduce_to_n_imp_reduce_to
    by fastforce
  thus ?case
    using Lfilled.LN[OF LN(1), of _ n es' _ es'']
    by blast
qed

lemma reduce_to_n_lfilled_context_equiv:
  assumes "Lfilled k lholed es les"
          "Lfilled k lholed es' les'"
          "(s', vs', les') \<Down>{(ls,r,i)} (s_r, vs_r, res)"
          "\<And>s'' vs'' res' ls vcs. ((s', vs', ($$* vcs)@es') \<Down>{(ls,r,i)} (s'', vs'', res')) \<Longrightarrow> ((s, vs, ($$* vcs)@es) \<Down>{(ls,r,i)} (s'', vs'', res'))"
  shows "(s, vs, les) \<Down>{(ls,r,i)} (s_r, vs_r, res)"
  using assms
proof (induction arbitrary: s' vs' res ls es' les' s_r vs_r rule: Lfilled.induct)
  case (L0 vs0 lholed es0 es)
  have les'_is:"les' = vs0 @ es' @ es0"
    using Lfilled.intros(1)[OF L0(1,2)] L0(3) lfilled_deterministic
    by auto
  consider
    (1) s'' vs'' rvs where
      "(s', vs', vs0 @ es') \<Down>{(ls, r, i)} (s'', vs'', RValue rvs)"
      "(s'', vs'', ($$* rvs) @ es0) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
  | (2) "(s', vs', vs0 @ es') \<Down>{(ls, r, i)} (s_r, vs_r, res)"
        "(\<nexists>rvs. res = RValue rvs)"
    using reduce_to_app L0(4) les'_is
    by (metis append_assoc)
  thus ?case
  proof (cases)
    case 1
    show ?thesis
      using reduce_to_seq_value_all[OF L0(5)[OF _] 1(2)] 1(1) L0(1) e_type_const_conv_vs
      by auto
  next
    case 2
    show ?thesis
      using L0(5) 2(1,2) e_type_const_conv_vs
      by (metis L0.hyps(1) append.assoc append_Nil2 reduce_to.seq_nonvalue2)
  qed
next
  case (LN vs_ln lholed n esl_ln lholedk es_ln k es lfilledk)
  obtain lfilledk' where lfilledk'_def:"(les' = vs_ln @ [Label n esl_ln lfilledk'] @ es_ln)"
                                       "const_list vs_ln"
                                       "Lfilled k lholedk es' lfilledk'"
    using Lfilled.simps[of "k+1" lholed es' les'] LN(2,5)
    by fastforce
  have 1: "(s', vs', (vs_ln @ [Label n esl_ln lfilledk']) @ es_ln) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
    using lfilledk'_def(1) LN(6)
    by simp
  obtain vvs_ln where vvs_ln_def:"($$* vvs_ln) = vs_ln"
    using lfilledk'_def(2) e_type_const_conv_vs
    by blast
  consider (a) s'' vs'' rvs where
              "(s', vs', ($$* vvs_ln) @ [Label n esl_ln lfilledk']) \<Down>{(ls, r, i)} (s'', vs'',  RValue rvs)"
              "(s'', vs'', ($$* rvs) @ es_ln) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
         | (b) "(s', vs', ($$* vvs_ln) @ [Label n esl_ln lfilledk']) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
               "(\<nexists>rvs. res = RValue rvs)"
    using reduce_to_app[OF 1] vvs_ln_def
    by blast
  thus ?case
  proof (cases)
    case a
    consider (aa) rvsaa where "(s', vs', lfilledk') \<Down>{(n # ls, r, i)} (s'', vs'', RValue rvsaa)"
                              "RValue rvs = RValue (vvs_ln @ rvsaa)"
      | (bb) rvsbb s''bb vs''bb res'bb vcs1bb vcs2bb where
                    "vvs_ln = vcs1bb @ vcs2bb"
                    "(s', vs', lfilledk') \<Down>{(n # ls, r, i)} (s''bb, vs''bb, RBreak 0 rvsbb)"
                    "(s''bb, vs''bb, ($$* vcs2bb) @ ($$* rvsbb) @ esl_ln) \<Down>{(ls, r, i)} (s'', vs'', res'bb)"
                    "(\<exists>rvs'. res'bb = RValue rvs' \<and>  RValue rvs = RValue (vcs1bb @ rvs'))"
      using reduce_to_label[OF a(1)]
      by fastforce
    hence "(s, vs, ($$* vvs_ln) @ [Label n esl_ln lfilledk]) \<Down>{(ls, r, i)} (s'', vs'', RValue rvs)"
    proof (cases)
      case aa
      show ?thesis
        using LN(4)[OF lfilledk'_def(3) aa(1) LN(7)] aa(2)
        by (simp add: reduce_to.label_value reduce_to_L0_consts_left)
    next
      case bb
      show ?thesis
        using LN(4)[OF lfilledk'_def(3) bb(2) LN(7)] bb(1,3,4)
        by (auto simp add: reduce_to.label_break_nil reduce_to_L0_consts_left)
    qed
    thus ?thesis
      using a(2) reduce_to_seq_value_all vvs_ln_def
      by fastforce
  next
    case b
    consider (aa) "(s', vs', lfilledk') \<Down>{(n # ls, r, i)} (s_r, vs_r, RTrap)"
                  "res = RTrap"
      | (bb) "(\<exists>rvs. ((s', vs', lfilledk') \<Down>{(n # ls, r, i)} (s_r, vs_r, RReturn rvs)) \<and>
                      res = RReturn rvs)"
      | (cc)
        "(\<exists>na rvs. ((s', vs', lfilledk') \<Down>{(n # ls, r, i)} (s_r, vs_r, RBreak (Suc na) rvs)) \<and>
            res = RBreak na rvs)"
      | (dd) rvsdd s''dd vs''dd vcs1dd vcs2dd where
            "vvs_ln = vcs1dd @ vcs2dd"
            "(s', vs', lfilledk') \<Down>{(n # ls, r, i)} (s''dd, vs''dd, RBreak 0 rvsdd)"
            "(s''dd, vs''dd, ($$* vcs2dd) @ ($$* rvsdd) @ esl_ln) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
      using reduce_to_label[OF b(1)] b(2)
      by fastforce
    hence "(s, vs, ($$* vvs_ln) @ [Label n esl_ln lfilledk]) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
    proof (cases)
      case aa
      show ?thesis
        using LN(4)[OF lfilledk'_def(3) aa(1) LN(7)] aa(2)
        by (simp add: reduce_to.label_trap reduce_to_L0_consts_left_trap)
    next
      case bb
      show ?thesis
        using LN(4)[OF lfilledk'_def(3) _ LN(7), of s' vs'] bb
              lfilledk'_def(2) reduce_to.label_return reduce_to.seq_nonvalue1 vvs_ln_def
        by fastforce
    next
      case cc
      show ?thesis
        using LN(4)[OF lfilledk'_def(3) _ LN(7), of s' vs'] cc
              lfilledk'_def(2) reduce_to.label_break_suc reduce_to.seq_nonvalue1 vvs_ln_def
        by fastforce
    next
      case dd
      have 1:"(s''dd, vs''dd, ($$* vcs2dd @ rvsdd) @ esl_ln) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
        using dd(3)
        by simp
      have 2:"(s, vs, ($$* vcs2dd) @  [Label n esl_ln lfilledk]) \<Down>{(ls, r, i)} (s_r, vs_r, res)"
        using reduce_to.label_break_nil[OF LN(4)[OF lfilledk'_def(3) dd(2) LN(7)] 1]
        by simp
      thus ?thesis
        using reduce_to.seq_nonvalue1[OF _ 2 b(2), of "($$* vcs1dd)"] dd(1) vvs_ln_def is_const_list
        by force
    qed
    thus ?thesis
      by (metis append_Nil2 append_assoc b(2) reduce_to.seq_nonvalue2 vvs_ln_def)
  qed
qed

lemma reduce_to_app_reduce_simple:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
          "((s,vs,($$*vcsf)@es') \<Down>{(ls,r,i)} (s',vs',res))"
  shows "((s,vs,($$*vcsf)@es) \<Down>{(ls,r,i)} (s',vs',res))"
  using assms
proof (induction arbitrary: ls r res vs' s' vcsf rule: reduce_simple.induct)
  case (unop v t op)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.unop]
          reduce_to_consts[of _ _ "vcsf@[app_unop op v]"]
    by fastforce
next
  case (binop_Some op v1 v2 v t)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.binop_Some]
          reduce_to_consts[of _ _ "vcsf@[v]"]
    by fastforce
next
  case (binop_None op v1 v2 t)
  thus ?case
    using reduce_to_L0_consts_left_trap[OF reduce_to.binop_None]
          reduce_to_trap[of s vs "(ls, r, i)"] reduce_to_trap_L0_left
    by metis
next
  case (testop v t op)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.testop]
          reduce_to_consts[of _ _ "vcsf@[app_testop op v]"]
    by fastforce
next
  case (relop v1 v2 t op)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.relop]
          reduce_to_consts[of _ _ "vcsf@[app_relop op v1 v2]"]
    by fastforce
next
  case (convert_Some t1 v t2 sx v')
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.convert_Some]
          reduce_to_consts[of _ _ "vcsf@[v']"]
    by fastforce
next
  case (convert_None t1 v t2 sx)
  thus ?case
    using reduce_to_L0_consts_left_trap[OF reduce_to.convert_None]
          reduce_to_trap[of s vs "(ls, r, i)"] reduce_to_trap_L0_left
    by metis
next
  case (reinterpret t1 v t2)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.reinterpret]
          reduce_to_consts[of _ _ "vcsf@[wasm_deserialise (bits v) t2]"]
    by fastforce
next
  case unreachable
  thus ?case
    using reduce_to_L0_consts_left_trap[OF reduce_to.unreachable]
          reduce_to_trap[of s vs "(ls, r, i)"] reduce_to_trap_L0_left
    by metis
next
  case nop
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.nop]
          reduce_to_consts[of _ _ "vcsf@[]"]
    by fastforce
next
  case (drop v)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.drop]
          reduce_to_consts[of _ _ "vcsf@[]"]
    by fastforce
next
  case (select_false n v1 v2)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.select_false]
          reduce_to_consts[of _ _ "vcsf@[v2]"]
    by fastforce
next
  case (select_true n v1 v2)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.select_true]
          reduce_to_consts[of _ _ "vcsf@[v1]"]
    by fastforce
next
  case (block vls n t1s t2s m es)
  thus ?case
    using reduce_to_label_emp1[OF block(5)]
    apply (cases res)
    apply simp_all
    apply (metis reduce_to.block reduce_to_L0_consts_left)
    apply (metis append_is_Nil_conv is_const_list not_Cons_self2 reduce_to.block reduce_to.seq_nonvalue1 res_b.distinct(1) self_append_conv2)
    apply (metis append_is_Nil_conv is_const_list not_Cons_self2 reduce_to.block reduce_to.seq_nonvalue1 res_b.distinct(3) self_append_conv2)
    apply (metis reduce_to.block reduce_to_L0_consts_left_trap)
    done
next
  case (loop vs n t1s t2s m es)
  thus ?case
    using reduce_to_label_loop2[OF loop(5)]
    apply (cases res)
       apply simp_all
    apply (metis reduce_to.loop reduce_to_L0_consts_left)
    apply (metis append_is_Nil_conv is_const_list not_Cons_self2 reduce_to.loop reduce_to.seq_nonvalue1 res_b.distinct(1) self_append_conv2)
    apply (metis append_is_Nil_conv is_const_list not_Cons_self2 reduce_to.loop reduce_to.seq_nonvalue1 res_b.distinct(3) self_append_conv2)
    apply (metis reduce_to.loop reduce_to_L0_consts_left_trap)
    done
next
  case (if_false n tf e1s e2s)
  thus ?case
    using reduce_to.if_false[OF if_false(1)_ if_false(2)]
    by (fastforce simp add: is_const_list)
next
  case (if_true n tf e1s e2s)
  thus ?case
    using reduce_to.if_true[OF if_true(1)_ if_true(2)]
    by (fastforce simp add: is_const_list)
next
  case (label_const ves n es)
  obtain vcs where vcs_def:"ves = $$*vcs"
    using label_const(1) e_type_const_conv_vs
    by auto
  hence 0:"res = RValue (vcsf@vcs)"
    using label_const(2)
    apply simp
    apply (metis map_append reduce_to_imp_reduce_to_n reduce_to_n_consts)
    done
  have 1:"(s, vs, ves) \<Down>{(n#ls, r, i)} (s', vs', RValue vcs)"
    using vcs_def
    by (metis label_const.prems map_append reduce_to_consts1 reduce_to_imp_reduce_to_n reduce_to_n_consts)
  show ?case
    using reduce_to_L0_consts_left[OF reduce_to.label_value[OF 1]] 0
    by simp
next
  case (label_trap n es)
  thus ?case
    using reduce_to_L0_consts_left_trap[OF reduce_to.label_trap]
          reduce_to_trap[of s vs "(ls, r, i)"] reduce_to_trap_L0_left
    by (metis reduce_to.trap)
next
  case (br vs n i lholed LI es)
  obtain vcs where vcs_def:"Lfilled i lholed (($$*vcs) @ [$Br (0 + i)]) LI"
                           "vs = $$*vcs"
                           "length vcs = n"
    using br(1,2,3) e_type_const_conv_vs
    by fastforce
  thus ?case
    using reduce_to.label_break_nil[OF reduce_to_n_br_lfilled[OF vcs_def(1,3)]] br.prems
    by auto
next
  case (br_if_false n i)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.br_if_false]
          reduce_to_consts[of _ _ "vcsf@[]"]
    by fastforce
next
  case (br_if_true n i)
  thus ?case
    using reduce_to.br_if_true[OF br_if_true(1)_ br_if_true(2)]
    by (fastforce simp add: is_const_list)
next
  case (br_table "is" c i)
  thus ?case
    using reduce_to.br_table[OF br_table(1)_ br_table(2)]
    by (fastforce simp add: is_const_list)
next
  case (br_table_length "is" c i)
  thus ?case
    using reduce_to.br_table_length[OF br_table_length(1)_ br_table_length(2)]
    by (fastforce simp add: is_const_list)
next
  case (local_const es n i vls)
  obtain vcs where vcs_def:"es = $$*vcs"
    using local_const(1) e_type_const_conv_vs
    by fastforce
  hence 0:"res = RValue (vcsf@vcs) \<and> s = s' \<and> vs = vs'"
    using local_const(2)
    apply simp
    apply (metis map_append reduce_to_imp_reduce_to_n reduce_to_n_consts)
    done
  have 1:"(s, vls, es) \<Down>{([], Some n, i)} (s', vls, RValue vcs)"
    using vcs_def 0
    by (simp add: reduce_to_consts1)
  show ?case
    using reduce_to_L0_consts_left[OF reduce_to.local_value[OF 1]] 0
    by simp
next
  case (local_trap n i vls)
  thus ?case
    using reduce_to_L0_consts_left_trap[OF reduce_to.local_trap]
          reduce_to_trap[of s vs "(ls, r, i)"] reduce_to_trap_L0_left
    by (metis reduce_to.trap reduce_to_trap)
next
  case (return ves j n lholed es i' vls)
  obtain vcs where vcs_def:"($$* vcs) = ves"
    using return(1) e_type_const_conv_vs
    by blast
  hence 1:"vs = vs'" "s = s'" "res = RValue (vcsf@vcs)" 
    using return reduce_to_consts
    by (metis map_append)+
  have "(s, vls, es) \<Down>{([], Some j, i')} (s, vls, RReturn vcs)"
    using reduce_to_n_return_lfilled vcs_def return
    by fastforce
  thus ?case
    using 1 reduce_to.local_return
    by (simp add: reduce_to_L0_consts_left)
next
  case (tee_local v j)
  obtain k where k_is:"((s, vs, ($$* vcsf) @  [v, v, $Set_local j]) \<Down>k{(ls, r, i)} (s', vs', res))"
    using tee_local(2) reduce_to_imp_reduce_to_n
    by blast
  obtain c where c_is:"v = $C c"
    using tee_local(1)
    by (metis e_type_const_unwrap)
  hence 0:"((s, vs, ($$* vcsf@[c]) @  [$C c, $Set_local j]) \<Down>k{(ls, r, i)} (s', vs', res))"
    using k_is c_is
    by auto
  have 1:"s = s'" "vs[j := c] = vs'" "j < length vs" "res = RValue (vcsf@[c])"
    using reduce_to_n_set_local[OF 0]
    by auto
  hence "((s, vs, [v, v, $Set_local j]) \<Down>{(ls, r, i)} (s', vs', RValue [c]))"
    using 
          upd_conv_take_nth_drop[OF 1(3)] c_is id_take_nth_drop[OF 1(3)] c_is
          reduce_to.const_value[OF reduce_to.set_local[of "take j vs" j s "vs!j" "drop (Suc j) vs" c "(ls, r, i)"], of "[c]"]
    by simp
  thus ?case
    using reduce_to.tee_local k_is c_is reduce_to.const_value 1(4) reduce_to_L0_consts_left tee_local
    by auto
next
  case (trap es lholed)
  then obtain ves es_c where es_is:"es = ves @ [Trap] @ es_c"
                                   "const_list ves"
                                   "lholed = LBase ves es_c"
    using Lfilled.simps[of 0 lholed "[Trap]" es]
    by simp blast
  have s_is:"s = s'" "vs = vs'" "res = RTrap"
    using trap(3) reduce_to_trap[of s vs "(ls, r, i)" s' vs' res] reduce_to_trap_L0_left
    by auto
  have "ves \<noteq> [] \<or> es_c \<noteq> []"
    using trap(1) es_is
    by auto
  thus ?case
    using s_is es_is
    apply simp
    apply (metis es_is(1,2) e_type_const_conv_vs reduce_to.seq_nonvalue2 reduce_to_L0_consts_left_trap reduce_to_trap_L0_left res_b.distinct(5) trap.prems)
    done
qed

lemma reduce_to_app_reduce:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
          "((s',vs',($$*vcsf)@es') \<Down>{(ls,r,i)} (s'',vs'',res))"
  shows "((s,vs,($$*vcsf)@es) \<Down>{(ls,r,i)} (s'',vs'',res))"
  using assms
proof (induction arbitrary: ls r res vs'' s'' vcsf rule: reduce.induct)
  case (basic e e' s vs i)
  thus ?case
    using reduce_to_app_reduce_simple
    by auto
next
  case (call s vs j i)
  thus ?case
    using reduce_to_call
    by fastforce
next
  case (call_indirect_Some s i c cl j tf vs)
  thus ?case
    using reduce_to.call_indirect_Some[OF call_indirect_Some(1,2,3), of "$$*vcsf"]
    by (fastforce simp add: is_const_list)
next
  case (call_indirect_None s i c cl j vs)
  thus ?case
    using reduce_to.call_indirect_None reduce_to_trap[of s vs "(ls, r, i)"]
    by (metis reduce_to_L0_consts_left_trap reduce_to_trap_L0_left)
next
  case (invoke_native cl j t1s t2s ts es ves vcs n k m zs s vs i)
  thus ?case
  proof (cases "\<exists>rvs. res = RValue rvs")
    case True
    obtain rvs' where rvs'_def:"res = RValue rvs'"
      using True
      by blast
    hence 0:"(\<exists>rvs2.
             rvs' = vcsf @ rvs2 \<and>
             (s, vs,
              [Local m j (vcs @ zs)
                [$Block ([] _> t2s)
                   es]]) \<Down>{(ls, r,
   i)} (s'', vs'', RValue rvs2))"
      using reduce_to_local[OF invoke_native(8)]
            True
      by fastforce
    thus ?thesis
      using rvs'_def reduce_to.invoke_native[OF invoke_native(1,2,3,4,5,6,7)]
      apply simp
      apply (metis reduce_to_L0_consts_left)
      done
  next
    case False
    have 0:"(s, vs, ves @ [Invoke cl]) \<Down>{(ls, r, i)} (s'', vs'', res)"
      using reduce_to.invoke_native[OF invoke_native(1,2,3,4,5,6,7)] reduce_to_local[OF invoke_native(8)]
            False
      by blast
    thus ?thesis
      using reduce_to.seq_nonvalue1[OF _ 0 False] is_const_list const_list_def
      apply (cases vcsf)
      apply simp_all
      apply fastforce
      done
  qed

next
  case (invoke_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs i)
  thus ?case
    using reduce_to.invoke_host_Some reduce_to_consts[of s' "vs" "vcsf@vcs'"]
    apply simp
    apply (metis reduce_to_L0_consts_left)
    done
next
  case (invoke_host_None cl t1s t2s f ves vcs n m s vs i)
  thus ?case
    using reduce_to.invoke_host_None reduce_to_trap[of s vs "(ls, r, i)"]
    by (metis reduce_to_L0_consts_left_trap reduce_to_trap_L0_left)
next
  case (get_local vi j s v vs i)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.get_local]
          reduce_to_consts[of _ "(vi @ [v] @ vs)" "vcsf@[v]"]
    by fastforce
next
  case (set_local vi j s v vs v' i)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.set_local]
          reduce_to_consts[of _ "(vi @ [v'] @ vs)" "vcsf@[]"]
    by fastforce
next
  case (get_global s vs j i)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.get_global]
          reduce_to_consts[of _ vs "vcsf@[sglob_val s i j]"]
    by fastforce
next
  case (set_global s i j v s' vs)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.set_global]
          reduce_to_consts[of _ vs "vcsf@[]"]
    by fastforce
next
  case (load_Some s i j m k off t bs vs a)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.load_Some]
          reduce_to_consts[of _ vs "vcsf@[wasm_deserialise bs t]"]
    by fastforce
next
  case (load_None s i j m k off t vs a)
  thus ?case
    using reduce_to.load_None reduce_to_trap[of s vs "(ls, r, i)"]
    by (metis reduce_to_L0_consts_left_trap reduce_to_trap_L0_left)
next
  case (load_packed_Some s i j m sx k off tp t bs vs a)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.load_packed_Some]
          reduce_to_consts[of _ vs "vcsf@[wasm_deserialise bs t]"]
    by fastforce
next
  case (load_packed_None s i j m sx k off tp t vs a)
  thus ?case
    using reduce_to.load_packed_None reduce_to_trap[of s vs "(ls, r, i)"]
    by (metis reduce_to_L0_consts_left_trap reduce_to_trap_L0_left)
next
  case (store_Some t v s i j m k off mem' vs a)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.store_Some]
          reduce_to_consts[of _ vs "vcsf@[]"]
    by fastforce
next
  case (store_None t v s i j m k off vs a)
  thus ?case
    using reduce_to.store_None reduce_to_trap[of s vs "(ls, r, i)"]
    by (metis reduce_to_L0_consts_left_trap reduce_to_trap_L0_left)
next
  case (store_packed_Some t v s i j m k off tp mem' vs a)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.store_packed_Some]
          reduce_to_consts[of _ vs "vcsf@[]"]
    by fastforce
next
  case (store_packed_None t v s i j m k off tp vs a)
  thus ?case
    using reduce_to.store_packed_None reduce_to_trap[of s vs "(ls, r, i)"]
    by (metis reduce_to_L0_consts_left_trap reduce_to_trap_L0_left)
next
  case (current_memory s i j m n vs)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.current_memory]
          reduce_to_consts[of _ vs "vcsf@[ConstInt32 (Wasm_Base_Defs.int_of_nat n)]"]
    by fastforce
next
  case (grow_memory s i j m n c mem' vs)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.grow_memory]
          reduce_to_consts[of _ vs "vcsf@[ConstInt32 (Wasm_Base_Defs.int_of_nat n)]"]
    by fastforce
next
  case (grow_memory_fail s i j m n vs c)
  thus ?case
    using reduce_to_L0_consts_left[OF reduce_to.grow_memory_fail]
          reduce_to_consts[of _ vs "vcsf@[ConstInt32 int32_minus_one]"]
    by fastforce
next
  case (label s vs es i s' vs' es' k lholed les les')
  obtain lholed' where lholed':"Lfilled k lholed' es (($$* vcsf)@les)"
                               "Lfilled k lholed' es' (($$* vcsf) @ les')"
    using lfilled_lfilled_app[OF label(2,3)]
    by blast
  thus ?case
    using reduce_to_n_lfilled_context_equiv[OF lholed' label(5,4)]
    by blast
next
  case (local s vs es i s_l lvs es' v0s n j)
  obtain k where res_b_def:"((s_l, v0s, ($$* vcsf) @ [Local n i lvs es']) \<Down>k{(ls, r, j)} (s'', vs'', res))"
    using local(3) reduce_to_imp_reduce_to_n
    by blast
  then obtain lvs' lres where lres_def:"(s_l, lvs, ($$*[])@es') \<Down>{([], Some n, i)} (s'', lvs', lres)"
                                       "v0s = vs''"
                                       "(lres = RTrap \<and> res = RTrap \<or>
                                        (\<exists>rvs. (lres = RValue rvs \<or>
                                                lres = RReturn rvs) \<and>
                                               res = RValue (vcsf @ rvs)))"
    using local_imp_body[OF res_b_def(1)] reduce_to_n_imp_reduce_to
    by fastforce
  show ?case
  proof (cases lres)
    case (RValue x1)
    thus ?thesis
      using local(2)[OF lres_def(1)] lres_def(2,3) reduce_to.local_value
      by (metis (no_types, lifting) map_append reduce_to_L0_consts_left res_b.distinct(3,5) self_append_conv2)
  next
    case (RBreak x21 x22)
    thus ?thesis
      using lres_def(3)
      by simp
  next
  case (RReturn x3)
    thus ?thesis
      using local(2)[OF lres_def(1)] lres_def(2,3) reduce_to.local_return
      by (metis (no_types, lifting) map_append reduce_to_L0_consts_left res_b.distinct(11,3) self_append_conv2)
  next
    case RTrap
    thus ?thesis
      using local(2)[OF lres_def(1)] lres_def(2,3) reduce_to.local_trap
      by (metis (no_types, lifting) map_append reduce_to_L0_consts_left_trap res_b.distinct(11,5) self_append_conv2)
  qed
qed

definition res_agree :: "e list \<Rightarrow> res_b \<Rightarrow> bool" where
  "res_agree res res_b \<equiv> (\<exists>rvs. (res = ($$* rvs) \<and> res_b = RValue rvs)) \<or>
                         (res = [Trap] \<and> res_b = RTrap)"

lemma reduce_trans_imp_reduce_to:
  assumes "reduce_trans i (s,vs,es) (s',vs',res)"
          "(res = [Trap] \<or> (\<exists>rvs. res = $$* rvs))"
  shows "\<exists>res_b. ((s,vs,es) \<Down>{(ls,r,i)} (s',vs',res_b)) \<and> res_agree res res_b"
  using assms
  unfolding reduce_trans_def
proof (induction "(s,vs,es)" arbitrary: s vs es rule: converse_rtranclp_induct)
case base
  thus ?case
    apply safe
    apply (fastforce intro: reduce_to.trap simp add: res_agree_def)
    apply (fastforce intro: reduce_to_n_imp_reduce_to[OF reduce_to_n_consts1] simp add: res_agree_def)
    done
next
  case (step z)
  obtain s'' vs'' es'' where z_def:"z = (s'',vs'',es'')"
    apply (cases z)
    apply blast
    done
  have "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s'';vs'';es''\<rparr>"
    using step(1) z_def
    by simp
  moreover
  have "(\<lambda>(s, vs, es) (s', x, y). \<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';x;y\<rparr>)\<^sup>*\<^sup>* (s'',vs'',es'') (s', vs', res)"
    using step(2) z_def
    by simp
  have "\<exists>res_b. ((s'',vs'',es'') \<Down>{(ls, r, i)} (s', vs', res_b)) \<and> res_agree res res_b"
    using step(3,4) z_def
    by simp
  ultimately
  show ?case
    using reduce_to_app_reduce[of _ _ _ _ _ _ _ "[]"]
    by fastforce
qed

lemma reduce_trans_equiv_reduce_to_trap:
  shows "reduce_trans i (s,vs,es) (s',vs',[Trap]) = ((s,vs,es) \<Down>{([],None,i)} (s',vs',RTrap))"
  using reduce_trans_imp_reduce_to reduce_to_imp_reduce_trans
  unfolding res_agree_def
  apply simp
  apply safe
  apply blast
  apply blast
  done

lemma reduce_trans_equiv_reduce_to_consts:
  shows "reduce_trans i (s,vs,es) (s',vs',$$* vcs) = ((s,vs,es) \<Down>{([],None,i)} (s',vs',RValue vcs))"
proof -
  {
    assume local_assms:"(s, vs, es) \<Down>{([], None, i)} (s', vs', RValue vcs)"
    have "reduce_trans i (s, vs, es) (s', vs', $$* vcs)"
      using reduce_to_imp_reduce_trans[OF local_assms]
      by fastforce
  }
  thus ?thesis
  using reduce_trans_imp_reduce_to inj_basic_econst
  unfolding res_agree_def
  by fastforce
qed

theorem reduce_trans_equiv_reduce_to:
  assumes "res_agree res res_b"
  shows "reduce_trans i (s,vs,es) (s',vs',res) = ((s,vs,es) \<Down>{([],None,i)} (s',vs',res_b))"
  using assms reduce_trans_equiv_reduce_to_trap reduce_trans_equiv_reduce_to_consts
  unfolding res_agree_def
  by metis
end
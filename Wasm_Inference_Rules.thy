theory Wasm_Inference_Rules imports Wasm_Assertions_Shallow begin

definition var_st_differ_on :: "'a var_st \<Rightarrow> var set \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "var_st_differ_on v_st vars v_st' \<equiv> (\<forall>var. var \<notin> vars \<longrightarrow> var_st_agree v_st var v_st')"

lemma var_st_ex:
  assumes "(\<forall>gn<length (inst.globs i). inst.globs i ! gn < length (s.globs s))"
  shows "\<exists>var_st. reifies_glob (s.globs s) (inst.globs i) var_st \<and> reifies_loc vs var_st \<and> snd (snd var_st) = lvar_st"
  using assms
  unfolding reifies_glob_def reifies_loc_def
  by simp (metis (full_types) length_map nth_map)

lemma var_st_eq_intro1:
  assumes "reifies_glob (s.globs s) (inst.globs i) var_st"
          "reifies_loc vs var_st"
          "snd (snd var_st) = lvar_st"
          "reifies_glob (s.globs s) (inst.globs i) var_st'"
          "reifies_loc vs var_st'"
          "snd (snd var_st') = lvar_st"
  shows "var_st = var_st'"
  using assms
proof -
  have f1: "length (fst var_st') = length (inst.globs i)"
    by (meson assms(4) reifies_glob_def)
  have f2: "length (fst var_st) = length (inst.globs i)"
    by (meson assms(1) reifies_glob_def)
  then have "\<And>n. \<not> n < length (inst.globs i) \<or> fst var_st' ! n = fst var_st ! n"
    using f1 by (metis assms(1,4) reifies_glob_def)
  then show ?thesis
    using f2 f1 by (metis (no_types) assms(2,3,5,6) nth_equalityI prod.collapse reifies_loc_def)
qed

lemma var_st_eq_intro2:
  assumes "reifies_glob (s.globs s) (inst.globs i) var_st"
          "reifies_loc vs var_st"
          "snd (snd var_st) = lvar_st"
          "reifies_glob (s.globs (s\<lparr>s.mem := mem'\<rparr>)) (inst.globs i) var_st'"
          "reifies_loc vs var_st'"
          "snd (snd var_st') = lvar_st"
  shows "var_st = var_st'"
  using assms
proof -
  have f1: "length (fst var_st') = length (inst.globs i)"
    by (meson assms(4) reifies_glob_def)
  have f2: "length (fst var_st) = length (inst.globs i)"
    by (meson assms(1) reifies_glob_def)
  then have "\<And>n. \<not> n < length (inst.globs i) \<or> fst var_st' ! n = fst var_st ! n"
    using f1 assms(1,4)
    unfolding reifies_glob_def
    by auto
  then show ?thesis
    using f2 f1 by (metis (no_types) assms(2,3,5,6) nth_equalityI prod.collapse reifies_loc_def)
qed

lemma var_st_differ_on_refl: "var_st_differ_on v_st vars v_st"
  unfolding var_st_differ_on_def var_st_agree_def
  by (auto split: var.splits)

lemma var_st_differ_on_subset:
  assumes "var_st_differ_on v_st vars v_st'"
          "vars \<subseteq> vars'"
  shows "var_st_differ_on v_st vars' v_st'"
  unfolding var_st_differ_on_def
  by (metis assms(1) assms(2) contra_subsetD var_st_differ_on_def)

lemma var_st_differ_on_emp:
  assumes "var_st_differ_on v_st {} v_st'"
  shows "v_st = v_st'"
  using assms
  unfolding var_st_differ_on_def var_st_agree_def var_st_get_global_def var_st_get_local_def
            var_st_get_lvar_def
  apply (cases v_st)
  apply (cases v_st')
  apply (simp split: var.splits if_splits)
  apply safe
    apply (metis less_irrefl neqE nth_equalityI)
  apply (metis less_irrefl neqE nth_equalityI)
  apply auto
  done

definition stack_ass_ind_on :: "'a stack_ass \<Rightarrow> var set \<Rightarrow> bool" where
  "stack_ass_ind_on St vars \<equiv> \<forall>vs v_st v_st'. var_st_differ_on v_st vars v_st' \<longrightarrow> stack_ass_sat St vs v_st = stack_ass_sat St vs v_st'"

definition heap_ass_ind_on :: "'a heap_ass \<Rightarrow> var set \<Rightarrow> bool" where
  "heap_ass_ind_on H vars \<equiv> \<forall>h v_st v_st'. var_st_differ_on v_st vars v_st' \<longrightarrow> H h v_st = H h v_st'"

context encapsulated_module
begin

inductive modifies :: "cl list \<Rightarrow> e list \<Rightarrow> var \<Rightarrow> bool" where
"\<lbrakk>(modifies fs [e] v) \<or> (modifies fs es v)\<rbrakk> \<Longrightarrow> modifies fs (e#es) v"
| "modifies fs [$Set_local j] (Lc j)"
| "\<lbrakk>modifies fs [$Set_local j] v\<rbrakk> \<Longrightarrow> modifies fs [$Tee_local j] v"
| "modifies fs [$Set_global j] (Gl j)"
| "\<lbrakk>j \<ge> length (inst.globs i)\<rbrakk> \<Longrightarrow> modifies fs [$Set_global j] (Gl j)"
| "\<lbrakk>(modifies fs [Label _ [] ($* b_es)] v)\<rbrakk> \<Longrightarrow> modifies fs [$Block _ b_es] v"
| "\<lbrakk>(modifies fs ($* b_es) v)\<rbrakk> \<Longrightarrow> modifies fs [$Loop tf b_es] v"
| "\<lbrakk>(modifies fs [$Block _ b_es1] v) \<or> (modifies fs [$Block _ b_es2] v)\<rbrakk> \<Longrightarrow> modifies fs [$If _ b_es1 b_es2] v"
| "\<lbrakk>(modifies fs [Callcl (fs!j)] v)\<rbrakk> \<Longrightarrow> modifies fs [$Call j] v"
| "\<lbrakk>j \<ge> length fs\<rbrakk> \<Longrightarrow> modifies fs [$Call j] v"
| "\<lbrakk>(modifies fs les v) \<or> (modifies fs es v)\<rbrakk> \<Longrightarrow> modifies fs [Label _ les es] v"
| "\<lbrakk>(modifies fs es v)\<rbrakk> \<Longrightarrow> modifies fs [Local _ i lvs es] v"
| "\<lbrakk>j \<noteq> i\<rbrakk> \<Longrightarrow> modifies fs [Local _ j lvs es] v"
| "\<lbrakk>cl = Func_native j _ _ b_es; (modifies fs [Local _ j _ [$Block _ b_es]] v)\<rbrakk> \<Longrightarrow> modifies fs [Callcl cl] v"
| "\<lbrakk>cl = Func_host _ _\<rbrakk> \<Longrightarrow> modifies fs [Callcl cl] v"
| "modifies fs [$Call_indirect k] v"



definition modset where "modset cls es = {v. modifies cls es v}"

lemma modifies_modset_eq [pred_set_conv]: "modifies cl es = (\<lambda>v. v \<in> modset cl es)"
by(simp add: modset_def)

lemmas modset_intros [intro?] = modifies.intros[to_set]
lemmas modset_induct [consumes 1, induct set: modset] = modifies.induct[to_set]
lemmas modset_cases [consumes 1, cases set: modset] = modifies.cases[to_set]
lemmas modset_simps = modifies.simps[to_set]

lemma modset_consts:
  assumes "x \<in> modset fs ($$*vs)"
  shows "False"
  using assms
proof (induction fs "($$*vs)" x arbitrary: vs rule: modset_induct)
  case (1 fs e v es)
  thus ?case
    using consts_app_ex[of "[e]" "es"]
    by (metis append_Nil append_eq_Cons_conv)
qed auto

lemma modset_emp:
  assumes "x \<in> modset fs []"
  shows "False"
  using assms modset_consts[of x fs "[]"]
  by auto

lemma modset_cons:
  assumes "m \<in> modset fs es"
          "es = e1#es2"
  shows "m \<in> modset fs [e1] \<or> m \<in> modset fs es2"
  using assms
  by (induction rule: modset_induct) (auto intro: modset_intros)

lemma modset_arb_app1:
  assumes "m \<in> modset fs es"
          "es = es1@es2"
  shows "m \<in> modset fs es1 \<or> m \<in> modset fs es2"
  using assms
proof (induction es1 arbitrary: es es2)
  case Nil
  thus ?case
    by simp
next
  case (Cons e es1)
  hence "m \<in> modset fs [e] \<or> m \<in> modset fs (es1@es2)"
    using modset_cons
    by fastforce
  thus ?case
    using Cons modset_intros(1) 
    by blast
qed

lemma modset_arb_app:
  assumes "m \<in> modset fs es1 \<or> m \<in> modset fs es2"
  shows "m \<in> modset fs (es1@es2)"
  using assms
proof (induction es1)
  case Nil
  thus ?case
    using modset_emp
    by fastforce
next
  case (Cons a es1)
  thus ?case
    by (metis append_Cons modset_intros(1) modset_cons)
qed

lemma modset_consts_app:
  "(m \<in> modset fs (($$*vs)@es)) = (m \<in> modset fs es)"
  using modset_arb_app modset_arb_app1 modset_consts
  by blast

lemma modset_consts_app_equiv:
  "(modset fs (($$*vs)@es)) = (modset fs es)"
  using modset_arb_app modset_arb_app1 modset_consts
  by blast

lemma modset_call:
  assumes "j \<ge> length fs"
  shows "modset fs [$Call j] = UNIV"
  using assms modset_intros(10)
  by blast

lemma modset_call_indirect:
  shows "modset fs [$Call_indirect j] = UNIV"
  using modset_intros(16)
  by blast

lemma modset_label:
  assumes "v \<in> modset fs [Label n les es]"
  shows "v \<in> modset fs les \<or> v \<in> modset fs es"
  using assms
  apply (induction fs "[Label n les es]" v rule: modset_induct)
   apply (auto dest: modset_emp)
  done

lemma modset_label_inner:
  "(v \<in> modset fs [Label n les (($$*ves)@es)]) = (v \<in> modset fs [Label n les es])"
  using modset_label modset_consts_app modset_intros(11)
  by blast

lemma modset_block1:
  assumes "v \<in> modset fs [$Block tf b_es]"
  shows "v \<in> modset fs [Label n [] ($*b_es)]"
  using assms
  apply (induction fs "[$Block tf b_es]" v rule: modset_induct)
   apply (auto dest: modset_label simp add: modset_intros(11))
  done

lemma modset_block:
  "v \<in> modset fs [$Block tf b_es] = (v \<in> modset fs [Label n [] ($*b_es)])"
  using modset_block1 modset_intros(6)
  by blast

lemma modset_loop1:
  assumes "v \<in> modset fs [$Loop tf b_es]"
  shows "v \<in> modset fs ($*b_es)"
  using assms
  apply (induction fs "[$Loop tf b_es]" v rule: modset_induct)
   apply (auto dest: modset_emp)
  done

lemma modset_loop:
  "v \<in> modset fs [$Loop tf b_es] = (v \<in> modset fs ($*b_es))"
  using modset_loop1 modset_intros(7)
  by blast

lemma modset_tee_local1:
  assumes "v \<in> modset fs [$Tee_local j]"
  shows "v \<in> modset fs [$Set_local j]"
  using assms
  apply (induction fs "[$Tee_local j]" v rule: modset_induct)
   apply (auto dest: modset_emp)
  done

lemma modset_tee_local:
  "v \<in> modset fs [$Tee_local j] = (v \<in> modset fs [$Set_local j])"
  using modset_tee_local1 modset_intros(3)
  by blast

lemma modset_if1:
  assumes "v \<in> modset fs [$If tf b_es1 b_es2]"
  shows "v \<in> modset fs [$Block tf1 b_es1] \<or> (v \<in> modset fs [$Block tf2 b_es2])"
  using assms
  apply (induction fs "[$If tf b_es1 b_es2]" v rule: modset_induct)
  apply (metis modset_emp)
  apply (metis modset_block) 
  done

lemma modset_if:
  "v \<in> modset fs [$If tf b_es1 b_es2] = (v \<in> modset fs [$Block tf1 b_es1] \<or> v \<in> modset fs [$Block tf2 b_es2])"
  using modset_if1 modset_intros(8)
  by blast

lemma modset_if_1:
  "modset fs [$Block tf1 b_es1] \<subseteq> modset fs [$If tf b_es1 b_es2]"
  using modset_if1 modset_intros(8)
  by blast

lemma modset_if_2:
  "modset fs [$Block tf2 b_es2] \<subseteq> modset fs [$If tf b_es1 b_es2]"
  using modset_if1 modset_intros(8)
  by blast

lemma modset_implies:
  assumes "\<And>x. x \<in> modset fs es \<Longrightarrow> x \<in> modset fs es'"
  shows "modset fs es \<subseteq> modset fs es'"
  using assms
  by auto

lemma modset_call1:
  assumes "reifies_func (s.funcs s) (inst.funcs i) fs"
          "x \<in> modset fs ([Callcl (sfunc s i j)])"
  shows "x \<in> modset fs ([$Call j])"
  using reifies_func_ind[OF assms(1)] modset_call assms(2) modset_intros(9)
  apply (cases "j < length fs")
   apply auto
  done

lemma modset_br1:  "x \<in> modset fs ([$Br j]) \<Longrightarrow> False"
  apply (induction "[$Br j]" x rule: modset_induct)
  apply (auto dest: modset_emp)
  done

lemma modset_br: "modset fs ([$Br j]) = {}"
  using modset_br1
  by auto

lemma modset_local:
  assumes "v \<in> modset fs [Local m i vls es]"
  shows "v \<in> modset fs es"
  using assms
  apply (induction fs "[Local m i vls es]" v rule: modset_induct)
  apply (auto dest: modset_emp)
  done

lemma modset_callcl_native1:
  assumes "v \<in> modset fs [Callcl cl]"
          "cl = Func_native j tf ts b_es"
  shows "v \<in> modset fs [Local m j vls [$Block tf' b_es]]"
  using assms
proof (induction fs "[Callcl cl]" v arbitrary: rule: modset_induct)
  case (14 j' vc vd b_es' fs ve vf vg v)
  hence j'_def:"j = j'"
               "b_es = b_es'"
    by auto
  thus ?case
  proof (cases "j = i")
    case True
    thus ?thesis
      using modset_local j'_def 14(2)
      by (metis encapsulated_module.modset_block modset_intros(12))
  next
    case False
      thus ?thesis
        using modset_intros(13)
        by blast
  qed
qed (auto dest: modset_emp)

lemma modset_callcl_native:
  assumes "cl = Func_native j tf ts b_es"    
  shows "modset fs [Local m j vls [$Block tf' b_es]] = modset fs [Callcl cl]"
  using assms modset_callcl_native1 modset_intros(14)
  by blast

lemma var_st_differ_on_subset_const_list_helper:
  assumes "var_st_differ_on var_st (modset fs (ves @ es)) var_st'"
          "const_list ves"
          "modset fs es \<subseteq> modset fs es'"
  shows "var_st_differ_on var_st (modset fs (ves @ es')) var_st'"
  using assms(1,2) e_type_const_conv_vs var_st_differ_on_subset[OF _ assms(3)]
        modset_consts_app_equiv
  by metis

lemma var_st_differ_on_arb_app3:
  assumes "var_st_differ_on var_st (modset fs es) var_st'"
  shows "var_st_differ_on var_st (modset fs (es' @ es @ es'')) var_st'"
  by (meson assms modset_arb_app var_st_differ_on_def)

lemma var_st_differ_on_trans:
  assumes "var_st_differ_on var_st (modset fs es) var_st''"
          "var_st_differ_on var_st'' (modset fs es) var_st'"
  shows "var_st_differ_on var_st (modset fs es) var_st'"
  using assms
  unfolding var_st_differ_on_def var_st_agree_def
  by (simp split: var.splits) metis

lemma var_st_differ_on_app:
  assumes "var_st_differ_on var_st (modset fs es) var_st''"
          "var_st_differ_on var_st'' (modset fs es') var_st'"
  shows "var_st_differ_on var_st (modset fs (es@es')) var_st'"
  using assms
  unfolding var_st_differ_on_def var_st_agree_def
  by (simp split: var.splits) (metis modset_arb_app)

lemma var_st_eq_local_differ:
  assumes "var_st_differ_on var_st_l vset var_st_l'"
          "reifies_glob (s.globs s) (inst.globs i) var_st"
          "reifies_loc vs var_st"
          "snd (snd var_st) = lvar_st"
          "reifies_glob (s.globs s') (inst.globs i) var_st'"
          "reifies_loc vs var_st'"
          "snd (snd var_st') = lvar_st"
          "reifies_glob (s.globs s) (inst.globs i) var_st_l"
          "reifies_loc lvs var_st_l"
          "snd (snd var_st_l) = lvar_st"
          "reifies_glob (s.globs s') (inst.globs i) var_st_l'"
          "reifies_loc lvs' var_st_l'"
          "snd (snd var_st_l') = lvar_st"
  shows "var_st_differ_on var_st vset var_st'"
  using assms
  unfolding var_st_differ_on_def reifies_loc_def reifies_glob_def var_st_agree_def var_st_get_global_def
            var_st_get_lvar_def var_st_get_local_def
  apply (cases var_st)
  apply (cases var_st')
  apply (cases var_st_l)
  apply (cases var_st_l')
  apply (auto split: var.splits if_splits)
  done

lemma modifies_var_st:
  assumes "(s,vs,es) \<Down>k{(ls,r,i)} (s',vs',res)"
          "reifies_func (funcs s) (inst.funcs i) fs"
          "reifies_glob (globs s) (inst.globs i) var_st"
          "reifies_loc vs var_st"
          "snd (snd var_st) = lvar_st"
          "reifies_glob (globs s') (inst.globs i) var_st'"
          "reifies_loc vs' var_st'"
          "snd (snd var_st') = lvar_st"
  shows "var_st_differ_on var_st (modset fs es) var_st'"
  using assms
proof (induction "(s,vs,es)" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs es s' vs' res var_st var_st' ls r rule: reduce_to_n.induct)
  case (block ves n t1s t2s m s vs es k s' vs' res)
  hence "var_st_differ_on var_st (modset fs [Label m [] (ves @ ($* es))]) var_st'"
    by blast
  hence "var_st_differ_on var_st (modset fs [$Block (t1s _> t2s) es]) var_st'"
    using modset_block modset_label_inner
    by (metis block(1) e_type_const_conv_vs var_st_differ_on_def)
  thus ?case
    by (metis modset_arb_app var_st_differ_on_def)
next
  case (loop ves n t1s t2s m s vs es k s' vs' res)
  hence "var_st_differ_on var_st (modset fs [Label n [$Loop (t1s _> t2s) es] (ves @ ($* es))]) var_st'"
    by blast
  hence "var_st_differ_on var_st (modset fs [$Loop (t1s _> t2s) es]) var_st'"
    using modset_loop modset_label_inner
    by (metis e_type_const_conv_vs loop(1) modset_label var_st_differ_on_def)
  thus ?case
    by (metis modset_arb_app var_st_differ_on_def)
next
  case (if_false n ves s vs tf e2s k s' vs' res e1s)
  hence "var_st_differ_on var_st (modset fs (ves @ [$Block tf e2s])) var_st'"
    by blast
  hence "var_st_differ_on var_st (modset fs ([$Block tf e2s])) var_st'"
    using modset_consts_app_equiv
    by (metis e_type_const_conv_vs if_false(2))
  hence "var_st_differ_on var_st (modset fs ([$If tf e1s e2s])) var_st'"
    using var_st_differ_on_subset[OF _ modset_if_2] 
    by fastforce
  thus ?case
    by (metis modset_arb_app modset_intros(1) var_st_differ_on_def)
next
  case (if_true n ves s vs tf e1s k s' vs' res e2s)
  hence "var_st_differ_on var_st (modset fs (ves @ [$Block tf e1s])) var_st'"
    by blast
  hence "var_st_differ_on var_st (modset fs ([$Block tf e1s])) var_st'"
    using modset_consts_app_equiv
    by (metis e_type_const_conv_vs if_true(2))
  hence "var_st_differ_on var_st (modset fs ([$If tf e1s e2s])) var_st'"
    using var_st_differ_on_subset[OF _ modset_if_1] 
    by fastforce
  thus ?case
    by (metis modset_arb_app modset_intros(1) var_st_differ_on_def)
next
  case (br_if_true n ves s vs j k s' vs' res)
  hence "var_st_differ_on var_st (modset fs (ves @ [$Br j])) var_st'"
    by simp
  hence "var_st_differ_on var_st {} var_st'"
    using modset_br var_st_differ_on_emp modset_consts_app_equiv e_type_const_conv_vs[OF br_if_true(2)]
    by auto
  thus ?case
    by (simp add: var_st_differ_on_def)
next
  case (br_table js c ves s vs k s' vs' res j)
  hence "var_st_differ_on var_st (modset fs (ves @ [$Br (js !  Wasm_Base_Defs.nat_of_int c)])) var_st'"
    by simp
  hence "var_st_differ_on var_st {} var_st'"
    using modset_br var_st_differ_on_emp modset_consts_app_equiv e_type_const_conv_vs[OF br_table(2)]
    by auto
  thus ?case
    by (simp add: var_st_differ_on_def)
next
  case (br_table_length js c ves s vs j k s' vs' res)
  hence "var_st_differ_on var_st (modset fs (ves @ [$Br j])) var_st'"
    by simp
  hence "var_st_differ_on var_st {} var_st'"
    using modset_br var_st_differ_on_emp modset_consts_app_equiv e_type_const_conv_vs[OF br_table_length(2)]
    by auto
  thus ?case
    by (simp add: var_st_differ_on_def)
next
  case (set_local vi j s v vs v' k)
  then show ?case sorry
next
  case (tee_local v s vs i k s' vs' res)
  obtain v_c where v_c_def:"v = $C v_c"
    using e_type_const_unwrap[OF tee_local(1)]
    by blast
  hence "var_st_differ_on var_st (modset fs [v, v, $Set_local i]) var_st'"
    using tee_local
    by blast
  hence "var_st_differ_on var_st (modset fs ([$Set_local i])) var_st'"
    using modset_consts_app_equiv[of _ "[v_c, v_c]" "[$Set_local i]"] v_c_def
    by simp
  thus ?case
    by (meson modset_intros(1,3) var_st_differ_on_def)
next
  case (set_global s j v s' vs k)
  then show ?case sorry
next
  case (store_Some t v s j m n off mem' vs a k)
  thus ?case
    by (metis var_st_eq_intro2 var_st_differ_on_refl)
next
  case (store_packed_Some t v s j m n off tp mem' vs a k)
  thus ?case
    by (metis var_st_eq_intro2 var_st_differ_on_refl)
next
  case (grow_memory s j m n c mem' vs k)
  thus ?case
    by (metis var_st_eq_intro2 var_st_differ_on_refl)
next
  case (call ves s vs j k s' vs' res)
  thus ?case
    using modset_call1
    by (metis modset_implies var_st_differ_on_subset_const_list_helper)
next
  case (call_indirect_Some s c cl j tf ves vs k ls r s' vs' res)
  show ?case
    by (meson modset_arb_app modset_intros(1,16) var_st_differ_on_def)
next
  case (callcl_native cl j t1s t2s ts es ves vcs n m zs s vs k ls r s' vs' res)
  hence "var_st_differ_on var_st (modset fs [Local m j (vcs @ zs) [$Block ([] _> t2s) es]]) var_st'"
    by blast
  hence "var_st_differ_on var_st (modset fs ([Callcl cl])) var_st'"
    using modset_callcl_native[OF callcl_native(1)]
    by simp
  thus ?case
    using callcl_native(2)
    by (simp add: modset_consts_app_equiv)
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs k)
  thus ?case
    by (simp add: modset_consts_app_equiv modset_intros(15) var_st_differ_on_def)
next
  case (const_value s vs es k s' vs' res ves)
  thus ?case
    by (simp add: modset_consts_app_equiv)
next
  case (label_value s vs es k n ls r s' vs' res les)
  hence "var_st_differ_on var_st (modset fs es) var_st'"
    by simp
  thus ?case
    by (meson modset_intros(11) var_st_differ_on_def)
next
  case (local_value s lls es k n j s' lls' res vs)
  show ?case
  proof (cases "j = i")
    case True
    have 1:"\<forall>gn<length (inst.globs i).
         inst.globs i ! gn
         < length (s.globs s)"
      using local_value(4)
      unfolding reifies_glob_def
      by metis
    hence 2:"\<forall>gn<length (inst.globs i).
         inst.globs i ! gn
         < length (s.globs s')"
      using reduce_to_length_globs[OF local_value(1)]
      by simp
    obtain var_st_l where var_st_l_def:"reifies_glob (s.globs s) (inst.globs i) var_st_l"
                                                "reifies_loc lls var_st_l"
                                                "snd (snd var_st_l) = lvar_st"
      using var_st_ex 1
      by blast
    obtain var_st_l' where var_st_l'_def:"reifies_glob (s.globs s') (inst.globs i) var_st_l'"
                                            "reifies_loc lls' var_st_l'"
                                            "snd (snd var_st_l') = lvar_st"
      using var_st_ex 2
      by blast
    have "var_st_differ_on var_st_l (modset fs es) var_st_l'"
      using local_value(2)[OF True local_value(3) var_st_l_def var_st_l'_def]
      by -
    hence "var_st_differ_on var_st (modset fs es) var_st'"
      using var_st_eq_local_differ[OF _ local_value(4,5,6,7,8,9) var_st_l_def var_st_l'_def]
      by blast
    thus ?thesis
      by (metis True modset_intros(12) var_st_differ_on_def)
  next
    case False
    thus ?thesis
      by (simp add: modset_intros(13) var_st_differ_on_def)
  qed
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  have 1:"reifies_func (s.funcs s'') (inst.funcs i) fs"
    using reduce_to_funcs[OF seq_value(1)] seq_value(5)
    by simp
  have "\<forall>gn<length (inst.globs i).
       inst.globs i ! gn
       < length (s.globs s)"
    using seq_value(6)
    unfolding reifies_glob_def
    by metis
  hence "\<forall>gn<length (inst.globs i).
       inst.globs i ! gn
       < length (s.globs s'')"
    using reduce_to_length_globs[OF seq_value(1)]
    by simp
  then obtain var_st'' where var_st''_def:"reifies_glob (s.globs s'') (inst.globs i) var_st''"
                                          "reifies_loc vs'' var_st''"
                                          "snd (snd var_st'') =
                                          lvar_st"
    using var_st_ex
    by blast
  have "var_st_differ_on var_st (modset fs es) var_st''"
    using seq_value(2)[OF _ _ _ _ var_st''_def] seq_value.prems(1,2,3,4)
    by blast
  moreover
  have "var_st_differ_on var_st'' (modset fs es') var_st'"
    using seq_value(4)[OF 1 var_st''_def]
    by (simp add: modset_consts_app_equiv seq_value.prems(5,6,7))
  ultimately
  show ?case
    using var_st_differ_on_app
    by blast
next
  case (seq_nonvalue ves s vs es k s' vs' res es')
  thus ?case
    by (simp add: var_st_differ_on_arb_app3)
next
  case (label_trap s vs es k n s' vs' les)
  thus ?case
    by (metis modset_intros(11) var_st_differ_on_def)
next
  case (local_trap s lls es k n j s' lls' vs)
  show ?case
  proof (cases "j = i")
    case True
    have 1:"\<forall>gn<length (inst.globs i).
         inst.globs i ! gn
         < length (s.globs s)"
      using local_trap(4)
      unfolding reifies_glob_def
      by metis
    hence 2:"\<forall>gn<length (inst.globs i).
         inst.globs i ! gn
         < length (s.globs s')"
      using reduce_to_length_globs[OF local_trap(1)]
      by simp
    obtain var_st_l where var_st_l_def:"reifies_glob (s.globs s) (inst.globs i) var_st_l"
                                                "reifies_loc lls var_st_l"
                                                "snd (snd var_st_l) = lvar_st"
      using var_st_ex 1
      by blast
    obtain var_st_l' where var_st_l'_def:"reifies_glob (s.globs s') (inst.globs i) var_st_l'"
                                            "reifies_loc lls' var_st_l'"
                                            "snd (snd var_st_l') = lvar_st"
      using var_st_ex 2
      by blast
    have "var_st_differ_on var_st_l (modset fs es) var_st_l'"
      using local_trap(2)[OF True local_trap(3) var_st_l_def var_st_l'_def]
      by -
    hence "var_st_differ_on var_st (modset fs es) var_st'"
      using var_st_eq_local_differ[OF _ local_trap(4,5,6,7,8,9) var_st_l_def var_st_l'_def]
      by blast
    thus ?thesis
      by (metis True modset_intros(12) var_st_differ_on_def)
  next
    case False
    thus ?thesis
      by (simp add: modset_intros(13) var_st_differ_on_def)
  qed
next
  case (label_break_suc s vs es k n s' vs' bn bvs les)
  thus ?case
    by (metis modset_intros(11) var_st_differ_on_def)
next
  case (label_break_nil s vs es k n ls r s'' vs'' bvs les s' vs' res)
  have 1:"reifies_func (s.funcs s'') (inst.funcs i) fs"
    using reduce_to_funcs[OF label_break_nil(1)] label_break_nil(5)
    by simp
  have "\<forall>gn<length (inst.globs i).
       inst.globs i ! gn
       < length (s.globs s)"
    using label_break_nil(6)
    unfolding reifies_glob_def
    by metis
  hence "\<forall>gn<length (inst.globs i).
       inst.globs i ! gn
       < length (s.globs s'')"
    using reduce_to_length_globs[OF label_break_nil(1)]
    by simp
  then obtain var_st'' where var_st''_def:"reifies_glob (s.globs s'') (inst.globs i) var_st''"
                                          "reifies_loc vs'' var_st''"
                                          "snd (snd var_st'') =
                                          lvar_st"
    using var_st_ex
    by blast
  have "var_st_differ_on var_st (modset fs es) var_st''"
    using label_break_nil(2)[OF _ _ _ _ var_st''_def] label_break_nil.prems(1,2,3,4)
    by blast
  moreover
  have "var_st_differ_on var_st'' (modset fs les) var_st'"
    using label_break_nil(4)[OF 1 var_st''_def]
    by (simp add: modset_consts_app_equiv label_break_nil.prems(5,6,7))
  ultimately
  show ?case
    using var_st_differ_on_app
    by (metis modset_arb_app1 modset_intros(11) var_st_differ_on_def)
next
  case (label_return s vs es k n s' vs' rvs les)
  thus ?case
    by (metis modset_intros(11) var_st_differ_on_def)
next
  case (local_return s lls es k n j s' lls' rvs vs)
  show ?case
  proof (cases "j = i")
    case True
    have 1:"\<forall>gn<length (inst.globs i).
         inst.globs i ! gn
         < length (s.globs s)"
      using local_return(4)
      unfolding reifies_glob_def
      by metis
    hence 2:"\<forall>gn<length (inst.globs i).
         inst.globs i ! gn
         < length (s.globs s')"
      using reduce_to_length_globs[OF local_return(1)]
      by simp
    obtain var_st_l where var_st_l_def:"reifies_glob (s.globs s) (inst.globs i) var_st_l"
                                                "reifies_loc lls var_st_l"
                                                "snd (snd var_st_l) = lvar_st"
      using var_st_ex 1
      by blast
    obtain var_st_l' where var_st_l'_def:"reifies_glob (s.globs s') (inst.globs i) var_st_l'"
                                            "reifies_loc lls' var_st_l'"
                                            "snd (snd var_st_l') = lvar_st"
      using var_st_ex 2
      by blast
    have "var_st_differ_on var_st_l (modset fs es) var_st_l'"
      using local_return(2)[OF True local_return(3) var_st_l_def var_st_l'_def]
      by -
    hence "var_st_differ_on var_st (modset fs es) var_st'"
      using var_st_eq_local_differ[OF _ local_return(4,5,6,7,8,9) var_st_l_def var_st_l'_def]
      by blast
    thus ?thesis
      by (metis True modset_intros(12) var_st_differ_on_def)
  next
    case False
    thus ?thesis
      by (simp add: modset_intros(13) var_st_differ_on_def)
  qed
qed (metis var_st_eq_intro1 var_st_differ_on_refl)+



definition pred_option_Some :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "pred_option_Some pred opt \<equiv> opt \<noteq> None \<and> pred_option pred opt"

(* separating conjuction *)
definition sep_conj :: "'a heap_ass \<Rightarrow> 'a heap_ass \<Rightarrow> 'a heap_ass" (infixr "\<^emph>" 60) where
  "ha' \<^emph> ha'' \<equiv> \<lambda>h st. \<exists>h' h''. heap_disj h' h'' \<and> ha' h' st \<and> ha'' h'' st \<and> heap_merge h' h'' = h"

definition ass_frame :: "'a heap_ass \<Rightarrow> 'a ass \<Rightarrow> 'a ass" where
  "ass_frame F ass \<equiv> (case ass of
                        (St \<^sub>s|\<^sub>h H) \<Rightarrow>  St \<^sub>s|\<^sub>h (H \<^emph> F)
                      | x \<Rightarrow> x)"

lemma ass_stack_len_ass_frame_inv: "ass_stack_len (ass_frame Hf ass) = ass_stack_len ass"
  unfolding ass_frame_def
  apply (cases ass)
   apply auto
  done

lemma reifies_lab_ass_frame_inv: "reifies_lab labs (fs, map (ass_frame Hf) ls,  rs) = reifies_lab labs (fs, ls, rs)"
  unfolding reifies_lab_def
  by (auto simp add: ass_stack_len_ass_frame_inv)

lemma reifies_ret_ass_frame_inv: "reifies_ret ret (fs, ls, map_option (ass_frame Hf) rs) = reifies_ret ret (fs, ls, rs)"
  unfolding reifies_ret_def
  by (metis (no_types, lifting) ass_stack_len_ass_frame_inv not_Some_eq option.simps(8,9) prod.sel(2))

definition args_ass :: "'a stack_ass \<Rightarrow> nat \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "args_ass St n v_st \<equiv> (length St = n \<and> (\<forall>i < n. pred_option_Some (\<lambda>v. (St!i) v v_st) (var_st_get_local v_st i)))"

definition zeros_ass :: "nat \<Rightarrow> t list \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "zeros_ass n ts v_st \<equiv> (\<forall>i < (length ts). (var_st_get_local v_st (i+n)) = Some (bitzero (ts!i)))"

definition is_lvar :: "lvar \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar lv v v_st \<equiv> var_st_get_lvar v_st lv = Some (V_p v)"

definition is_lvar32 :: "lvar \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar32 lv v v_st \<equiv> var_st_get_lvar v_st lv = Some (V_p v) \<and> typeof v = T_i32"

definition is_lvar_len :: "lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_len lv h v_st \<equiv> let (h_raw,l_opt) = h in
                            h_raw = Map.empty \<and> pred_option_Some (\<lambda>l. var_st_get_lvar v_st lv = Some (V_n l)) l_opt"

definition is_lvar_lvar32_len :: "lvar \<Rightarrow> lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_lvar32_len lv lv32 h v_st \<equiv> let (h_raw,l_opt) = h in
                                        h_raw = Map.empty 
                                      \<and> pred_option_Some (\<lambda>l. var_st_get_lvar v_st lv = Some (V_n l) \<and> var_st_get_lvar v_st lv32 = Some (V_p (ConstInt32 (int_of_nat l)))) l_opt"

inductive inf_triples :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_\<bullet>_ \<tturnstile> _" 60)
      and inf_triple :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> 'a ass \<Rightarrow> e list \<Rightarrow> 'a ass \<Rightarrow> bool" ("_\<bullet>_ \<turnstile> {_}_{_}" 60) where
  "\<Gamma>\<bullet>assms \<turnstile> {P} es {Q} \<equiv> \<Gamma>\<bullet>assms \<tturnstile> {(P,es,Q)}"
| Size_mem:"\<Gamma>\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h is_lvar_len lv_l} [$Current_memory] {[is_lvar32 lv'] \<^sub>s|\<^sub>h is_lvar_lvar32_len lv_l lv'}"
(*| Grow_mem:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar32 lv] \<^sub>s|\<^sub>h is_lvar_len lv_l} [$Grow_memory] {[is_lvar32 lv'] \<^sub>s|\<^sub>h H}" *)
| Function:"\<lbrakk>cl = Func_native i (tn _> tm) tls es; (fs,[],Some (St' \<^sub>s|\<^sub>h H'))\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h (\<lambda>h v_st. H h v_st \<and> (args_ass St (length tn) v_st) \<and> (zeros_ass (length tn) tls v_st))} [$Block ([] _> tm) es] {St' \<^sub>s|\<^sub>h H'}\<rbrakk> \<Longrightarrow> (fs,ls,r)\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} [Callcl cl] {St' \<^sub>s|\<^sub>h H'}"
| Asm:"\<lbrakk>(P, [$Call k], Q) \<in> assms\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} [$Call k] {Q}"
| Seq:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> {P} es {Q}; \<Gamma>\<bullet>assms \<turnstile> {Q} es' {R}\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} es@es' {R}"
| Conseq:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> {P'} es {Q'}; \<forall>vs h vs_t. (ass_sat P vs h vs_t \<longrightarrow> ass_sat P' vs h vs_t) \<and> (ass_sat Q' vs h vs_t \<longrightarrow> ass_sat Q vs h vs_t)\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} es {Q}"
| Frame:"\<lbrakk>(fs,ls,rs)\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} es {St' \<^sub>s|\<^sub>h H'}; heap_ass_ind_on Hf (modset fs es); (\<forall>ass \<in> (set ls). \<exists>Sa Ha. ass = Sa \<^sub>s|\<^sub>h Ha); pred_option (\<lambda>ass. \<exists>Sa Ha. ass = Sa \<^sub>s|\<^sub>h Ha) rs\<rbrakk> \<Longrightarrow> (fs,map (ass_frame Hf) ls, map_option (ass_frame Hf) rs)\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h (H \<^emph> Hf)} es {St' \<^sub>s|\<^sub>h (H' \<^emph> Hf)}"
| Ext:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} es {St' \<^sub>s|\<^sub>h H'}; stack_ass_ind_on Stf (modset (fst \<Gamma>) es)\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {(Stf @ St) \<^sub>s|\<^sub>h H} es {(Stf @ St') \<^sub>s|\<^sub>h H'}"
| Call:"\<lbrakk>(fs,[],None)\<bullet>specs \<tturnstile> ({(P,c,Q). \<exists>i. (P, [$Call i], Q) \<in> specs \<and> i< length fs \<and> c = [Callcl (fs!i)]}); \<forall>(P,c,Q) \<in> specs. \<exists>i. c = [$Call i] \<and> i < length fs\<rbrakk> \<Longrightarrow> (fs,[],None)\<bullet>({}) \<tturnstile> specs"
| ConjI:"\<forall>(P,es,Q) \<in> specs. (\<Gamma>\<bullet>assms \<turnstile> {P} es {Q}) \<Longrightarrow> \<Gamma>\<bullet>assms \<tturnstile> specs"
| ConjE:"\<lbrakk>\<Gamma>\<bullet>assms \<tturnstile> specs; (P,es,Q) \<in> specs\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} es {Q}"

lemma valid_triple_n_call_equiv_callcl:
  assumes "j < length fs"
          "(\<Gamma>::'a triple_context) = (fs, [], None)"
  shows "\<Gamma> \<Turnstile>_ (Suc n) {P} [$Call j] {Q} = (\<Gamma> \<Turnstile>_n {P} [Callcl (fs!j)] {Q})"
proof -
  {
    fix lvar_st::"(lvar \<Rightarrow> 'a lvar_v option)"
    and P es Q vcs h st s locs labs ret hf vcsf s' locs' res
    {
      assume local_assms:"ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P"
      have "((s,locs,($$*vcsf)@($$*vcs)@[$Call j]) \<Down>(Suc n){(labs,ret,i)} (s',locs', res)) =
              ((s,locs,($$*vcsf)@($$*vcs)@[Callcl (fs!j)]) \<Down>n{(labs,ret,i)} (s',locs', res))"
        using calln reifies_func_ind[OF _ assms(1)] local_assms
        unfolding ass_wf_def reifies_s_def assms(2)
        by (metis (no_types, lifting) Pair_inject append.assoc map_append prod.collapse)
    }
    hence "((ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P) \<and> ((s,locs,($$*vcsf)@($$*vcs)@[$Call j]) \<Down>(Suc n){(labs,ret,i)} (s',locs', res))) =
              ((ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P) \<and> ((s,locs,($$*vcsf)@($$*vcs)@[Callcl (fs!j)]) \<Down>n{(labs,ret,i)} (s',locs', res)))"
      by blast
  }
  thus ?thesis
    unfolding valid_triple_n_def
    by metis
qed

lemma sep_conj_imp_frame:
  assumes   "stack_ass_sat St vcs st"
            "heap_disj h_H h_Hf"
            "H h_H st"
            "Hf h_Hf st"
            "heap_merge h_H h_Hf = h"
            "heap_disj h hf"
            "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
            "reifies_loc locs st"
            "reifies_lab labs \<Gamma>"
            "reifies_ret ret \<Gamma>"
            "snd (snd st) = lvar_st"
  shows "(ass_wf lvar_st ret \<Gamma> labs locs s (heap_merge h_Hf hf) st h_H vcs (St \<^sub>s|\<^sub>h H))"
proof -
  show ?thesis
    using assms
    unfolding ass_wf_def
    by (auto simp add: heap_merge_assoc heap_disj_merge_assoc)
qed

lemma res_wf_intro_value:
  assumes "ass_sat (St' \<^sub>s|\<^sub>h H') vcs' h'' st'"
          "rvs = vcsf @ vcs'"
          "heap_disj h'' hf"
          "h' = heap_merge h'' hf"
          "reifies_s s' i h' st' fs"
          "reifies_loc locs' st'"
          "snd (snd st') = lvar_st"
  shows "res_wf lvar_st (fs,lesss,ress) (RValue rvs) locs' s' hf vcsf (St' \<^sub>s|\<^sub>h H')"
  using assms
proof -
  have "\<exists>p pa vs pb. ass_sat (St' \<^sub>s|\<^sub>h H') vs pa pb \<and> vcsf @ vcs' = vcsf @ vs \<and> heap_disj pa hf \<and> p = heap_merge pa hf \<and> reifies_s s' i p pb fs \<and> reifies_loc locs' pb \<and> snd (snd pb) = lvar_st"
    using assms by blast
  then show ?thesis
    by (simp add: assms(2) res_wf_def)
qed

lemma res_wf_intro_break:
  assumes "k < length lesss"
          "ass_sat (lesss ! k) vcs' h'' st'"
          "rvs = vcs'"
          "heap_disj h'' hf"
          "h' = heap_merge h'' hf"
          "reifies_s s' i h' st' fs"
          "reifies_loc locs' st'"
          "snd (snd st') = lvar_st"
  shows "res_wf lvar_st (fs,lesss,ress) (RBreak k rvs) locs' s' hf vcsf (St' \<^sub>s|\<^sub>h H')"
  using assms
proof -

  have "\<exists>h' h'' vcs' st'.
              k < length lesss \<and>
              ass_sat (lesss ! k) vcs' h''
               st' \<and>
              rvs = vcs' \<and>
              heap_disj h'' hf \<and>
              h' = heap_merge h'' hf \<and>
              reifies_s s' i h' st' fs \<and>
              reifies_loc locs' st' \<and>
              snd (snd st') = lvar_st"
    using assms
    by blast
  thus ?thesis
    by (simp add: assms(2) res_wf_def)
qed

lemma res_wf_intro_return:
  assumes "ress = Some the_ress"
          "ass_sat the_ress vcs' h'' st'"
          "rvs = vcs'"
          "heap_disj h'' hf"
          "h' = heap_merge h'' hf"
          "reifies_s s' i h' st' fs"
          "reifies_loc locs' st'"
          "snd (snd st') = lvar_st"
  shows "res_wf lvar_st (fs,lesss,ress) (RReturn rvs) locs' s' hf vcsf (St' \<^sub>s|\<^sub>h H')"
  using assms
proof -
  have "\<exists>h' h'' vcs' st' the_rass.
              ress = Some the_rass \<and>
              ass_sat the_rass vcs' h'' st' \<and>
              rvs = vcs' \<and>
              heap_disj h'' hf \<and>
              h' = heap_merge h'' hf \<and>
              reifies_s s' i h' st' fs \<and>
              reifies_loc locs' st' \<and>
              snd (snd st') = lvar_st"
    using assms
    by blast
  thus ?thesis
    by (simp add: assms(2) res_wf_def)
qed

lemma stack_ass_sat_differ:
  assumes "stack_ass_sat Stf vcs st"
          "var_st_differ_on st vars st'"
          "stack_ass_ind_on Stf vars"
  shows "stack_ass_sat Stf vcs st'"
  using assms
  unfolding var_st_differ_on_def stack_ass_ind_on_def
  by blast

lemma heap_ass_sat_differ:
  assumes "Hf h st"
          "var_st_differ_on st vars st'"
          "heap_ass_ind_on Hf vars"
  shows "Hf h st'"
  using assms
  unfolding var_st_differ_on_def heap_ass_ind_on_def
  by blast

lemma res_wf_ext:
  assumes "(ass_wf lvar_st ret \<Gamma> labs locs s hf st h (vcs_sf @ vcs_s) (Stf @ St \<^sub>s|\<^sub>h H))"
          "(s,locs,($$*vcsf)@($$*vcs)@es) \<Down>n{(labs,ret,i)} (s',locs', (RValue res))"
          "res_wf lvar_st \<Gamma> (RValue res) locs' s' hf (vcsf@vcs_sf) (St' \<^sub>s|\<^sub>h H')"
          "stack_ass_ind_on Stf (modset (fst \<Gamma>) (($$*vcsf)@($$*vcs)@es))"
          "stack_ass_sat Stf vcs_sf st"
          "stack_ass_sat St vcs_s st"
  shows "res_wf lvar_st \<Gamma> (RValue res) locs' s' hf vcsf (Stf @ St' \<^sub>s|\<^sub>h H')"
proof -
  have st_is:"ass_sat (Stf @ St \<^sub>s|\<^sub>h H) (vcs_sf @ vcs_s) h st"
       "reifies_func (funcs s) (inst.funcs i) (fst \<Gamma>)"
       "reifies_glob (globs s) (inst.globs i) st"
       "reifies_loc locs st"
       "snd (snd st) = lvar_st"
    using assms(1)
    unfolding ass_wf_def reifies_s_def
    by auto
  obtain  h' h'' vcs' st' where st'_is:
          "ass_sat (St' \<^sub>s|\<^sub>h H') vcs' h''  st'"
          "res = vcsf @ (vcs_sf @ vcs')"
          "heap_disj h'' hf"
          "h' = heap_merge h'' hf"
          "reifies_s s' i h' st' (fst \<Gamma>)"
          "reifies_loc locs' st'"
          "snd (snd st') = lvar_st"
    using assms(3)
    unfolding res_wf_def
    by fastforce
  have 1:"reifies_glob (s.globs s') (inst.globs i) st'"
    using st'_is(5)
    unfolding reifies_s_def
    by blast
  have "ass_sat (Stf @ St' \<^sub>s|\<^sub>h H') (vcs_sf @ vcs') h'' st'"
    using st'_is(1)
          stack_ass_sat_differ[OF assms(5) _ assms(4)]
          modifies_var_st[OF assms(2) st_is(2,3,4,5) 1 st'_is(6,7)]
    by (simp add: list_all2_appendI stack_ass_sat_def)
  thus ?thesis
    using res_wf_intro_value[OF _ st'_is(2,3,4,5,6,7)]
    by (metis prod.exhaust_sel)
qed

lemma res_wf_frame:
  assumes "\<Gamma> = (fs, map (ass_frame Hf) ls, map_option (ass_frame Hf) rs)"
          "(ass_wf lvar_st ret \<Gamma> labs locs s hf st (heap_merge h_H h_Hf) vcs (St \<^sub>s|\<^sub>h (H \<^emph> Hf)))"
          "(s,locs,($$*vcsf)@($$*vcs)@es) \<Down>n{(labs,ret,i)} (s',locs', res)"
          "res_wf lvar_st (fs,ls,rs) res locs' s' (heap_merge h_Hf hf) vcsf (St' \<^sub>s|\<^sub>h H')"
          "heap_disj h_H h_Hf"
          "H h_H st"
          "Hf h_Hf st"
          "heap_ass_ind_on Hf (modset fs es)"
          "\<forall>ass\<in>set ls. \<exists>Sa Ha. ass = Sa \<^sub>s|\<^sub>h Ha"
          "pred_option (\<lambda>ass. \<exists>Sa Ha. ass = Sa \<^sub>s|\<^sub>h Ha) rs"
  shows "res_wf lvar_st \<Gamma> res locs' s' hf vcsf (St' \<^sub>s|\<^sub>h (H' \<^emph> Hf))"
proof -
  have st_is:"ass_sat (St \<^sub>s|\<^sub>h (H \<^emph> Hf)) vcs (heap_merge h_H h_Hf) st"
       "reifies_func (funcs s) (inst.funcs i) (fst \<Gamma>)"
       "reifies_glob (globs s) (inst.globs i) st"
       "reifies_loc locs st"
       "snd (snd st) = lvar_st"
       "heap_disj (heap_merge h_H h_Hf) hf"
       "reifies_heap (s.mem s) (inst.mem i) (heap_merge (heap_merge h_H h_Hf) hf)"
    using assms(2)
    unfolding ass_wf_def reifies_s_def
    by auto
  show ?thesis
  proof (cases res)
    case (RValue x1)
    then obtain  h' h'' vcs' st' where st'_is:
          "ass_sat (St' \<^sub>s|\<^sub>h H') vcs' h'' st'"
          "x1 = vcsf @ vcs'"
          "heap_disj h'' (heap_merge h_Hf hf)"
          "h' = heap_merge h'' (heap_merge h_Hf hf)"
          "reifies_s s' i h' st' fs"
          "reifies_loc locs' st'"
          "snd (snd st') = lvar_st"
      using assms(4)
      unfolding res_wf_def
      by fastforce
    have 0:"heap_disj h'' h_Hf"
      using st'_is(3)
      unfolding heap_disj_def heap_merge_def map_disj_def disjnt_def option_disj_def
      by (auto split: option.splits prod.splits)
    have 2:"H' h'' st'"
      using st'_is(1)
      by auto
    have 1:"reifies_glob (s.globs s') (inst.globs i) st'"
      using st'_is(5)
      unfolding reifies_s_def
      by blast
    have 3:"Hf h_Hf st'"
      using heap_ass_sat_differ[OF assms(7) _ assms(8)] assms(1) modset_consts_app[of _ fs "vcsf@vcs" es]
            modifies_var_st[OF assms(3) st_is(2,3,4,5) 1 st'_is(6,7)]
      by (simp add: var_st_differ_on_def)
    have 4:"ass_sat (St' \<^sub>s|\<^sub>h (H' \<^emph> Hf)) vcs' (heap_merge h'' h_Hf) st'"
      using st'_is(1) 3 0 2
      apply ( simp add: list_all2_appendI sep_conj_def)
      apply (metis prod.collapse)
      done
    have "heap_disj (heap_merge h'' h_Hf) hf"
      by (metis heap_disj_merge_assoc heap_disj_merge_sub(2) heap_disj_sym st'_is(3) st_is(6))
    thus ?thesis
      using RValue res_wf_intro_value[OF 4 st'_is(2) _ _ st'_is(5,6,7)] assms(1) heap_merge_assoc st'_is(4)
      by blast
  next
    case (RBreak x21 x22)
    then obtain  h' h'' vcs' st' where st'_is:
          "x21 < length ls"
          "ass_sat (ls ! x21) vcs' h'' st'"
          "x22 = vcs'"
          "heap_disj h'' (heap_merge h_Hf hf)"
          "h' = heap_merge h'' (heap_merge h_Hf hf)"
          "reifies_s s' i h' st' fs"
          "reifies_loc locs' st'"
          "snd (snd st') = lvar_st"
      using assms(4)
      unfolding res_wf_def
      by fastforce
    have 0:"heap_disj h'' h_Hf"
      using st'_is(4)
      unfolding heap_disj_def heap_merge_def map_disj_def disjnt_def option_disj_def
      by (auto split: option.splits prod.splits)
    obtain Hr Str where lsi:"(ls ! x21) = Str \<^sub>s|\<^sub>h Hr"
      using assms(9) st'_is(1) nth_mem
      by blast
    have 2:"Hr h'' st'"
      using st'_is(2) lsi
      by auto
    have 1:"reifies_glob (s.globs s') (inst.globs i) st'"
      using st'_is(6)
      unfolding reifies_s_def
      by blast
    have 3:"Hf h_Hf st'"
      using heap_ass_sat_differ[OF assms(7) _ assms(8)] assms(1) modset_consts_app[of _ fs "vcsf@vcs" es]
            modifies_var_st[OF assms(3) st_is(2,3,4,5) 1 st'_is(7,8)]
      by (simp add: var_st_differ_on_def)
    have 4:"ass_sat (Str \<^sub>s|\<^sub>h (Hr \<^emph> Hf)) vcs' (heap_merge h'' h_Hf) st'"
      using st'_is(2) 3 0 2 lsi
      apply (simp add: list_all2_appendI sep_conj_def)
      apply (metis prod.collapse)
      done
    have 5:"heap_disj (heap_merge h'' h_Hf) hf"
      by (metis heap_disj_merge_assoc heap_disj_merge_sub(2) heap_disj_sym st'_is(4) st_is(6))
    have 6:"(map (ass_frame Hf) ls)!x21 = (Str \<^sub>s|\<^sub>h (Hr \<^emph> Hf))"
      using st'_is(1) lsi
      unfolding ass_frame_def
      by auto
    show ?thesis
      using RBreak res_wf_intro_break[OF _ _ _ 5 _ st'_is(6,7,8)] assms(1) heap_merge_assoc 4 6 st'_is(1,3,5)
      by auto
  next
    case RTrap
    thus ?thesis
      using assms(4)
      unfolding res_wf_def
      by auto
  next
    case (RReturn x3)
    then obtain  h' h'' vcs' st' the_rass where st'_is:
          "rs = Some the_rass"
          "ass_sat the_rass vcs' h'' st'"
          "x3 = vcs'"
          "heap_disj h'' (heap_merge h_Hf hf)"
          "h' = heap_merge h'' (heap_merge h_Hf hf)"
          "reifies_s s' i h' st' fs"
          "reifies_loc locs' st'"
          "snd (snd st') = lvar_st"
      using assms(4)
      unfolding res_wf_def
      by fastforce
    have 0:"heap_disj h'' h_Hf"
      using st'_is(4)
      unfolding heap_disj_def heap_merge_def map_disj_def disjnt_def option_disj_def
      by (auto split: option.splits prod.splits)
    obtain Hr Str where rass_def:"the_rass = Str \<^sub>s|\<^sub>h Hr"
      using assms(10) st'_is(1)
      by auto
    have 2:"Hr h'' st'"
      using st'_is(2) rass_def
      by auto
    have 1:"reifies_glob (s.globs s') (inst.globs i) st'"
      using st'_is(6)
      unfolding reifies_s_def
      by blast
    have 3:"Hf h_Hf st'"
      using heap_ass_sat_differ[OF assms(7) _ assms(8)] assms(1) modset_consts_app[of _ fs "vcsf@vcs" es]
            modifies_var_st[OF assms(3) st_is(2,3,4,5) 1 st'_is(7,8)]
      by (simp add: var_st_differ_on_def)
    have 4:"ass_sat (Str \<^sub>s|\<^sub>h (Hr \<^emph> Hf)) vcs' (heap_merge h'' h_Hf) st'"
      using st'_is(2) 3 0 2 rass_def
      apply (simp add: list_all2_appendI sep_conj_def)
      apply (metis prod.collapse)
      done
    have 5:"heap_disj (heap_merge h'' h_Hf) hf"
      by (metis heap_disj_merge_assoc heap_disj_merge_sub(2) heap_disj_sym st'_is(4) st_is(6))
    have 6:"map_option (ass_frame Hf) rs = Some (Str \<^sub>s|\<^sub>h (Hr \<^emph> Hf))"
      using st'_is(1) rass_def
      unfolding ass_frame_def
      by auto
    show ?thesis
      using RReturn res_wf_intro_return[OF 6 4 st'_is(3) 5 _ st'_is(6,7,8)] assms(1) heap_merge_assoc st'_is(5)
      by blast
  qed
qed

lemma valid_triples_n_call_equiv_callcl:
  assumes "(\<Gamma>::'a triple_context) = (fs, [], None)"
          "\<forall>(P, c, Q)\<in>specs. \<exists>i. c = [$Call i] \<and> i < length fs"
          "\<Gamma> \<TTurnstile>_n
             {(P, c, Q).
                \<exists>i. (P, [$Call i], Q) \<in> specs \<and>
                    i < length fs \<and> c = [Callcl (fs ! i)]}"
  shows "\<Gamma>\<bullet>{} \<TTurnstile>_ (Suc n) specs"
proof -
  have "\<Gamma> \<TTurnstile>_(Suc n) specs"
    using valid_triple_n_call_equiv_callcl[OF _ assms(1), symmetric] assms(2,3)
    unfolding valid_triples_n_def
    by fastforce
  thus ?thesis
    using assms(2)
    unfolding valid_triples_assms_n_def
    by auto
qed

lemma
  assumes "\<Gamma>\<bullet>assms \<tturnstile> specs"
  shows "(\<Gamma>\<bullet>assms \<TTurnstile>_n specs)"
  using assms
proof(induction arbitrary: n rule:inf_triples.induct)
case (Size_mem \<Gamma> assms lv_l lv')
  then show ?case sorry
next
  case (Function cl tn tm tls es fs St' H' assms H St ls r)
  then show ?case sorry
next
  case (Asm P k Q assms \<Gamma>)
  {
    assume "((fst \<Gamma>,[],None) \<TTurnstile>_n assms)"
    hence "((fst \<Gamma>,[],None) \<TTurnstile>_n {(P, [$Call k], Q)})"
      using Asm
      by (metis singletonD valid_triples_n_def)
    hence "\<Gamma> \<TTurnstile>_ n {(P, [$Call k], Q)}"
      using extend_context_call
      apply (cases \<Gamma>)
      apply (simp add: valid_triple_defs(5) extend_context_call)
      done
  }
  thus ?case
    unfolding valid_triples_assms_n_def
    by blast
next
  case (Seq \<Gamma> assms P es Q es' R)
  then show ?case sorry
next
  case (Conseq \<Gamma> assms P' es Q' P Q)
  thus ?case
    using valid_triple_assms_n_conseq
    by blast
next
  case (Frame fs ls rs assms St H es St' H' Hf)
  {
    fix vcs h st s locs labs ret lvar_st vcsf s' locs' res hf \<Gamma>
    assume local_assms:"\<Gamma> = (fs, map (ass_frame Hf) ls,  map_option (ass_frame Hf) rs)"
                       "(fst \<Gamma>,[],None) \<TTurnstile>_n assms"
                       "(ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (St \<^sub>s|\<^sub>h (H \<^emph> Hf)))"
                       "(s,locs,($$*vcsf)@($$*vcs)@es) \<Down>n{(labs,ret,i)} (s',locs', res)"
    then obtain h_H h_Hf where h_H_def:"heap_disj h_H h_Hf"
                                       "H h_H st"
                                       "Hf h_Hf st"
                                       "heap_merge h_H h_Hf = h"
      unfolding ass_wf_def sep_conj_def
      by fastforce
    hence 0:"(ass_wf lvar_st ret \<Gamma> labs locs s (heap_merge h_Hf hf) st h_H vcs (St \<^sub>s|\<^sub>h H))"
      using sep_conj_imp_frame local_assms(1,3) heap_disj_merge_assoc heap_merge_assoc
      unfolding ass_wf_def sep_conj_def
      by auto
    hence 1:"(ass_wf lvar_st ret (fs, ls, rs) labs locs s (heap_merge h_Hf hf) st h_H vcs (St \<^sub>s|\<^sub>h H))"
      using reifies_lab_ass_frame_inv reifies_ret_ass_frame_inv local_assms(1)
      unfolding ass_wf_def
      by (metis fstI prod.sel(2) reifies_lab_def reifies_ret_def)
    have "((fs, ls, rs) \<Turnstile>_n {(St \<^sub>s|\<^sub>h H)}es{(St' \<^sub>s|\<^sub>h H')})"
      using local_assms(1,2) Frame(5)
      unfolding valid_triples_assms_n_def valid_triples_n_def
      by auto
    hence "res_wf lvar_st (fs, ls, rs) res locs' s' (heap_merge h_Hf hf) vcsf (St' \<^sub>s|\<^sub>h H')"
      using local_assms(4) 1
      unfolding valid_triple_defs
      by metis
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf (St' \<^sub>s|\<^sub>h (H' \<^emph> Hf))"
      using res_wf_frame[OF local_assms(1) _ local_assms(4) _ h_H_def(1) _ _ _ Frame(3,4)]
            Frame(2) h_H_def(2,3,4) local_assms(3)
      by blast
  }
  thus ?case
    unfolding valid_triple_defs
    by auto
next
  case (Ext \<Gamma> assms St H es St' H' Stf)
  {
    fix vcs h st s locs labs ret lvar_st vcsf s' locs' res hf
    assume local_assms:"(fst \<Gamma>,[],None) \<TTurnstile>_n assms"
                       "(ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (Stf @ St \<^sub>s|\<^sub>h H))"
                       "(s,locs,($$*vcsf)@($$*vcs)@es) \<Down>n{(labs,ret,i)} (s',locs', res)"
    obtain vcs' vcs'' where vcs_is:"stack_ass_sat (Stf @ St) vcs st"
                                    "stack_ass_sat Stf vcs' st"
                                    "stack_ass_sat St vcs'' st"
                                    "vcs = vcs'@vcs''"
      using local_assms(2)
      unfolding ass_wf_def
      by (fastforce simp add: stack_ass_sat_def list_all2_append1)
    hence 1:"(ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs'' (St \<^sub>s|\<^sub>h H))"
      using local_assms(2)
      unfolding ass_wf_def ass_sat.simps
      by simp
    have "(\<Gamma> \<Turnstile>_n {(St \<^sub>s|\<^sub>h H)}es{(St' \<^sub>s|\<^sub>h H')})"
      using local_assms(1) Ext(3)[of n]
      unfolding valid_triples_assms_n_def valid_triples_n_def
      by auto
    hence 2:"res_wf lvar_st \<Gamma> res locs' s' hf (vcsf@vcs') (St' \<^sub>s|\<^sub>h H')"
      using local_assms(3) 1
      unfolding valid_triple_defs
      by (metis vcs_is(4) append.assoc map_append)
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf (Stf @ St' \<^sub>s|\<^sub>h H')"
    proof (cases res)
      case (RValue x1)
      hence 3:"(ass_wf lvar_st ret \<Gamma> labs locs s hf st h (vcs'@vcs'') (Stf @ St \<^sub>s|\<^sub>h H))"
              "(s,locs,($$*vcsf)@($$*vcs)@es) \<Down>n{(labs,ret,i)} (s',locs', (RValue x1))"
              "res_wf lvar_st \<Gamma> (RValue x1) locs' s' hf (vcsf@vcs') (St' \<^sub>s|\<^sub>h H')"
        using local_assms(2,3) vcs_is(4) 2
        by auto
      have "stack_ass_ind_on Stf (modset (fst \<Gamma>) (($$* vcsf) @ ($$* vcs) @ es))"
        using Ext(2) modset_consts_app
        by (metis Collect_cong modifies_modset_eq modset_def)
      thus ?thesis
        using res_wf_ext[OF 3(1,2,3) _ vcs_is(2,3)] RValue
        by fastforce
    qed (auto simp add: res_wf_def)
  }
  thus ?case
    unfolding valid_triple_defs
    by auto
next
  case (Call fs specs)
  show ?case
    using Call(2,3)
  proof (induction n)
    case 0
    {
      fix a :: "'a ass" and aa :: "e list" and b :: "'a ass" and vcs :: "v list" and ab :: "nat \<Rightarrow> 8 word option" and ba :: "nat option" and ac :: "global list" and ad :: "v list" and bb :: "lvar \<Rightarrow> 'a lvar_v option" and s :: s and locs :: "v list" and labs :: "nat list" and ret :: "nat option" and lvar_st :: "lvar \<Rightarrow> 'a lvar_v option" and ae :: "nat \<Rightarrow> 8 word option" and bc :: "nat option" and vcsf :: "v list" and s' :: s and locs' :: "v list" and res :: res_b
      assume a1: "\<And>s vs ves j a aa b s' vs' res. (s, vs, ($$* ves) @ [$Call j]) \<Down>0{(a, aa, b)} (s', vs', res) \<Longrightarrow> False"
      assume a2: "(s, locs, ($$* vcsf) @ ($$* vcs) @ aa) \<Down>0{(labs, ret, i)} (s', locs', res)"
      assume a3: "\<forall>x\<in>specs. case x of (P, c, Q) \<Rightarrow> \<exists>i. c = [$Call i] \<and> i < length fs"
      assume "(a, aa, b) \<in> specs"
      then obtain nn :: "e list \<Rightarrow> nat" where
        "aa = [$Call (nn aa)] \<and> nn aa < length fs"
        using a3 by moura
      then have "res_wf lvar_st (fs, []::'a ass list, None::'a ass option) res locs' s' (ae, bc) vcsf b"
        using a2 a1 by (metis (no_types) append.assoc map_append)
    }
    thus ?case
      unfolding valid_triple_defs
      using Call.hyps(2) call0 case_prodD case_prodI2
      by force
  next
    case (Suc n)
    have "(fs, [], None)\<bullet>{} \<TTurnstile>_ n specs"
      using Suc(1)[OF Suc(2,3)]
      by -
    hence "(fs, [], None) \<TTurnstile>_ n {(P, c, Q). \<exists>i. (P, [$Call i], Q) \<in> specs \<and> i < length fs \<and> c = [Callcl (fs ! i)]}"
      using Suc(3)[of n]
      unfolding valid_triples_assms_n_def
      by (simp add: valid_triples_n_emp)
    thus ?case
      using valid_triples_n_call_equiv_callcl[OF _ Suc(2)]
      by blast
  qed
next
  case (ConjI specs \<Gamma> assms)
  thus ?case
    by (metis (no_types, lifting) case_prodE valid_triple_defs(5,6) singletonI)
next
case (ConjE \<Gamma> assms specs P es Q)
  thus ?case
    by (metis encapsulated_module.valid_triple_defs(5,6) singletonD)
qed

end
end
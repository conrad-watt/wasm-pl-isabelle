theory Wasm_Inference_Rules imports Wasm_Assertions_Shallow begin

lemma lv_neq_update:
  assumes "lv_arb \<noteq> lv"
  shows "var_st_get_lvar (var_st_set_lvar st lv_arb v) lv = var_st_get_lvar st lv"
  using assms
  unfolding var_st_get_lvar_def var_st_set_lvar_def
  by (simp split: prod.splits)

lemma lv_eq_update:
  shows "var_st_get_lvar (var_st_set_lvar st lv_arb v) lv_arb = Some v"
  unfolding var_st_get_lvar_def var_st_set_lvar_def
  by (simp split: prod.splits)

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

definition stack_ass_ind_on_locals :: "'a stack_ass \<Rightarrow> bool" where
  "stack_ass_ind_on_locals St \<equiv> stack_ass_ind_on St {lc. \<exists>n. lc = Lc n}"

definition heap_ass_ind_on_locals :: "'a heap_ass \<Rightarrow> bool" where
  "heap_ass_ind_on_locals H \<equiv> heap_ass_ind_on H {lc. \<exists>n. lc = Lc n}"

context encapsulated_module
begin

inductive modifies :: "cl list \<Rightarrow> e list \<Rightarrow> var \<Rightarrow> bool" where
"\<lbrakk>(modifies fs [e] v) \<or> (modifies fs es v)\<rbrakk> \<Longrightarrow> modifies fs (e#es) v"
| "modifies fs [$Set_local j] (Lc j)"
| "\<lbrakk>modifies fs [$Set_local j] v\<rbrakk> \<Longrightarrow> modifies fs [$Tee_local j] v"
| "modifies fs [$Set_global j] (Gl j)"
| "\<lbrakk>j \<ge> length (inst.globs i)\<rbrakk> \<Longrightarrow> modifies fs [$Set_global j] v"
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

lemma modset_set_local1:
  assumes "v \<in> modset fs [$Set_local j]"
  shows "v = Lc j"
  using assms
  apply (induction fs "[$Set_local j]" v rule: modset_induct)
  apply (auto dest: modset_emp)
  done

lemma modset_set_local: "modset fs [$Set_local j] = {Lc j}"
  using modset_set_local1 modset_def modifies.intros(2)
  by fastforce

lemma modset_set_global1:
  assumes "v \<in> modset fs [$Set_global j]"
          "j < length (inst.globs i)"
  shows "v = Gl j"
  using assms
  apply (induction fs "[$Set_global j]" v rule: modset_induct)
  apply (auto dest: modset_emp)
  done

lemma modset_set_global:
  assumes "j \<ge> length (inst.globs i)"
  shows "modset fs [$Set_global j] = UNIV"
  using modset_def modifies.intros(5) assms
  by fastforce

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
      by (metis modset_block modset_intros(12))
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
  apply (auto simp add: split: var.splits if_splits)
  done

lemma var_st_eq_set_local_differ:
  assumes "reifies_glob (s.globs s) (inst.globs i) var_st"
          "reifies_loc (vi @ [v] @ vs) var_st"
          "snd (snd var_st) = lvar_st"
          "reifies_glob (s.globs s) (inst.globs i) var_st'"
          "reifies_loc (vi @ [v'] @ vs) var_st'"
          "snd (snd var_st') = lvar_st"
  shows "var_st_differ_on var_st {Lc (length vi)} var_st'"
  using assms
  unfolding var_st_differ_on_def reifies_loc_def reifies_glob_def var_st_agree_def var_st_get_global_def
            var_st_get_lvar_def var_st_get_local_def
  apply (cases var_st)
  apply (cases var_st')
  apply (fastforce dest: set_local_access split: var.splits if_splits)
  done

lemma set_local_differ:
  assumes "x1 < length (inst.globs i)"
          "j < length (inst.globs i)"
          "x1 \<noteq> j"
          "(inst.globs i ! j) < length (s.globs s)"
          "(inst.globs i ! x1) < length (s.globs s)"
  shows "s.globs s ! (inst.globs i ! x1) =
          s.globs
            (s\<lparr>s.globs := s.globs s
                    [(inst.globs i ! j) :=
     (s.globs s ! (inst.globs i ! j))\<lparr>g_val := v\<rparr>]\<rparr>) !
           (inst.globs i ! x1)"
  using assms encapsulated_inst_globs
  by auto

lemma var_st_set_global_differ:
  assumes "supdate_glob s i j v = s'"
          "j < length (inst.globs i)"
          "reifies_func (s.funcs s) (inst.funcs i) fs"
          "reifies_glob (s.globs s) (inst.globs i) var_st"
          "reifies_loc vs var_st"
          "snd (snd var_st) = lvar_st"
          "reifies_glob (s.globs s') (inst.globs i) var_st'"
          "reifies_loc vs var_st'"
          "snd (snd var_st') = lvar_st"
  shows "var_st_differ_on var_st {Gl j} var_st'"
  using assms
  unfolding var_st_differ_on_def reifies_loc_def reifies_glob_def var_st_agree_def var_st_get_global_def
            var_st_get_lvar_def var_st_get_local_def supdate_glob_def sglob_ind_def supdate_glob_s_def
  apply (cases var_st)
  apply (cases var_st')
  apply (simp split: var.splits if_splits)
  apply (metis encapsulated_inst_globs nth_list_update_neq s.ext_inject s.surjective s.update_convs(4))
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
  thus ?case
    using var_st_eq_set_local_differ modset_set_local
    by (metis modset_intros(1) var_st_differ_on_def)
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
  show ?case
  proof (cases "j < length (inst.globs i)")
    case True
    show ?thesis
      using var_st_set_global_differ[OF set_global(1) True set_global(2,3,4,5,6,7,8)] modset_set_global1
      by (metis modset_intros(1,4) singletonD var_st_differ_on_def)
  next
    case False
    thus ?thesis
      by (meson modset_intros(1) modset_intros(5) not_le_imp_less var_st_differ_on_def)
  qed
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
    using reduce_to_funcs[OF seq_value(1)] seq_value(7)
    by simp
  have "\<forall>gn<length (inst.globs i).
       inst.globs i ! gn
       < length (s.globs s)"
    using seq_value(8)
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
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  thus ?case
    by (metis self_append_conv var_st_differ_on_arb_app3)
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    by (metis append_self_conv2 var_st_differ_on_arb_app3)
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

definition emp :: "heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "emp h v_st \<equiv> h = (Map.empty,None)"

definition args_ass :: "'a stack_ass \<Rightarrow> nat \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "args_ass St n v_st \<equiv> (length St = n \<and> (\<forall>i < n. pred_option_Some (\<lambda>v. (St!i) v v_st) (var_st_get_local v_st i)))"

definition zeros_ass :: "nat \<Rightarrow> t list \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "zeros_ass n ts v_st \<equiv> (\<forall>i < (length ts). (var_st_get_local v_st (i+n)) = Some (bitzero (ts!i)))"

definition is_v :: "v \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_v v stack_v v_st \<equiv> v = stack_v"

definition is_lvs :: "lvar list \<Rightarrow> t \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvs lvs t v v_st \<equiv> \<exists>bs. list_all2 (\<lambda>lv b. var_st_get_lvar v_st lv = Some (V_b b)) lvs bs \<and>
                              (wasm_deserialise bs t) = v"

definition is_lvs_packed :: "lvar list \<Rightarrow> t \<Rightarrow> sx \<Rightarrow> nat \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvs_packed lvs t sx l v v_st \<equiv> \<exists>bs. list_all2 (\<lambda>lv b. var_st_get_lvar v_st lv = Some (V_b b)) lvs bs \<and>
                                          (wasm_deserialise ((sign_extend sx l bs)) t) = v"

definition is_lvar :: "lvar \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar lv v v_st \<equiv> var_st_get_lvar v_st lv = Some (V_p v)"

definition is_lvar_t :: "lvar \<Rightarrow> t \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_t lv t v v_st \<equiv> var_st_get_lvar v_st lv = Some (V_p v) \<and> (typeof v = t)"

definition is_lvar_unop :: "lvar \<Rightarrow> unop \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_unop lv op v v_st \<equiv> \<exists>v'. var_st_get_lvar v_st lv = Some (V_p v') \<and> v = (app_unop op v')"

definition is_lvar_testop :: "lvar \<Rightarrow> testop \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_testop lv op v v_st \<equiv> \<exists>v'. var_st_get_lvar v_st lv = Some (V_p v') \<and> v = (app_testop op v')"

definition can_lvar_binop :: "lvar \<Rightarrow> lvar \<Rightarrow> binop \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "can_lvar_binop lv1 lv2 op h v_st \<equiv> (emp h v_st) \<and> (\<exists>v1 v2. var_st_get_lvar v_st lv1 = Some (V_p v1) \<and> var_st_get_lvar v_st lv2 = Some (V_p v2) \<and> (\<exists>v. Some v = (app_binop op v1 v2)))"

definition is_lvar_binop :: "lvar \<Rightarrow> lvar \<Rightarrow> binop \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_binop lv1 lv2 op v v_st \<equiv> \<exists>v1 v2. var_st_get_lvar v_st lv1 = Some (V_p v1) \<and> var_st_get_lvar v_st lv2 = Some (V_p v2) \<and> Some v = (app_binop op v1 v2)"

definition is_lvar_relop :: "lvar \<Rightarrow> lvar \<Rightarrow> relop \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_relop lv1 lv2 op v v_st \<equiv> \<exists>v1 v2. var_st_get_lvar v_st lv1 = Some (V_p v1) \<and> var_st_get_lvar v_st lv2 = Some (V_p v2) \<and> v = (app_relop op v1 v2)"

definition can_lvar_convert :: "lvar \<Rightarrow> t \<Rightarrow> sx option \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "can_lvar_convert lv t sx h v_st \<equiv> (emp h v_st) \<and> (\<exists>v'. var_st_get_lvar v_st lv = Some (V_p v') \<and> (\<exists>v. Some v = cvt t sx v'))"

definition is_lvar_convert :: "lvar \<Rightarrow> t \<Rightarrow> sx option \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_convert lv t sx v v_st \<equiv> \<exists>v'. var_st_get_lvar v_st lv = Some (V_p v') \<and> Some v = cvt t sx v'"

definition is_lvar_reinterpret :: "lvar \<Rightarrow> t  \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_reinterpret lv t v v_st \<equiv> \<exists>v'. var_st_get_lvar v_st lv = Some (V_p v') \<and> v = (wasm_deserialise (bits v') t)"

definition local_is_lvar :: "nat \<Rightarrow> lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "local_is_lvar j lv h v_st \<equiv> (emp h v_st) \<and> var_st_get_lvar v_st lv = map_option V_p (var_st_get_local v_st j)"

definition global_is_lvar :: "nat \<Rightarrow> lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "global_is_lvar j lv h v_st \<equiv> (emp h v_st) \<and> var_st_get_lvar v_st lv = map_option (\<lambda>g. V_p (g_val g)) (var_st_get_global v_st j)"

definition is_lvar32 :: "lvar \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar32 lv v v_st \<equiv> var_st_get_lvar v_st lv = Some (V_p v) \<and> typeof v = T_i32"

definition is_lvar32_zero :: "lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar32_zero lv h v_st \<equiv> (emp h v_st) \<and> (\<exists>n. var_st_get_lvar v_st lv = Some (V_p (ConstInt32 n)) \<and> int_eq n 0)"

definition is_lvar32_n :: "lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar32_n lv h v_st \<equiv> (emp h v_st) \<and> (\<exists>n. var_st_get_lvar v_st lv = Some (V_p (ConstInt32 n)) \<and> int_ne n 0)"

definition is_lvar32_eq_n :: "lvar \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar32_eq_n lv n h v_st \<equiv> (emp h v_st) \<and> (\<exists>c. var_st_get_lvar v_st lv = Some (V_p (ConstInt32 c)) \<and> nat_of_int c = n)"

definition is_lvar32_geq_n :: "lvar \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar32_geq_n lv n h v_st \<equiv> (emp h v_st) \<and> (\<exists>c. var_st_get_lvar v_st lv = Some (V_p (ConstInt32 c)) \<and> nat_of_int c \<ge> n)"

definition is_lvar32_minus_one :: "lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar32_minus_one lv h v_st \<equiv> (emp h v_st) \<and> var_st_get_lvar v_st lv = Some (V_p (ConstInt32 int32_minus_one))"

definition lvar_is_lvar_and_lvar32_0 :: "lvar \<Rightarrow> lvar \<Rightarrow> lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "lvar_is_lvar_and_lvar32_0 lv1 lv2 lv32 h v_st \<equiv> (emp h v_st) \<and> (\<exists>v. var_st_get_lvar v_st lv1 = Some (V_p v) \<and>
                                                                       var_st_get_lvar v_st lv2 = Some (V_p v) \<and>
                                                                       is_lvar32_zero lv32 h v_st)"

definition lvar_is_lvar_and_lvar32_n :: "lvar \<Rightarrow> lvar \<Rightarrow> lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "lvar_is_lvar_and_lvar32_n lv1 lv2 lv32 h v_st \<equiv> (emp h v_st) \<and> (\<exists>v. var_st_get_lvar v_st lv1 = Some (V_p v) \<and>
                                                                         var_st_get_lvar v_st lv2 = Some (V_p v) \<and>
                                                                         is_lvar32_n lv32 h v_st)"

definition is_lvar_len :: "lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_lvar_len lv h v_st \<equiv> let (h_raw,l_opt) = h in
                            h_raw = Map.empty \<and> pred_option_Some (\<lambda>l. var_st_get_lvar v_st lv = Some (V_n l)) l_opt"

definition is_i32_of_lvar :: "lvar \<Rightarrow> v \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_i32_of_lvar lv v v_st \<equiv> \<exists>vnat. var_st_get_lvar v_st lv = Some (V_n vnat) \<and> v = (ConstInt32 (int_of_nat vnat))"

definition lvar_is_i32_of_lvar :: "lvar \<Rightarrow> lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "lvar_is_i32_of_lvar lv32 lv h v_st \<equiv> (emp h v_st) \<and> (\<exists>vnat. var_st_get_lvar v_st lv = Some (V_n vnat) \<and> var_st_get_lvar v_st lv32 = Some (V_p (ConstInt32 (int_of_nat vnat))))"

definition make_pages where
  "make_pages old_l l \<equiv> map_of (zip [(old_l* Ki64)..<(l* Ki64)] (replicate ((l* Ki64) - (old_l* Ki64)) (0::byte)))"

lemma make_pages_dom_ran:
  assumes "h_raw = make_pages old_l l"
  shows "dom h_raw = {n::nat. (old_l * Ki64) \<le> n \<and> n < (l * Ki64)}"
        "\<forall>n \<in> ran h_raw. n = (0::byte)"
proof -
  have 1:"length [(old_l* Ki64)..<(l* Ki64)] = length (replicate ((l* Ki64) - (old_l* Ki64)) (0::byte))"
    by auto
  have 2:"distinct [(old_l* Ki64)..<(l* Ki64)]"
    by auto
  show "dom h_raw = {n::nat. (old_l * Ki64) \<le> n \<and> n < (l * Ki64)}"
       "\<forall>n \<in> ran h_raw. n = (0::byte)"
    using dom_map_of_zip[OF 1] ran_map_of_zip[OF 1 2] assms
    unfolding make_pages_def
    by auto
qed

definition make_bs_t where
  "make_bs_t ind n bs \<equiv> map_of (zip [ind..<(ind+n)] bs)"

lemma make_bs_t_dom_ran:
  assumes "h_raw = make_bs_t ind n bs"
          "n = length bs"
  shows "dom h_raw = {k::nat. ind \<le> k \<and> k < ind+n}"
        "\<forall>k \<in> dom h_raw. h_raw k = Some (bs!(k-ind))"
proof -
  have 1:"length [ind..<(ind+n)] = length bs"
    using assms(2)
    by auto
  have 2:"distinct [ind..<(ind+n)]"
    by auto
  show "dom h_raw = {k::nat. ind \<le> k \<and> k < ind+n}"
        "\<forall>k \<in> dom h_raw. h_raw k = Some (bs!(k-ind))"
    using dom_map_of_zip[OF 1] ran_map_of_zip[OF 1 2] assms
    unfolding make_bs_t_def
     apply (simp_all add: in_set_zip)
     apply fastforce
    apply safe
    apply simp
    apply (metis add_diff_cancel_left' add_less_cancel_left le_Suc_ex nth_upt)
    done
qed

definition is_n_locs_from_lvar32_off :: "bytes \<Rightarrow> nat \<Rightarrow> lvar \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_n_locs_from_lvar32_off bs n lv32 off h v_st \<equiv> let (h_raw,l_opt) = h in
                                                l_opt = None \<and>
                                                (\<exists>c. var_st_get_lvar v_st lv32 = Some (V_p (ConstInt32 c)) \<and>
                                                (let k = (nat_of_int c) in
                                                 length bs = n \<and>
                                                 h_raw = make_bs_t (k+off) n bs))"

definition is_n_locs_from_lvar32_off_lvars :: "lvar list \<Rightarrow> nat \<Rightarrow> lvar \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_n_locs_from_lvar32_off_lvars lvs n lv32 off h v_st \<equiv> \<exists>bs. list_all2 (\<lambda>lv b. var_st_get_lvar v_st lv = Some (V_b b)) lvs bs \<and>
                                                                is_n_locs_from_lvar32_off bs n lv32 off h v_st"

definition is_n_locs_from_lvar32_off_lvar :: "lvar \<Rightarrow> nat \<Rightarrow> lvar \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "is_n_locs_from_lvar32_off_lvar lv n lv32 off h v_st \<equiv> \<exists>v. var_st_get_lvar v_st lv = Some (V_p v) \<and>
                                                                is_n_locs_from_lvar32_off (bytes_takefill 0 n (bits v)) n lv32 off h v_st"

definition lvar32_zero_pages_from_lvar_len :: "lvar \<Rightarrow> lvar \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "lvar32_zero_pages_from_lvar_len lv32 lv h v_st \<equiv> let (h_raw,l_opt) = h in
                                                \<exists>l old_l c. l_opt = Some l \<and>
                                                    var_st_get_lvar v_st lv = Some (V_n old_l) \<and>
                                                    (l = old_l + nat_of_int c) \<and>
                                                    var_st_get_lvar v_st lv32 = Some (V_p (ConstInt32 c)) \<and>
                                                    make_pages old_l l = h_raw"

lemma list_all2_bs_unique:
  assumes "list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs"
          "list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs'"
  shows "bs = bs'"
    using assms
    unfolding list_all2_conv_all_nth
    by (simp add: nth_equalityI)

lemma lvar32_zero_pages_from_lvar_len_neq_update:
  assumes "lvar32_zero_pages_from_lvar_len lv1 lv2 h st"
          "lv_arb \<noteq> lv1"
          "lv_arb \<noteq> lv2"
  shows "lvar32_zero_pages_from_lvar_len lv1 lv2 h (var_st_set_lvar st lv_arb v)"
  using assms
  unfolding lvar32_zero_pages_from_lvar_len_def
  by (simp add: lv_neq_update)

inductive inf_triples :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_\<bullet>_ \<tturnstile> _" 60)
      and inf_triple :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> 'a ass \<Rightarrow> e list \<Rightarrow> 'a ass \<Rightarrow> bool" ("_\<bullet>_ \<turnstile> {_}_{_}" 60) where
  "\<Gamma>\<bullet>assms \<turnstile> {P} es {Q} \<equiv> \<Gamma>\<bullet>assms \<tturnstile> {(P,es,Q)}"
| Const:"\<Gamma>\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h emp } [$C v] {[is_v v] \<^sub>s|\<^sub>h emp }"
| Unop:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv] \<^sub>s|\<^sub>h emp } [$Unop t op] {[is_lvar_unop lv op] \<^sub>s|\<^sub>h emp }"
| Testop:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv] \<^sub>s|\<^sub>h emp } [$Testop t op] {[is_lvar_testop lv op] \<^sub>s|\<^sub>h emp }"
| Binop:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv1, is_lvar lv2] \<^sub>s|\<^sub>h can_lvar_binop lv1 lv2 op } [$Binop t op] {[is_lvar_binop lv1 lv2 op] \<^sub>s|\<^sub>h emp }"
| Relop:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv1, is_lvar lv2] \<^sub>s|\<^sub>h emp } [$Relop t op] {[is_lvar_relop lv1 lv2 op] \<^sub>s|\<^sub>h emp }"
| Convert:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar_t lv t1] \<^sub>s|\<^sub>h can_lvar_convert lv t2 sx } [$(Cvtop t2 Convert t1 sx)] {[is_lvar_convert lv t2 sx] \<^sub>s|\<^sub>h emp }"
| Reinterpret:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar_t lv t1] \<^sub>s|\<^sub>h emp } [$(Cvtop t2 Reinterpret t1 None)] {[is_lvar_reinterpret lv t2] \<^sub>s|\<^sub>h emp }"
| Nop:"\<Gamma>\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h emp } [$Nop] {[] \<^sub>s|\<^sub>h emp }"
| Drop:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv] \<^sub>s|\<^sub>h emp } [$Drop] {[] \<^sub>s|\<^sub>h emp }"
| Select:"\<lbrakk>lv_arb \<noteq> lv1; lv_arb \<noteq> lv2; lv_arb \<noteq> lv32\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv1, is_lvar lv2, is_lvar32 lv32] \<^sub>s|\<^sub>h emp } [$Select] {Ex_ass lv_arb ([is_lvar lv_arb] \<^sub>s|\<^sub>h (\<lambda>h st. lvar_is_lvar_and_lvar32_0 lv_arb lv2 lv32 h st \<or> lvar_is_lvar_and_lvar32_n lv_arb lv1 lv32 h st)) }"
| Block:"\<lbrakk>(fs,Q#ls,r)\<bullet>assms \<turnstile> {P} ($*es) {Q}; length tn = n; length tm = m; ass_stack_len P = n; ass_stack_len Q = m\<rbrakk> \<Longrightarrow> (fs,ls,r)\<bullet>assms \<turnstile> {P} [$(Block (tn _> tm) es)] {Q}"
| Loop:"\<lbrakk>(fs,P#ls,r)\<bullet>assms \<turnstile> {P} ($*es) {Q}; length tn = n; length tm = m; ass_stack_len P = n; ass_stack_len Q = m\<rbrakk> \<Longrightarrow> (fs,ls,r)\<bullet>assms \<turnstile> {P} [$(Loop (tn _> tm) es)] {Q}"
| If:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> { St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_n lv) } [$(Block tf es1)] {Q}; \<Gamma>\<bullet>assms \<turnstile> { St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_zero lv) } [$(Block tf es2)] {Q}\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> { St@[is_lvar32 lv] \<^sub>s|\<^sub>h H } [$(If tf es1 es2)] {Q}"
| Get_local:"\<Gamma>\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h local_is_lvar j lv } [$Get_local j] {[is_lvar lv] \<^sub>s|\<^sub>h local_is_lvar j lv }"
| Set_local:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv] \<^sub>s|\<^sub>h emp } [$Set_local j] {[] \<^sub>s|\<^sub>h local_is_lvar j lv }"
| Tee_local:"\<lbrakk> \<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv,is_lvar lv] \<^sub>s|\<^sub>h emp } [$Set_local j] { Q } \<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv] \<^sub>s|\<^sub>h emp } [$Tee_local j] { Q }"
| Get_global:"\<lbrakk>j < length (inst.globs i)\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h global_is_lvar j lv } [$Get_global j] {[is_lvar lv] \<^sub>s|\<^sub>h global_is_lvar j lv }"
| Set_global:"\<lbrakk>j < length (inst.globs i)\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {[is_lvar lv] \<^sub>s|\<^sub>h emp } [$Set_global j] {[] \<^sub>s|\<^sub>h global_is_lvar j lv }"
| Load:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv off } [$(Load t None a off)] {[is_lvs lvs t] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv off }"
| Load_packed:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv off} [$(Load t (Some (tp,sx)) a off)] {[is_lvs_packed lvs t sx (t_length t)] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv off }"
| Store:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar32 lv32, is_lvar lv] \<^sub>s|\<^sub>h (\<lambda>h st. (\<exists>bs. is_n_locs_from_lvar32_off bs (t_length t) lv32 off h st)) } [$(Store t None a off)] {[] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvar lv (t_length t) lv32 off }"
| Store_packed:"\<Gamma>\<bullet>assms \<turnstile> {[is_lvar32 lv32, is_lvar lv] \<^sub>s|\<^sub>h (\<lambda>h st. (\<exists>bs. is_n_locs_from_lvar32_off bs (tp_length tp) lv32 off h st)) } [$(Store t (Some tp) a off)] {[] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvar lv (tp_length tp) lv32 off }"
| Br:"\<lbrakk>j < length ls\<rbrakk> \<Longrightarrow> (fs,ls,r)\<bullet>assms \<turnstile> {ls ! j} [$Br j] { Q }"
| Br_if:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> { St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_n lv) } [$Br j] { Q }\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> { St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H } [$Br_if j] { St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_zero lv) }"
| Br_table:"\<lbrakk>\<forall>jn < (length js). (\<Gamma>\<bullet>assms \<turnstile> { St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_eq_n lv jn) } [$Br (js!jn)] { Q }); (\<Gamma>\<bullet>assms \<turnstile> { St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_geq_n lv (length js)) } [$Br j] { Q })\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> { St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H } [$Br_table js j] { Q }"
| Return:"(fs,ls,Some r')\<bullet>assms \<turnstile> {r'} [$Return] { Q }"
| Size_mem:"\<Gamma>\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h is_lvar_len lv_l} [$Current_memory] {[is_i32_of_lvar lv_l] \<^sub>s|\<^sub>h is_lvar_len lv_l}"
| Grow_mem:"\<lbrakk>lv_arb \<noteq> lv; lv_arb \<noteq> lv_l\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {[is_lvar32 lv] \<^sub>s|\<^sub>h is_lvar_len lv_l} [$Grow_memory] {Ex_ass lv_arb ([is_lvar32 lv_arb] \<^sub>s|\<^sub>h (\<lambda>h v_st. ((lvar32_zero_pages_from_lvar_len lv lv_l \<^emph> lvar_is_i32_of_lvar lv_arb lv_l) h v_st) \<or> ((is_lvar32_minus_one lv_arb \<^emph> is_lvar_len lv_l) h v_st)))}"
| Function:"\<lbrakk>cl = Func_native i (tn _> tm) tls es;
             length St = length tn;
             length St' = length tm;
             stack_ass_ind_on_locals St;
             stack_ass_ind_on_locals St';
             heap_ass_ind_on_locals H;
             heap_ass_ind_on_locals H';
             (fs,[],Some (St' \<^sub>s|\<^sub>h H'))\<bullet>assms \<turnstile> {[] \<^sub>s|\<^sub>h (\<lambda>h v_st. H h v_st \<and> (args_ass St (length tn) v_st) \<and> (zeros_ass (length tn) tls v_st))} [$Block ([] _> tm) es] {St' \<^sub>s|\<^sub>h H'}\<rbrakk>
             \<Longrightarrow> (fs,ls,r)\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} [Callcl cl] {St' \<^sub>s|\<^sub>h H'}"
| Asm:"\<lbrakk>(P, [$Call k], Q) \<in> assms\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} [$Call k] {Q}"
| Seq:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> {P} es {Q}; \<Gamma>\<bullet>assms \<turnstile> {Q} es' {R}\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} es@es' {R}"
| Conseq:"\<lbrakk>(fs,ls',rs')\<bullet>assms \<turnstile> {P'} es {Q'}; \<forall>vs h v_st. (list_all2 (\<lambda>L L'. ass_conseq L L' vs h v_st) ls' ls) \<and> (rel_option (\<lambda>R R'. ass_conseq R R' vs h v_st) rs' rs) \<and> (ass_sat P vs h v_st \<longrightarrow> ass_sat P' vs h v_st) \<and> (ass_sat Q' vs h v_st \<longrightarrow> ass_sat Q vs h v_st)\<rbrakk> \<Longrightarrow> (fs,ls,rs)\<bullet>assms \<turnstile> {P} es {Q}"
| Exists:"\<lbrakk>(fs,ls,rs)\<bullet>assms \<turnstile> {P} es {Q}\<rbrakk> \<Longrightarrow> (fs,(map (\<lambda>l. Ex_ass lv l) ls),(map_option) (\<lambda>l. Ex_ass lv l) rs)\<bullet>assms \<turnstile> {Ex_ass lv P} es {Ex_ass lv Q}"
| Frame:"\<lbrakk>(fs,ls,rs)\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} es {St' \<^sub>s|\<^sub>h H'}; heap_ass_ind_on Hf (modset fs es); (\<forall>ass \<in> (set ls). \<exists>Sa Ha. ass = Sa \<^sub>s|\<^sub>h Ha); pred_option (\<lambda>ass. \<exists>Sa Ha. ass = Sa \<^sub>s|\<^sub>h Ha) rs\<rbrakk> \<Longrightarrow> (fs,map (ass_frame Hf) ls, map_option (ass_frame Hf) rs)\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h (H \<^emph> Hf)} es {St' \<^sub>s|\<^sub>h (H' \<^emph> Hf)}"
| Ext:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} es {St' \<^sub>s|\<^sub>h H'}; stack_ass_ind_on Stf (modset (fst \<Gamma>) es)\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {(Stf @ St) \<^sub>s|\<^sub>h H} es {(Stf @ St') \<^sub>s|\<^sub>h H'}"
| Call:"\<lbrakk>(fs,[],None)\<bullet>specs \<tturnstile> ({(P,c,Q). \<exists>i. (P, [$Call i], Q) \<in> specs \<and> i< length fs \<and> c = [Callcl (fs!i)]}); \<forall>(P,c,Q) \<in> specs. \<exists>i. c = [$Call i] \<and> i < length fs\<rbrakk> \<Longrightarrow> (fs,[],None)\<bullet>({}) \<tturnstile> specs"
| ConjI:"\<forall>(P,es,Q) \<in> specs. (\<Gamma>\<bullet>assms \<turnstile> {P} es {Q}) \<Longrightarrow> \<Gamma>\<bullet>assms \<tturnstile> specs"
| ConjE:"\<lbrakk>\<Gamma>\<bullet>assms \<tturnstile> specs; (P,es,Q) \<in> specs\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} es {Q}"

lemma make_pages_reifies:
  assumes "h  = (make_pages n (n+c),Some (n+c))"
          "\<forall>ind \<in> (dom (fst hf)). ind < mem_length m"
          "(snd hf) = None"
          "mem_length m = n * Ki64"
          "reifies_heap_contents m (fst (heap_merge (Map.empty, Some n) hf))"
          "heap_disj h hf"
  shows "reifies_heap_contents (mem_grow m c) (fst (heap_merge h hf))"
        "reifies_heap_length (mem_grow m c) (snd (heap_merge h hf))"
proof -
  have 0:"mem_length (mem_grow m c) = (n+c) * Ki64"
    using assms(4) mem_grow_length
    by (metis distrib_right)
  hence 1:"\<forall>ind\<in>dom (fst (heap_merge h hf)). ind < mem_length (mem_grow m c)"
    using assms(1,2,4) make_pages_dom_ran[of _ n "n+c"]
    unfolding heap_merge_def
    apply (simp split: prod.splits)
    apply safe
    apply simp
    apply (metis add_leD1 add_mult_distrib2 domI mult.commute not_le)
    done
  have 2:"snd (heap_merge h hf) = Some (n+c)"
    using assms(1,3)
    unfolding heap_merge_def
    by (auto split: prod.splits)
  have "\<forall>ind\<in>dom (fst (heap_merge h hf)).
         fst (heap_merge h hf) ind =
         Some (byte_at (mem_grow m c) ind)"
  proof -
    {
      fix ind
      assume local_assms:"ind\<in>dom (fst (heap_merge h hf))"
      have "fst (heap_merge h hf) ind = Some (byte_at (mem_grow m c) ind)"
      proof (cases "mem_length m > ind")
        case True
        hence"ind\<in>dom (fst hf)"
          using local_assms heap_merge_dom[OF local_assms]
                make_pages_dom_ran assms
          unfolding reifies_heap_contents_def heap_merge_def
          by (auto split: prod.splits)
        thus ?thesis
          using True assms(5,6)
          unfolding heap_disj_def map_disj_def disjnt_def reifies_heap_contents_def
          by (auto simp add: True mem_grow_byte_at_m heap_merge_def split: prod.splits)
      next
        case False
        hence f1:"byte_at (mem_grow m c) ind = 0"
          using mem_grow_byte_at_m_n 1 local_assms
          by auto
        have "ind\<in>dom (fst h)"
             "\<forall>n \<in> ran (fst h). n = (0::byte)"
          using local_assms heap_merge_dom[OF local_assms] False
                make_pages_dom_ran assms
          unfolding reifies_heap_contents_def heap_merge_def
          by (auto split: prod.splits)
        hence "(fst (heap_merge h hf)) ind = Some (0::byte)"
          using heap_disj_merge_maps1[OF assms(6)]
          unfolding dom_def ran_def
          by auto
        thus ?thesis
          using f1
          by auto
      qed
    }
    thus ?thesis
      by blast
  qed
  thus "reifies_heap_contents (mem_grow m c) (fst (heap_merge h hf))"
    using 1
    unfolding reifies_heap_contents_def
    by blast
  show "reifies_heap_length (mem_grow m c) (snd (heap_merge h hf))"
    unfolding reifies_heap_length_def
    by (simp add: 0 2)
qed

lemma make_bs_t_length:
  assumes "h = ((make_bs_t (k+off) n bs), None)"
          "n = length bs"
          "reifies_heap_contents m (fst (heap_merge h hf))"
          "n \<ge> 1"
  shows "mem_length m \<ge> (k+off+n)"
proof -
  have "k+off+n-1 \<in> dom (make_bs_t (k + off) n bs)"
    using make_bs_t_dom_ran[OF _ assms(2), of _ "k+off"] assms(4)
    by simp
  hence "mem_length m > (k+off+n-1)"
    using heap_dom_merge assms(1,3,4)
    unfolding reifies_heap_contents_def
    by simp
  thus "mem_length m \<ge> (k+off+n)"
    by simp
qed

lemma make_bs_t_reifies:
  assumes "h = ((make_bs_t (k+off) n bs), None)"
          "n = length bs"
          "heap_disj h hf"
          "reifies_heap_contents m (fst (heap_merge h hf))"
          "reifies_heap_length m (snd (heap_merge h hf))"
          "n \<ge> 1"
  shows "load m k off n = Some bs"
proof -
  obtain h_raw where h_raw_def:"h_raw = (make_bs_t (k+off) n bs)"
    by blast
  hence 1:"mem_length m \<ge> (k+off+n)"
    using make_bs_t_length[OF assms(1,2,4,6)]
    by simp
  have 2:"(read_bytes m (k+off) n) = (map (byte_at m) [(k+off)..<(k+off) + n])"
    using make_bs_t_dom_ran[OF _ assms(2), of _ "k+off"] read_bytes_map 1
    by simp
  {
    fix i
    assume "i < length bs"
    hence "i + k + off \<in> dom h_raw"
      using make_bs_t_dom_ran(1)[OF h_raw_def assms(2)] assms(2)
      by auto
    hence "h_raw (i + k + off) = Some (bs ! i)"
      using make_bs_t_dom_ran(2)[OF h_raw_def assms(2)]
      by simp
    hence "(fst (heap_merge h hf)) (i + k + off) = Some (bs ! i)"
      using assms(3) h_raw_def
      by (simp add: assms(1) heap_disj_merge_maps2 heap_disj_sym heap_merge_disj_sym)
    hence "Rep_mem m ! (k + off + i) = bs ! i"
      using assms(2,4)
      unfolding reifies_heap_contents_def byte_at_def
      apply simp
      apply (metis (no_types, hide_lams) add.commute add.left_commute domIff option.distinct(1) option.sel)
      done
  }
  hence "(map (byte_at m) [(k+off)..<(k+off) + n]) = bs"
    using assms(2,4) make_bs_t_dom_ran[OF h_raw_def assms(2)]
    unfolding list_eq_iff_nth_eq reifies_heap_contents_def byte_at_def
    by simp
  thus ?thesis
    using 1 2
    unfolding load_def read_bytes_def
    by simp
qed

lemma write_bytes_byte_at_outside:
  assumes "mem_length m \<ge> k+l"
          "m' = (write_bytes m k (bytes_takefill 0 l bs))"
          "j < k \<or> (j \<ge> k+l \<and> j < mem_length m)"
  shows "byte_at m' j = byte_at m j"
proof -
  have "mem_length m = mem_length m'"
    using store_length[of m k 0 bs l m'] assms
    unfolding store_def
    by simp
  {
    assume "\<not> j - min (length (Rep_mem m)) k < l"
    assume a1: "j < length (Rep_mem m)"
    assume "k + l \<le> j"
    then have "k \<le> length (Rep_mem m)"
      using a1 by simp
    then have "Rep_mem m ! (k + j - min (length (Rep_mem m)) k) = Rep_mem m ! j"
      by (metis (no_types) Nat.diff_diff_right add.left_neutral add_diff_cancel_left' rev_min_pm1 zero_diff)
  }
  thus ?thesis
    using assms
    unfolding write_bytes_def bytes_takefill_def byte_at_def mem_length_def
    by (auto simp add: Abs_mem_inverse nth_append)
qed

lemma write_bytes_byte_at_inside:
  assumes "mem_length m \<ge> k+l"
          "m' = (write_bytes m k (bytes_takefill 0 l bs))"
          "j \<ge> k \<and> j < k+l"
        shows "byte_at m' j = (bytes_takefill 0 l bs)!(j-k)"
proof -
  have 0:"min (length (Rep_mem m)) k = k"
    using assms(1)
    unfolding mem_length_def
    by simp
  show ?thesis
    using assms
    unfolding mem_length_def write_bytes_def bytes_takefill_def byte_at_def
    by (auto simp add: Abs_mem_inverse nth_append 0)
qed

lemma make_bs_t_store_reifies:
  assumes "h = ((make_bs_t k l bs'), None)"
          "l = length bs'"
          "heap_disj h hf"
          "reifies_heap_contents m (fst (heap_merge h hf))"
          "reifies_heap_length m (snd (heap_merge h hf))"
          "mem_length m \<ge> k+l"
          "m' = (write_bytes m k (bytes_takefill 0 l bs))"
          "h' = ((make_bs_t k l (bytes_takefill 0 l bs)), None)"
  shows "heap_disj h' hf"
        "reifies_heap_contents m' (fst (heap_merge h' hf))"
        "reifies_heap_length m' (snd (heap_merge h' hf))"
proof -
  have 2:"mem_length m = mem_length m'"
    using store_length[of m k 0 bs l m'] assms(6,7)
    unfolding store_def
    by simp
  thus "reifies_heap_length m' (snd (heap_merge h' hf))"
    using assms(1,5,8)
    unfolding reifies_heap_length_def heap_merge_def Let_def
    by (simp split: prod.splits)
  have 0:"l = length (bytes_takefill 0 l bs)"
    unfolding bytes_takefill_def
    by simp
  have 1:"dom (fst h) = dom (fst h')"
    using assms(1,8) make_bs_t_dom_ran(1)[OF _ assms(2)] make_bs_t_dom_ran(1)[OF _ 0]
    by simp
  thus h'_disj:"heap_disj h' hf"
    using assms(1,3,8)
    unfolding heap_disj_def map_disj_def
    by simp
  hence 3:"dom (fst (heap_merge h hf)) = dom (fst (heap_merge h' hf))"
    using 1 heap_dom_merge_eq
    by blast
  have 4:"\<And>ind b. fst (heap_merge h hf) ind = Some b \<Longrightarrow> ind < mem_length m \<and> b = byte_at m ind"
    using assms(4)
    unfolding reifies_heap_contents_def
    by (metis domI option.sel)
  have "\<And>ind b. fst (heap_merge h' hf) ind = Some b \<Longrightarrow> b = byte_at m' ind"
  proof -
    {
      fix ind b
      assume local_assms:"fst (heap_merge h' hf) ind = Some b"
      hence loc_1:"ind \<in> dom (fst (heap_merge h' hf))"
        by (simp add: domI)
      hence "ind < mem_length m"
        using assms(4) 3
        unfolding reifies_heap_contents_def
        by auto
      then consider (1) "ind \<ge> k \<and> ind < k+l" | (2) "ind < k \<or> (ind \<ge> k+l \<and> ind < mem_length m)"
        using not_le_imp_less
        by blast
      hence "b = byte_at m' ind"
      proof cases
        case 1
        hence a1_1:"ind \<in> dom (fst h')"
          using local_assms assms(8) make_bs_t_dom_ran[OF _ 0] heap_merge_dom[OF loc_1]
          by auto
        show ?thesis
          using write_bytes_byte_at_inside[OF assms(6,7) 1] heap_dom_merge
          apply simp
          apply clarify
          apply (metis 0 a1_1 assms(8) fst_conv h'_disj heap_disj_merge_maps2 heap_disj_sym heap_merge_disj_sym local_assms make_bs_t_dom_ran(2) option.inject)
          done
      next
        case 2
        hence "ind \<in> dom (fst hf)"
          using local_assms assms(8) make_bs_t_dom_ran[OF _ 0] heap_merge_dom[OF loc_1]
          by auto
        thus ?thesis
          using write_bytes_byte_at_outside[OF assms(6,7) 2] 4 heap_dom_merge
          apply simp
          apply clarify
          apply (metis h'_disj assms(3) heap_disj_merge_maps1 heap_disj_sym heap_merge_disj_sym local_assms)
          done
      qed
    }
    thus "\<And>ind b. fst (heap_merge h' hf) ind = Some b \<Longrightarrow> b = byte_at m' ind"
      by blast
  qed
  thus "reifies_heap_contents m' (fst (heap_merge h' hf))"
    using assms(4) 2 3
    unfolding reifies_heap_contents_def
    by auto
qed

lemma make_bs_t_packed_reifies:
  assumes "h = ((make_bs_t (k+off) np bs), None)"
          "np = length bs"
          "heap_disj h hf"
          "reifies_heap_contents m (fst (heap_merge h hf))"
          "reifies_heap_length m (snd (heap_merge h hf))"
          "np \<ge> 1"
  shows "load_packed sx m k off np n = Some (sign_extend sx n bs)"
  using make_bs_t_reifies[OF assms(1,2,3,4,5,6)]
  unfolding load_packed_def
  by simp

lemma lvar32_zero_pages_from_lvar_len_reifies:
  assumes "ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_lvar_len lv_l) [(ConstInt32 c)] h st"
          "heap_disj h hf"
          "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
          "smem_ind s i = Some j"
          "((mem s)!j) = m"
          "mem_size m = n"
          "mem_grow m (nat_of_int c) = mem'"
          "lv_arb \<noteq> lv"
          "lv_arb \<noteq> lv_l"
  shows "\<exists>h'. ass_sat (Ex_ass lv_arb ([is_lvar32 lv_arb] \<^sub>s|\<^sub>h (\<lambda>h v_st. ((lvar32_zero_pages_from_lvar_len lv lv_l \<^emph> lvar_is_i32_of_lvar lv_arb lv_l) h v_st) \<or> ((is_lvar32_minus_one lv_arb \<^emph> is_lvar_len lv_l) h v_st)))) [ConstInt32 (int_of_nat n)] h' st
              \<and> heap_disj h' hf
              \<and> reifies_s (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>) i (heap_merge h' hf) st (fst \<Gamma>)"
proof -
  have 0:"\<exists>n'. var_st_get_lvar st lv_l = Some (V_n n') \<and> h = (Map.empty, Some n')"
         "var_st_get_lvar st lv = Some (V_p (ConstInt32 c))"
    using assms(1)
    by (auto simp add: is_lvar32_def is_lvar_len_def stack_ass_sat_def pred_option_Some_def typeof_def)
  hence 1:"h = (Map.empty, Some n)"
          "snd hf = None"
          "\<forall>ind \<in> (dom (fst h)). ind < mem_length m"
          "\<forall>ind \<in> (dom (fst hf)). ind < mem_length m"
          "mem_length m = n * Ki64"
    using assms(2,3,4,5,6)
    unfolding smem_ind_def reifies_s_def reifies_heap_def
    by (auto simp add: Option.is_none_def option_disj_def reifies_heap_length_def Ki64_def
                       reifies_heap_contents_def heap_merge_def heap_disj_def mem_size_def
             split: prod.splits if_splits)
  obtain h' where h'_def:"lvar32_zero_pages_from_lvar_len lv lv_l h' st"
    using 0 1
    unfolding lvar32_zero_pages_from_lvar_len_def
    by auto
  hence 2:"fst h' = (make_pages n (n+(nat_of_int c)))"
          "snd h' = Some (n+(nat_of_int c))"
          "h' = ((make_pages n (n+(nat_of_int c))), Some (n+(nat_of_int c)))"
    using 0 1
    unfolding lvar32_zero_pages_from_lvar_len_def
    by auto
  hence 3:"heap_disj h' hf"
    using 1 make_pages_dom_ran[OF 2(1)] not_less[of _ "(n + Wasm_Base_Defs.nat_of_int c) * Ki64"]
    unfolding Ki64_def lvar32_zero_pages_from_lvar_len_def mem_length_def heap_disj_def map_disj_def disjnt_def
    apply (simp add: option_disj_def Option.is_none_def)
    apply safe
    apply (metis domIff not_less option.distinct(1))
    done
  have "ass_sat ([is_i32_of_lvar lv_l] \<^sub>s|\<^sub>h (lvar32_zero_pages_from_lvar_len lv lv_l)) [ConstInt32 (int_of_nat n)] h' st"
    using 2 h'_def 0 1
    by (simp add: is_lvar32_def stack_ass_sat_def is_i32_of_lvar_def)
  hence "ass_sat ([is_lvar32 lv_arb] \<^sub>s|\<^sub>h (\<lambda>h v_st. ((lvar32_zero_pages_from_lvar_len lv lv_l \<^emph> lvar_is_i32_of_lvar lv_arb lv_l) h v_st))) [ConstInt32 (int_of_nat n)] h' (var_st_set_lvar st lv_arb (V_p (ConstInt32 (int_of_nat n))))"
    by (auto simp add: typeof_def lvar32_zero_pages_from_lvar_len_neq_update assms(8,9) lv_neq_update lv_eq_update stack_ass_sat_def is_i32_of_lvar_def
                       is_lvar32_def lvar_is_i32_of_lvar_def sep_conj_def lvar32_zero_pages_from_lvar_len_def heap_disj_def map_disj_def disjnt_def
                       option_disj_def emp_def heap_merge_def
             split: prod.splits)
  hence "ass_sat (Ex_ass lv_arb ([is_lvar32 lv_arb] \<^sub>s|\<^sub>h (\<lambda>h v_st. ((lvar32_zero_pages_from_lvar_len lv lv_l \<^emph> lvar_is_i32_of_lvar lv_arb lv_l) h v_st) \<or> ((is_lvar32_minus_one lv_arb \<^emph> is_lvar_len lv_l) h v_st)))) [ConstInt32 (int_of_nat n)] h' st"
    by fastforce
  moreover
  have "reifies_heap_contents (mem_grow (s.mem s ! j) (Wasm_Base_Defs.nat_of_int c)) (fst (heap_merge h' hf))"
       "reifies_heap_length (mem_grow m (Wasm_Base_Defs.nat_of_int c)) (snd (heap_merge h' hf))"
    using make_pages_reifies[OF 2(3) 1(4,2,5) _ 3]
    by (metis 1(1) assms(3,4,5) option.sel reifies_heap_def reifies_s_def smem_ind_def)+
  ultimately
  show ?thesis
    using 3 assms(3)
    unfolding reifies_s_def
    apply simp
    apply (metis assms(4,5,7) length_list_update nth_list_update_eq option.sel prod.exhaust_sel
                 reifies_heap_def smem_ind_def)
    done
qed

lemma is_n_locs_from_lvar32_off_reifies:
  assumes "ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv32 off) [(ConstInt32 c)] h st"
          "list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs"
  shows "ass_sat ([is_lvs lvs t] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv32 off) [(wasm_deserialise bs t)] h st"
proof -
  have "\<forall>bs'. list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs' \<longrightarrow> bs = bs'"
    using assms(2)
    unfolding list_all2_conv_all_nth
    by (simp add: nth_equalityI)
  hence "is_lvs lvs t (wasm_deserialise bs t) st"
    using assms(2)
    unfolding is_lvs_def
    by metis
  thus ?thesis
    using assms
    by (simp add: stack_ass_sat_def)
qed

lemma is_n_locs_from_lvar32_off_packed_reifies:
  assumes "ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv32 off) [(ConstInt32 c)] h st"
          "list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs"
  shows "ass_sat ([is_lvs_packed lvs t sx (t_length t)] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv32 off) [(wasm_deserialise (sign_extend sx (t_length t) bs) t)] h st"
proof -
  have "\<forall>bs'. list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs' \<longrightarrow> bs = bs'"
    using assms(2)
    unfolding list_all2_conv_all_nth
    by (simp add: nth_equalityI)
  hence "is_lvs_packed lvs t sx (t_length t) (wasm_deserialise (sign_extend sx (t_length t) bs) t) st"
    using assms(2)
    unfolding is_lvs_packed_def
    by metis
  thus ?thesis
    using assms
    by (simp add: stack_ass_sat_def)
qed

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

lemma ass_sat_ind_on_locals:
  assumes "ass_sat (St \<^sub>s|\<^sub>h H) ves h (gs, locs, lvs)"
          "stack_ass_ind_on_locals St"
          "heap_ass_ind_on_locals H"
  shows "ass_sat (St \<^sub>s|\<^sub>h H) ves h (gs, locs', lvs)"
proof -
  have "stack_ass_sat St ves (gs, locs', lvs)"
    using assms(1,2)
    unfolding ass_sat.simps stack_ass_ind_on_locals_def stack_ass_ind_on_def
              var_st_differ_on_def var_st_agree_def var_st_get_global_def
              var_st_get_local_def var_st_get_lvar_def
    by (fastforce split: var.splits if_splits)
  moreover
  have  "H h (gs, locs', lvs)"
  proof -
    {
    assume a1: "\<forall>a b aa ab ba ac ad bb. (\<forall>var. (\<forall>x1. (x1 < length aa \<longrightarrow> (x1 < length ac \<longrightarrow> var = Gl x1 \<longrightarrow> aa ! x1 = ac ! x1) \<and> (var = Gl x1 \<longrightarrow> x1 < length ac)) \<and> (var = Gl x1 \<longrightarrow> x1 < length aa \<or> \<not> x1 < length ac)) \<and> (\<forall>x3. var = Lv x3 \<longrightarrow> ba x3 = bb x3)) \<longrightarrow> H (a, b) (aa, ab, ba) = H (a, b) (ac, ad, bb)"
      assume a2: "H h (gs, locs, lvs)"
      have "\<And>p gs vs f vsa. \<not> H p (gs, vs, f) \<or> H p (gs, vsa, f)"
        using a1 by fastforce
    }
    note a = this
    show ?thesis
      using assms(1,3)
      unfolding ass_sat.simps heap_ass_ind_on_locals_def heap_ass_ind_on_def
                var_st_differ_on_def var_st_agree_def var_st_get_global_def
                var_st_get_local_def var_st_get_lvar_def
      apply (simp split: var.splits if_splits)
      apply (insert a)
      apply blast
      done
  qed
  ultimately
  show ?thesis
    by simp
qed

lemma stack_ass_to_heap_ass:
  assumes "stack_ass_sat St ves (gs, (ves@n_zeros tls), lvs)"
  shows "(args_ass St (length St) (gs, (ves@n_zeros tls), lvs)) \<and> (zeros_ass (length St) tls (gs, (ves@n_zeros tls), lvs))"
  using assms
  unfolding stack_ass_sat_def args_ass_def zeros_ass_def n_zeros_def list_all2_conv_all_nth
            pred_option_Some_def pred_option_def var_st_get_local_def
  apply (simp split: if_splits)
  apply (metis add_diff_cancel_right' not_add_less2 nth_append nth_map)
  done

lemma ass_sat_local:
  assumes "ass_sat (St \<^sub>s|\<^sub>h H) ves h (gs, locs, lvs)"
          "stack_ass_ind_on_locals St"
          "heap_ass_ind_on_locals H"
        shows "(ass_sat ([] \<^sub>s|\<^sub>h (\<lambda>h vl_st. H h vl_st \<and> (args_ass St (length St) vl_st) \<and> (zeros_ass (length St) tls vl_st))) [] h (gs, (ves@n_zeros tls), lvs))"
proof -
  have 1:"stack_ass_sat St ves (gs, ves @ n_zeros tls, lvs)"
         "H h (gs, ves @ n_zeros tls, lvs)"
    using ass_sat_ind_on_locals[OF assms, of "ves @ n_zeros tls"]
    by simp_all
  show ?thesis
    using stack_ass_to_heap_ass[OF 1(1)] 1(2)
    by (simp add: stack_ass_sat_def)
qed

definition ass_wf_P where
  "ass_wf_P lvar_st ret \<Gamma> labs hf P s locs vcs \<equiv> \<exists>st h. ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P"
 (*
res_wf lvar_st' \<Gamma> res locs' s' hf vcsf Q 
*)
definition res_wf_Q where
  "res_wf_Q lvar_st' \<Gamma> hf Q s' locs' vcsf res \<equiv> res_wf lvar_st' \<Gamma> res locs' s' hf vcsf Q"

lemma res_wf_Q_value_ext:
  assumes "res_wf_Q lvar_st' \<Gamma> hf Q s' locs' vcsf (RValue rvs)"
  shows "res_wf_Q lvar_st' \<Gamma> hf Q s' locs' (vcsf'@vcsf) (RValue (vcsf'@rvs))"
  using assms
  unfolding res_wf_Q_def res_wf_def
  by simp

lemma res_wf_Q_nonvalue_ext:
  assumes "res_wf_Q lvar_st' \<Gamma> hf Q s' locs' vcsf res"
          "\<And>rvs. res \<noteq> RValue rvs"
  shows "res_wf_Q lvar_st' \<Gamma> hf Q s' locs' (vcsf'@vcsf) res"
  using assms
  unfolding res_wf_Q_def res_wf_def
  by (fastforce split: res_b.splits prod.splits)

definition P_reduce where
  "P_reduce P Q b_es k \<Gamma> \<equiv> \<forall>s vs vcs s' vs' res. (P s vs vcs \<longrightarrow> ((s,vs,($$*vcs) @ ($*b_es)) \<Down>k{\<Gamma>} (s',vs',res)) \<longrightarrow> ((\<forall>rvs. ((res = RBreak 0 rvs) \<longrightarrow> P s' vs' rvs)) \<and> ((\<nexists>rvs. res = RBreak 0 rvs) \<longrightarrow> Q s' vs' [] res)))"

lemma reduce_to_n_loop:
  assumes "(s,locs,es) \<Down>k{(labs, ret, i)} (s',locs',res)"
          "es = ($$*vcsf) @ ($$*vcs) @ [$(Loop (t1s _> t2s) b_es)] \<or>
           es = ($$*vcsf) @ [(Label n [$(Loop (t1s _> t2s) b_es)] (($$*vcs)@ ($*b_es)))]"
          "length ($$*vcs) = n"
          "length t1s = n"
          "length t2s = m"
          "ass_stack_len P = n"
          "ass_stack_len Q = m"
          "ass_wf lvar_st ret (fs,P#ls,r) (n#labs) locs s hf st h vcs P"
          "(fs,P#ls,r) \<Turnstile>_k {P} ($*b_es) {Q}"
  shows "res_wf lvar_st (fs,ls,r) res locs' s' hf vcsf Q"
  using assms
proof (induction "(s,locs,es)" k "(labs, ret, i)" "(s',locs',res)" arbitrary: s locs s' locs' res vcs vcsf es labs ls st h rule: reduce_to_n.induct)
  case (const_value s vs es k s' vs' res ves)
  then show ?case sorry
next
  case (label_value s vs es k n' labs s' vs' res les)
  have les_is:"vcsf = []" "n' = n" "les  = [$Loop (t1s _> t2s) b_es]" "es = (($$* vcs) @ ($* b_es))"
    using label_value(3)
    by auto
  hence 1:"(s, vs, ($$* []) @ ($$* vcs) @ ($* b_es)) \<Down>k{(n # labs, ret, i)} (s', vs', RValue res)"
    using label_value(1)
    by auto
  show ?case
    using res_wf_valid_triple_n_intro[OF label_value(10,9) 1] les_is(1)
    unfolding res_wf_def
    by simp
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  then show ?case sorry
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  then show ?case sorry
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  then show ?case sorry
next
  case (label_trap s vs es k n' labs s' vs' les)
  have "vcsf = []" "n' = n" "les  = [$Loop (t1s _> t2s) b_es]" "es = (($$* vcs) @ ($* b_es))"
    using label_trap(3)
    by auto
  hence 1:"(s, vs, ($$* []) @ ($$* vcs) @ ($* b_es)) \<Down>k{(n # labs, ret, i)} (s', vs', RTrap)"
    using label_trap(1)
    by auto
  show ?case
    using res_wf_valid_triple_n_intro[OF label_trap(10,9) 1]
    unfolding res_wf_def
    by simp
next
  case (label_break_suc s vs es k n' labs s' vs' bn bvs les)
  have "vcsf = []" "n' = n" "les  = [$Loop (t1s _> t2s) b_es]" "es = (($$* vcs) @ ($* b_es))"
    using label_break_suc(3)
    by auto
  hence 1:"(s, vs, ($$* []) @ ($$* vcs) @ ($* b_es)) \<Down>k{(n # labs, ret, i)} (s', vs', RBreak (Suc bn) bvs)"
    using label_break_suc(1)
    by auto
  show ?case
    using res_wf_valid_triple_n_intro[OF label_break_suc(10,9) 1]
    unfolding res_wf_def
    by simp
next
  case (label_break_nil s vs es k n' labs s'' vs'' bvs les s' vs' res)
  have 0:"reifies_lab (n # labs) (fs, P # ls, r)"
         "reifies_ret ret (fs, P # ls, r)"
    using label_break_nil(11)
    unfolding ass_wf_def
    by simp_all
  have les_is:"vcsf = []" "n' = n" "les  = [$Loop (t1s _> t2s) b_es]" "es = (($$* vcs) @ ($* b_es))"
    using label_break_nil(5)
    by auto
  hence 1:"(s, vs, ($$* []) @ ($$* vcs) @ ($* b_es)) \<Down>k{(n # labs, ret, i)} (s'', vs'', RBreak 0 bvs)"
    using label_break_nil(1)
    by auto
  have res_wf_bvs:"res_wf lvar_st (fs, P # ls, r) (RBreak 0 bvs) vs'' s'' hf [] Q"
    using res_wf_valid_triple_n_intro[OF label_break_nil(12,11) 1]
    by -
  hence 2:"length ($$*bvs) = n"
    using label_break_nil(9) stack_ass_sat_len
    unfolding res_wf_def
    by fastforce
  obtain st'' h'' where st''_def:"ass_wf lvar_st ret (fs, P # ls, r) (n # labs) vs'' s'' hf st'' h'' bvs P"
                                 "snd (snd st'') = lvar_st"
    using 0 res_wf_bvs
    unfolding res_wf_def ass_wf_def
    by fastforce
  thus ?case
    using label_break_nil(4)[OF _ 2 label_break_nil(7,8,9,10) st''_def(1) label_break_nil(12)]
          les_is
    by blast
next
  case (label_return s vs es k n' labs s' vs' rvs les)
  have "vcsf = []" "n' = n" "les  = [$Loop (t1s _> t2s) b_es]" "es = (($$* vcs) @ ($* b_es))"
    using label_return(3)
    by auto
  hence 1:"(s, vs, ($$* []) @ ($$* vcs) @ ($* b_es)) \<Down>k{(n # labs, ret, i)} (s', vs', RReturn rvs)"
    using label_return(1)
    by auto
  show ?case
    using res_wf_valid_triple_n_intro[OF label_return(10,9) 1]
    unfolding res_wf_def
    by simp
qed auto

theorem
  assumes "\<Gamma>\<bullet>assms \<tturnstile> specs"
  shows "(\<Gamma>\<bullet>assms \<TTurnstile>_n specs)"
  using assms
proof(induction arbitrary: n rule:inf_triples.induct)
  case (Const \<Gamma> assms v)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([] \<^sub>s|\<^sub>h emp )::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$C v]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have vcs_is:"vcs = []"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$C v]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 2:"s = s'"
           "locs = locs'"
           "res = RValue (vcsf @ [v])"
      using reduce_to_n_consts[of _ _ "vcsf@[v]"] 1
      by auto
    hence 0:"ass_sat ([is_v v] \<^sub>s|\<^sub>h emp) [v] h st"
      using ass_is(1) 2 ass_is(4)
      apply (cases st)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def
                       var_st_get_lvar_def is_v_def var_st_get_local_def reifies_loc_def
                  split: if_splits)
      done
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_v v] \<^sub>s|\<^sub>h emp)"
      using vcs_is local_assms(1,4) 0 ass_is 2
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Unop \<Gamma> assms lv t op)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Unop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis Suc_length_conv list_exhaust_size_eq0)
      done
    hence 0:"ass_sat ([is_lvar_unop lv op] \<^sub>s|\<^sub>h emp) [app_unop op v] h st"
      using ass_is(1)
      by (simp add: stack_ass_sat_def is_lvar_unop_def list_all2_conv_all_nth is_lvar_def
                    var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C v,$Unop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar_unop lv op] \<^sub>s|\<^sub>h emp)"
      using reduce_to_n_unop[OF 1] vcs_is local_assms(1,4) 0 ass_is
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Testop \<Gamma> assms lv t op)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Testop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis Suc_length_conv list_exhaust_size_eq0)
      done
    hence 0:"ass_sat ([is_lvar_testop lv op] \<^sub>s|\<^sub>h emp) [app_testop op v] h st"
      using ass_is(1)
      by (simp add: stack_ass_sat_def is_lvar_testop_def list_all2_conv_all_nth is_lvar_def
                    var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C v,$Testop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar_testop lv op] \<^sub>s|\<^sub>h emp)"
      using reduce_to_n_testop[OF 1] vcs_is local_assms(1,4) 0 ass_is
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Binop \<Gamma> assms lv1 lv2 op t)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv1, is_lvar lv2] \<^sub>s|\<^sub>h can_lvar_binop lv1 lv2 op)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Binop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv1, is_lvar lv2] \<^sub>s|\<^sub>h can_lvar_binop lv1 lv2 op) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v1 v2 where vcs_is:"vcs = [v1, v2]"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def is_lvar_def var_st_get_lvar_def)
      apply (metis list_all2_Cons1 list_all2_Nil)
      done
    then obtain v where v_def:"app_binop op v1 v2 = Some v"
                              "emp h st"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def is_lvar_def var_st_get_lvar_def can_lvar_binop_def)
      apply fastforce
      done
    hence 0:"ass_sat ([is_lvar_binop lv1 lv2 op] \<^sub>s|\<^sub>h emp) [v] h st"
      using ass_is(1) vcs_is
      by (simp add: stack_ass_sat_def is_lvar_binop_def is_lvar_def var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C v1, $C v2, $Binop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "s = s' \<and> locs = locs' \<and> res = RValue (vcsf @ [v])"
      using reduce_to_n_binop[OF 1] v_def
      by simp
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar_binop lv1 lv2 op] \<^sub>s|\<^sub>h emp)"
      using vcs_is local_assms(1,4) 0 ass_is
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Relop \<Gamma> assms lv1 lv2 t op)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv1, is_lvar lv2] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Relop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv1, is_lvar lv2] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v1 v2 where vcs_is:"vcs = [v1, v2]"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def is_lvar_def var_st_get_lvar_def)
      apply (metis list_all2_Cons1 list_all2_Nil)
      done
    hence 0:"ass_sat ([is_lvar_relop lv1 lv2 op] \<^sub>s|\<^sub>h emp) [app_relop op v1 v2] h st"
      using ass_is(1)
      by (simp add: stack_ass_sat_def is_lvar_relop_def is_lvar_def var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C v1, $C v2, $Relop t op]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar_relop lv1 lv2 op] \<^sub>s|\<^sub>h emp)"
      using reduce_to_n_relop[OF 1] vcs_is local_assms(1,4) 0 ass_is
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Convert \<Gamma> assms lv t1 t2 sx)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar_t lv t1] \<^sub>s|\<^sub>h can_lvar_convert lv t2 sx)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Cvtop t2 Convert t1 sx]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar_t lv t1] \<^sub>s|\<^sub>h can_lvar_convert lv t2 sx) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis Suc_length_conv list_exhaust_size_eq0)
      done
    then obtain v' where v_def:"cvt t2 sx v = Some v'"
                              "emp h st"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def is_lvar_t_def var_st_get_lvar_def can_lvar_convert_def)
      apply fastforce
      done
    have 1:"(s, locs, ($$* vcsf) @ [$C v,$Cvtop t2 Convert t1 sx]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 2:"s = s' \<and> locs = locs' \<and> types_agree t1 v \<and> res = RValue (vcsf @ [v'])"
      using reduce_to_n_convert[OF 1] v_def
      by fastforce
    hence 0:"ass_sat ([is_lvar_convert lv t2 sx] \<^sub>s|\<^sub>h emp) [v'] h st"
      using ass_is(1) vcs_is 1 v_def
      by (simp add: stack_ass_sat_def is_lvar_convert_def list_all2_conv_all_nth is_lvar_t_def
                    var_st_get_lvar_def types_agree_def)
    have 3:"(s, locs, ($$* vcsf) @ [$C v,$Cvtop t2 Convert t1 sx]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar_convert lv t2 sx] \<^sub>s|\<^sub>h emp)"
      using 2 vcs_is local_assms(1,4) 0 ass_is 1 v_def
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Reinterpret \<Gamma> assms lv t1 t2)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar_t lv t1] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Cvtop t2 Reinterpret t1 None]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar_t lv t1] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis Suc_length_conv list_exhaust_size_eq0)
      done
    hence 0:"ass_sat ([is_lvar_reinterpret lv t2] \<^sub>s|\<^sub>h emp) [(wasm_deserialise (bits v) t2)] h st"
      using ass_is(1)
      by (simp add: stack_ass_sat_def is_lvar_reinterpret_def list_all2_conv_all_nth is_lvar_t_def
                    var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C v,$Cvtop t2 Reinterpret t1 None]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar_reinterpret lv t2] \<^sub>s|\<^sub>h emp)"
      using reduce_to_n_reinterpret[OF 1] vcs_is local_assms(1,4) 0 ass_is
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Nop \<Gamma> assms)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Nop]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have vcs_is:"vcs = []"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      done
    hence 0:"ass_sat ([] \<^sub>s|\<^sub>h emp) [] h st"
      using ass_is(1)
      by (simp add: stack_ass_sat_def is_lvar_testop_def list_all2_conv_all_nth is_lvar_def
                    var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$Nop]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([] \<^sub>s|\<^sub>h emp)"
      using reduce_to_n_nop[OF 1] vcs_is local_assms(1,4) 0 ass_is
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Drop \<Gamma> assms lv)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Drop]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis Suc_length_conv list_exhaust_size_eq0)
      done
    hence 0:"ass_sat ([] \<^sub>s|\<^sub>h emp) [] h st"
      using ass_is(1)
      by (simp add: stack_ass_sat_def is_lvar_testop_def list_all2_conv_all_nth is_lvar_def
                    var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C v,$Drop]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([] \<^sub>s|\<^sub>h emp)"
      using reduce_to_n_drop[OF 1] vcs_is local_assms(1,4) 0 ass_is
      unfolding res_wf_def
      apply simp
      apply (metis prod.collapse)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Select lv_arb lv1 lv2 lv32 \<Gamma> assms)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv1, is_lvar lv2, is_lvar32 lv32] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Select]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv1, is_lvar lv2, is_lvar32 lv32] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have emp_h:"emp h st"
      using ass_is(1)
      by fastforce
    obtain v1 v2 c where vcs_is:"vcs = [v1, v2, ConstInt32 c]"
                                "var_st_get_lvar st lv1 = Some (V_p v1)"
                                "var_st_get_lvar st lv2 = Some (V_p v2)"
                                "var_st_get_lvar st lv32 = Some (V_p (ConstInt32 c))"
      using ass_is(1) typeof_i32
      by (fastforce simp add: list_all2_Cons1 stack_ass_sat_def is_lvar_def is_lvar32_def var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C v1, $C v2, $C ConstInt32 c, $Select]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 2:"s = s'"
           "locs = locs'"
           "((res = RValue (vcsf @ [v2]) \<and> int_eq c 0) \<or> (res = RValue (vcsf @ [v1]) \<and> \<not> int_eq c 0))"
      using reduce_to_n_select[OF 1]
      by auto
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf (Ex_ass lv_arb ([is_lvar lv_arb] \<^sub>s|\<^sub>h (\<lambda>h st. lvar_is_lvar_and_lvar32_0 lv_arb lv2 lv32 h st \<or> lvar_is_lvar_and_lvar32_n lv_arb lv1 lv32 h st)))"
    proof (cases "(res = RValue (vcsf @ [v2]) \<and> int_eq c 0)")
      case True
      hence "ass_sat (Ex_ass lv_arb ([is_lvar lv_arb] \<^sub>s|\<^sub>h (\<lambda>h st. lvar_is_lvar_and_lvar32_0 lv_arb lv2 lv32 h st))) [v2] h st"
        using Select vcs_is emp_h
        apply (cases st)
        apply (simp add: stack_ass_sat_def lvar_is_lvar_and_lvar32_0_def var_st_get_lvar_def
                         var_st_set_lvar_def is_lvar_def is_lvar32_zero_def emp_def
                    split: prod.splits)
        done
      hence "ass_sat (Ex_ass lv_arb ([is_lvar lv_arb] \<^sub>s|\<^sub>h (\<lambda>h st. lvar_is_lvar_and_lvar32_0 lv_arb lv2 lv32 h st \<or> lvar_is_lvar_and_lvar32_n lv_arb lv1 lv32 h st))) [v2] h st"
        by auto
      thus ?thesis
        using local_assms(1) True ass_is
        unfolding res_wf_def
        apply simp
        apply (metis 2(1,2) prod.exhaust_sel)
        done
    next
      case False
      hence False2:"(res = RValue (vcsf @ [v1]) \<and> \<not> int_eq c 0)"
        using 2(3)
        by blast
      hence "ass_sat (Ex_ass lv_arb ([is_lvar lv_arb] \<^sub>s|\<^sub>h (\<lambda>h st. lvar_is_lvar_and_lvar32_n lv_arb lv1 lv32 h st))) [v1] h st"
        using Select vcs_is emp_h
        apply (cases st)
        apply (simp add: stack_ass_sat_def lvar_is_lvar_and_lvar32_n_def var_st_get_lvar_def
                         var_st_set_lvar_def is_lvar_def is_lvar32_n_def emp_def
                    split: prod.splits)
        done
      hence "ass_sat (Ex_ass lv_arb ([is_lvar lv_arb] \<^sub>s|\<^sub>h (\<lambda>h st. lvar_is_lvar_and_lvar32_0 lv_arb lv2 lv32 h st \<or> lvar_is_lvar_and_lvar32_n lv_arb lv1 lv32 h st))) [v1] h st"
        by auto
      thus ?thesis
        using local_assms(1) False2 ass_is
        unfolding res_wf_def
        apply simp
        apply (metis 2(1,2) prod.exhaust_sel)
          done
      qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Block fs Q ls r assms P es tn n tm m n')
  {
    fix \<Gamma> vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n' assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Block (tn _> tm) es]) \<Down>n'{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat P vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have vcs_is:"length vcs = n"
      using Block(4) stack_ass_sat_len[OF ass_is(1)]
      by simp
    hence 2:"(s, locs, ($$* vcsf) @ [Label m [] (($$* vcs) @ ($* es))]) \<Down>n'{(labs, ret, i)} (s', locs', res)"
      using reduce_to_n_block[OF local_assms(4)] Block(2,3)
      by auto
    obtain res' where res'_def:"(s, locs, ($$* []) @ ($$* vcs) @ ($* es)) \<Down>n'{(m # labs, ret, i)} (s', locs', res')"
                      "(res' = RTrap \<and> res = RTrap \<or>
                            (\<exists>rvs. res' = RValue rvs \<and>
                                   res = RValue (vcsf @ rvs)) \<or>
                            (\<exists>rvs. res' = RReturn rvs \<and>
                                   res = RReturn rvs) \<or>
                            (\<exists>n rvs.
                                res' = RBreak (Suc n) rvs \<and>
                                res = RBreak n rvs) \<or>
                            (\<exists>rvs. res' = RBreak 0 rvs \<and>
               res = RValue (vcsf @ rvs)))"
      using reduce_to_n_label_emp1[OF 2]
      by fastforce
    have r_lab':"reifies_lab (m#labs) (fs, Q # ls, r)"
      using local_assms(1) ass_is(5) Block(5)
      unfolding reifies_lab_def
      by auto
    have 3:"(fs, Q # ls, r) \<Turnstile>_n' {P} $* es {Q}"
      using Block(6) local_assms(2)
      unfolding valid_triple_defs
      by auto
    hence res_wf':"res_wf lvar_st (fs, Q # ls, r) res' locs' s' hf [] Q"
      using res_wf_valid_triple_n_intro[OF 3 _ res'_def(1)] ass_is r_lab' local_assms(1)
      unfolding ass_wf_def reifies_ret_def
      by auto
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
    proof (cases res')
      case (RValue x1)
      thus ?thesis
        using res_wf' local_assms(1) res'_def(2)
        unfolding res_wf_def
        by simp
    next
      case (RBreak x21 x22)
      thus ?thesis
        using res_wf' local_assms(1) res'_def(2)
        unfolding res_wf_def
        apply (cases x21)
         apply simp_all
        done
    next
      case (RReturn x3)
      thus ?thesis
        using res_wf' local_assms(1) res'_def(2)
        unfolding res_wf_def
        by simp
    next
      case RTrap
      thus ?thesis
        using res_wf'
        unfolding res_wf_def
        by simp
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply auto
    done
next
  case (Loop fs P ls r assms es Q tn n tm m n')
  {
    fix \<Gamma> vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n' assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Loop (tn _> tm) es]) \<Down>n'{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat P vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have vcs_is:"length ($$*vcs) = n"
      using Loop(4) stack_ass_sat_len[OF ass_is(1)]
      by simp
    have 3:"(fs, P # ls, r) \<Turnstile>_n' {P} $* es {Q}"
      using Loop(6) local_assms(2)
      unfolding valid_triple_defs
      by auto
    have 4:"ass_wf lvar_st ret (fs, P # ls, r) (n # labs)  locs s hf st h vcs P"
      using ass_is local_assms(1) Loop(4)
      unfolding ass_wf_def reifies_lab_def reifies_ret_def
      by simp
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
      using reduce_to_n_loop[OF local_assms(4) _ vcs_is Loop(2,3,4,5) 4 3] local_assms(1)
      by fastforce
  }
  thus ?case
    unfolding valid_triple_defs
    apply auto
    done

next
  case (If \<Gamma> assms St H lv tf es1 Q es2)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs ((St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$If tf es1 es2]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat (St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have block_is:"\<Gamma> \<Turnstile>_n {St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_n lv)} [$Block tf es1] {Q}"
         "\<Gamma> \<Turnstile>_n {St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_zero lv)} [$Block tf es2] {Q}"
      using If(3,4)[of n] local_assms(1,2)
      unfolding valid_triple_defs
      by auto
    have 1:"list_all2 (\<lambda>Si v. Si v st) (St @ [is_lvar32 lv]) vcs"
      using ass_is(1)
      by (simp add: stack_ass_sat_def var_st_get_lvar_def)
    obtain vcs' v where vcs_is:"vcs = vcs'@[v]" "is_lvar32 lv v st"
                               "stack_ass_sat St vcs' st"
      using list_all2_snoc1[OF 1]
      by (fastforce simp add: stack_ass_sat_def)
    then obtain c where v_is:"v = ConstInt32 c"
      using typeof_i32
      by (fastforce simp add: is_lvar32_def var_st_get_lvar_def)
    hence 2:"(s, locs, ($$* vcsf@vcs') @ [$C ConstInt32 c, $If tf es1 es2]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by simp
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
    proof (cases "int_eq c 0")
      case True
      hence true_is:"(s, locs, ($$* vcsf) @ ($$* vcs') @ [$Block tf es2]) \<Down>n{(labs, ret, i)} (s', locs', res)"
        using reduce_to_n_if[OF 2]
        by (metis append_assoc map_append)
      hence 0:"ass_sat  (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_zero lv)) vcs' h st"
        using ass_is vcs_is True v_is
        by (fastforce simp add: stack_ass_sat_def is_lvar_unop_def is_lvar_def is_lvar32_def heap_disj_def Option.is_none_def
                                option_disj_def map_disj_def disjnt_def var_st_get_lvar_def is_lvar32_zero_def sep_conj_def emp_def heap_merge_def
                      split: option.splits prod.splits)
      thus ?thesis
        using res_wf_valid_triple_n_intro[OF block_is(2) _ true_is]
        unfolding ass_wf_def
        by (metis ass_is(2,3,4,5,6,7))
    next
      case False
      hence false_is:"(s, locs, ($$* vcsf) @ ($$* vcs') @ [$Block tf es1]) \<Down>n{(labs, ret, i)} (s', locs', res)"
        using reduce_to_n_if[OF 2]
        by (metis append_assoc map_append)
      hence 0:"ass_sat  (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_n lv)) vcs' h st"
        using ass_is vcs_is False v_is
        by (fastforce simp add: stack_ass_sat_def is_lvar_unop_def is_lvar_def is_lvar32_def heap_disj_def Option.is_none_def
                                option_disj_def map_disj_def disjnt_def var_st_get_lvar_def is_lvar32_n_def sep_conj_def emp_def heap_merge_def
                      split: option.splits prod.splits)
      thus ?thesis
        using res_wf_valid_triple_n_intro[OF block_is(1) _ false_is]
        unfolding ass_wf_def
        by (metis ass_is(2,3,4,5,6,7))
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Get_local \<Gamma> assms j lv)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([] \<^sub>s|\<^sub>h local_is_lvar j lv)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Get_local j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([] \<^sub>s|\<^sub>h local_is_lvar j lv) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have vcs_is:"vcs = []"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$Get_local j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 2:"s = s'"
           "locs = locs'"
           "j < length locs"
           "res = RValue (vcsf @ [locs ! j])"
      using reduce_to_n_get_local[OF 1]
      by auto
    hence 0:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h local_is_lvar j lv) [(locs!j)] h st"
      using ass_is(1) 2 ass_is(4)
      apply (cases st)
      apply (simp add: stack_ass_sat_def is_lvar_testop_def list_all2_conv_all_nth is_lvar_def
                       var_st_get_lvar_def local_is_lvar_def var_st_get_local_def reifies_loc_def
                  split: if_splits)
      done
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar lv] \<^sub>s|\<^sub>h local_is_lvar j lv)"
      using vcs_is local_assms(1,4) 0 ass_is 2
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Set_local \<Gamma> assms lv j)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Set_local j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
                          "emp h st"
                          "lvar_st lv = Some (V_p v)"
      using ass_is(1,7)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis length_Suc_conv list_exhaust_size_eq0)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$C v, $Set_local j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 2:"s = s'"
           "locs[j := v] = locs'"
           "j < length locs"
           "res = RValue (vcsf)"
      using reduce_to_n_set_local[OF 1]
      by auto
    hence 0:"ass_sat ([] \<^sub>s|\<^sub>h local_is_lvar j lv) [] h (fst st, locs', lvar_st)"
      using ass_is(1) 2 ass_is(4) vcs_is(3)
      apply (cases st)
      apply (auto simp add: stack_ass_sat_def is_lvar_testop_def list_all2_conv_all_nth is_lvar_def emp_def
                       var_st_get_lvar_def local_is_lvar_def var_st_get_local_def reifies_loc_def
                  split: if_splits)
      done
    have "reifies_s s' i (heap_merge h hf) (fst st, locs', lvar_st) (fst \<Gamma>)"
      using ass_is(3) 2
      unfolding reifies_s_def reifies_glob_def
      by simp
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([] \<^sub>s|\<^sub>h local_is_lvar j lv)"
      using vcs_is local_assms(1,4) 0 ass_is 2 local_assms(1)
      unfolding res_wf_def
      apply (simp add: reifies_loc_def stack_ass_sat_def)
      apply (metis surj_pair)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Tee_local \<Gamma> assms lv j Q)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Tee_local j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
                          "emp h st"
                          "lvar_st lv = Some (V_p v)"
      using ass_is(1,7)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis length_Suc_conv list_exhaust_size_eq0)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$C v, $Tee_local j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 4:"(s, locs, ($$* vcsf) @ ($$*[v,v]) @ [$Set_local j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using reduce_to_n_tee_local[OF 1]
      by fastforce
    have 2:"\<Gamma> \<Turnstile>_n {[is_lvar lv, is_lvar lv] \<^sub>s|\<^sub>h emp} [$Set_local j] {Q}"
      using Tee_local(2) local_assms(1,2)
      unfolding valid_triple_defs
      by simp
    have "ass_sat ([is_lvar lv, is_lvar lv] \<^sub>s|\<^sub>h emp) [v,v] h st"
      using ass_is vcs_is
      by (simp add: stack_ass_sat_def)
    hence "ass_wf lvar_st ret \<Gamma> labs locs s hf st h [v, v] ([is_lvar lv, is_lvar lv] \<^sub>s|\<^sub>h emp)"
      using ass_is
      unfolding ass_wf_def
      by auto
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
      using res_wf_valid_triple_n_intro[OF 2 _ 4]
      by blast
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Get_global j \<Gamma> assms lv)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([] \<^sub>s|\<^sub>h global_is_lvar j lv)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Get_global j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([] \<^sub>s|\<^sub>h global_is_lvar j lv) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have vcs_is:"vcs = []"
      using ass_is(1)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$Get_global j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 2:"s = s'"
           "locs = locs'"
           "res = RValue (vcsf @ [(sglob_val s i j)])"
      using reduce_to_n_get_global[OF 1]
      by auto
    hence 0:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h global_is_lvar j lv) [(sglob_val s i j)] h st"
      using ass_is(1) 2 ass_is(3)
      apply (cases st)
      apply (simp add: stack_ass_sat_def is_lvar_testop_def list_all2_conv_all_nth is_lvar_def
                       var_st_get_lvar_def global_is_lvar_def var_st_get_local_def reifies_loc_def
                       reifies_s_def reifies_glob_def sglob_val_def sglob_def sglob_ind_def
                       Get_global.hyps var_st_get_global_def
                  split: if_splits)
      done
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvar lv] \<^sub>s|\<^sub>h global_is_lvar j lv)"
      using vcs_is local_assms(1,4) 0 ass_is 2
      unfolding res_wf_def
      apply simp
      apply (metis prod.exhaust prod.sel(2))
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Set_global j \<Gamma> assms lv)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar lv] \<^sub>s|\<^sub>h emp)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Set_global j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar lv] \<^sub>s|\<^sub>h emp) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain v where vcs_is:"vcs = [v]"
                          "emp h st"
                          "lvar_st lv = Some (V_p v)"
      using ass_is(1,7)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar_def var_st_get_lvar_def)
      apply (metis length_Suc_conv list_exhaust_size_eq0)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$C v, $Set_global j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    have 3:"j < length (fst st)"
      using Set_global ass_is(3)
      unfolding reifies_s_def reifies_glob_def
      apply (cases st)
      apply auto
      done
    have 2:"supdate_glob s i j v = s'"
           "locs = locs'"
           "res = RValue vcsf"
      using reduce_to_n_set_global[OF 1]
      by auto
    hence 0:"ass_sat ([] \<^sub>s|\<^sub>h global_is_lvar j lv) [] h (var_st_set_global_v st j v)"
      using ass_is(1) 2 ass_is(4) vcs_is(1,3) 3
      apply (cases st)
      apply (auto simp add: stack_ass_sat_def is_lvar_testop_def list_all2_conv_all_nth is_lvar_def emp_def
                       var_st_get_lvar_def global_is_lvar_def var_st_get_local_def reifies_loc_def
                       var_st_set_global_v_def var_st_get_global_def
                  split: if_splits)
      done
    have 4:"reifies_s s' i (heap_merge h hf) (var_st_set_global_v st j v) (fst \<Gamma>)"
      using ass_is(3) 2 Set_global local_assms(1)
      by (auto simp add: var_st_set_global_v_def reifies_glob_def Let_def reifies_heap_def
                            reifies_s_def supdate_glob_def sglob_ind_def supdate_glob_s_def
                            reifies_func_def nth_list_update encapsulated_inst_globs
                  split: prod.splits)
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([] \<^sub>s|\<^sub>h global_is_lvar j lv)"
      using res_wf_intro_value[OF 0 _ ass_is(2) _ 4] ass_is(4,7) 3 2 local_assms(1)
      apply (cases st)
      apply (auto simp add: reifies_loc_def var_st_set_global_v_def)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
case (Load \<Gamma> assms lv lvs t off a)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv off)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Load t None a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv off) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain c where vcs_is:"vcs = [ConstInt32 c]"
                          "lvar_st lv = Some (V_p (ConstInt32 c))"
      using ass_is(1,7)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar32_def var_st_get_lvar_def)
      apply (metis Suc_length_conv list_exhaust_size_eq0 nth_Cons_0 typeof_i32)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$C ConstInt32 c, $Load t None a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    obtain j m where  2:"s = s'" "locs = locs'"
                         "smem_ind s i = Some j"
                         "s.mem s ! j = m"
                       "(\<exists>bs. load m (Wasm_Base_Defs.nat_of_int c)
                              off (t_length t) =
                             Some bs \<and>
                             res =
                             RValue
                              (vcsf @ [wasm_deserialise bs t]) \<or>
                             load m (Wasm_Base_Defs.nat_of_int c)
                              off (t_length t) =
                             None \<and>
                             res = RTrap)"
      using reduce_to_n_load[OF 1]
      by blast
    obtain bs where bs_def:"list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs"
      using ass_is(1)
      apply (simp add: is_n_locs_from_lvar32_off_lvars_def)
      apply blast
      done
    have 6:"(t_length t) \<ge> 1"
      by (simp add: t_length_def split: t.splits)
    have 5:"h = (make_bs_t ((Wasm_Base_Defs.nat_of_int c) + off) (t_length t) bs, None)"
           "(t_length t) = length bs"
      using ass_is(1) list_all2_bs_unique[OF bs_def] vcs_is
      apply (simp_all add: is_n_locs_from_lvar32_off_lvars_def is_n_locs_from_lvar32_off_def split: prod.splits)
       apply (metis ass_is(7) lvar_v.inject(1) option.inject prod.exhaust_sel v.inject(1) var_st_get_lvar_def)
      apply (metis prod.exhaust_sel)
      done
    have 6:"load m (Wasm_Base_Defs.nat_of_int c) off (t_length t) = Some bs"
      using 2(1,2,3,4) make_bs_t_reifies[OF 5(1) 5(2) ass_is(2) _ _ 6] ass_is(3)
      unfolding reifies_s_def reifies_heap_def Let_def smem_ind_def
      by simp
    hence 3:"res = RValue (vcsf @ [wasm_deserialise bs t])"
      using 2(5)
      by fastforce
    have 4:"ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv off) [ConstInt32 c] h st"
      using ass_is(1) vcs_is
      by simp
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvs lvs t] \<^sub>s|\<^sub>h
      is_n_locs_from_lvar32_off_lvars lvs (t_length t) lv off)"
      using is_n_locs_from_lvar32_off_reifies[OF 4] 3 local_assms(1) ass_is 2(1,2)
      unfolding res_wf_def
      apply simp
      apply (metis ass_is(2) ass_is(7) bs_def eq_snd_iff)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Load_packed \<Gamma> assms lv lvs tp off t sx a)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv off)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Load t (Some (tp,sx)) a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv off) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain c where vcs_is:"vcs = [ConstInt32 c]"
                          "lvar_st lv = Some (V_p (ConstInt32 c))"
      using ass_is(1,7)
      apply (simp add: stack_ass_sat_def list_all2_conv_all_nth is_lvar32_def var_st_get_lvar_def)
      apply (metis Suc_length_conv list_exhaust_size_eq0 nth_Cons_0 typeof_i32)
      done
    have 1:"(s, locs, ($$* vcsf) @ [$C ConstInt32 c, $Load t (Some (tp,sx)) a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    obtain j m where  2:"s = s'" "locs = locs'"
                         "smem_ind s i = Some j"
                         "s.mem s ! j = m"
                       "((\<exists>bs. load m (Wasm_Base_Defs.nat_of_int c)
                                off (tp_length tp) =
                               Some bs \<and>
                               res =
                               RValue
                                (vcsf @
                                 [wasm_deserialise
                                   (sign_extend sx (t_length t) bs)
                                   t]) \<or>
                               load m (Wasm_Base_Defs.nat_of_int c)
                                off (tp_length tp) =
                               None \<and>
               res = RTrap))"
      using reduce_to_n_load_packed[OF 1]
      by blast
    obtain bs where bs_def:"list_all2 (\<lambda>lv b. var_st_get_lvar st lv = Some (V_b b)) lvs bs"
      using ass_is(1)
      apply (simp add: is_n_locs_from_lvar32_off_lvars_def)
      apply blast
      done
    have 6:"(tp_length tp) \<ge> 1"
      by (simp add: tp_length_def split: tp.splits)
    have 5:"h = (make_bs_t ((Wasm_Base_Defs.nat_of_int c) + off) (tp_length tp) bs, None)"
           "(tp_length tp) = length bs"
      using ass_is(1) list_all2_bs_unique[OF bs_def] vcs_is
      apply (simp_all add: is_n_locs_from_lvar32_off_lvars_def is_n_locs_from_lvar32_off_def split: prod.splits)
       apply (metis ass_is(7) lvar_v.inject(1) option.inject prod.exhaust_sel v.inject(1) var_st_get_lvar_def)
      apply (metis prod.exhaust_sel)
      done
    have 6:"load m (Wasm_Base_Defs.nat_of_int c) off (tp_length tp) = Some bs"
      using 2(1,2,3,4) make_bs_t_reifies[OF 5(1) 5(2) ass_is(2) _ _ 6] ass_is(3)
      unfolding reifies_s_def reifies_heap_def Let_def smem_ind_def
      by simp
    hence 3:"res = RValue  (vcsf @ [wasm_deserialise (sign_extend sx (t_length t) bs) t])"
      using 2(5)
      by fastforce
    have 4:"ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv off) [ConstInt32 c] h st"
      using ass_is(1) vcs_is
      by simp
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_lvs_packed lvs t sx (t_length t)] \<^sub>s|\<^sub>h
      is_n_locs_from_lvar32_off_lvars lvs (tp_length tp) lv off)"
      using is_n_locs_from_lvar32_off_packed_reifies[OF 4] 3 local_assms(1) ass_is 2(1,2)
      unfolding res_wf_def
      apply simp
      apply (metis ass_is(2) ass_is(7) bs_def eq_snd_iff)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Store \<Gamma> assms lv32 lv t off a)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar32 lv32, is_lvar lv] \<^sub>s|\<^sub>h (\<lambda>h st. \<exists>bs. is_n_locs_from_lvar32_off bs (t_length t) lv32 off h st))::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Store t None a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar32 lv32, is_lvar lv] \<^sub>s|\<^sub>h (\<lambda>h st. \<exists>bs. is_n_locs_from_lvar32_off bs (t_length t) lv32 off h st)) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain c v where vcs_is:"vcs = [ConstInt32 c, v]"
                            "lvar_st lv32 = Some (V_p (ConstInt32 c))"
                            "lvar_st lv = Some (V_p v)"
      using ass_is(1,7) typeof_i32
      by (fastforce simp add: list_all2_Cons1 stack_ass_sat_def is_lvar_def is_lvar32_def var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C ConstInt32 c,$C v, $Store t None a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    obtain j m where  2:"locs = locs'"
                        "types_agree t v"
                        "smem_ind s i = Some j"
                        "s.mem s ! j = m"
                                 "(s = s' \<and>
                                  store (s.mem s ! j) (Wasm_Base_Defs.nat_of_int c) off (bits v) (t_length t) = None \<and>
                                  res = RTrap \<or>
                                  (\<exists>mem'.
                                      store (s.mem s ! j)
                                       (Wasm_Base_Defs.nat_of_int c) off
                                       (bits v) (t_length t) =
                                      Some mem' \<and>
                                      s' = s\<lparr>s.mem := s.mem s[j := mem']\<rparr> \<and>
                                      res = RValue vcsf))"
      using reduce_to_n_store[OF 1]
      by blast
    have 6:"(t_length t) \<ge> 1"
      by (simp add: t_length_def split: t.splits)
    obtain bs where bs_is:"h = (make_bs_t ((Wasm_Base_Defs.nat_of_int c) + off) (t_length t) bs, None)"
                          "t_length t = length bs"
      using ass_is(1,7) vcs_is(2)
      apply (cases h)
      apply (auto simp add: is_n_locs_from_lvar32_off_def var_st_get_lvar_def)
      done
    obtain h' m' where m'_def:"m' =
                          write_bytes m
                           (Wasm_Base_Defs.nat_of_int c + off)
                           (bytes_takefill 0 (t_length t) (bits v))"
                        "h' =
                            ((make_bs_t (Wasm_Base_Defs.nat_of_int c + off)
                              (t_length t)
                              (bytes_takefill 0 (t_length t) (bits v))), None::(nat option))"
                      
      by blast
    have 7:"mem_length m \<ge> ((Wasm_Base_Defs.nat_of_int c) + off) + (t_length t)"
      using make_bs_t_length[OF bs_is(1,2) _ 6] ass_is(1,3) ass_is
      unfolding reifies_s_def reifies_heap_def
      by (metis 2(3,4) option.sel smem_ind_def)
    have res_is:"store (s.mem s ! j) (Wasm_Base_Defs.nat_of_int c) off (bits v) (t_length t) = Some m'"
         "s' = s\<lparr>s.mem := s.mem s[j := m']\<rparr>"
         "res = RValue vcsf"
      using 2(4,5) 7 m'_def(1)
      unfolding store_def
      by (simp_all split: if_splits)
    have h'_is:"heap_disj h' hf"
         "reifies_heap_contents m' (fst (heap_merge h' hf))"
         "reifies_heap_length m' (snd (heap_merge h' hf))"
      using make_bs_t_store_reifies[OF bs_is(1,2) ass_is(2) _ _ 7 m'_def(1,2)] ass_is(3) 2(2,3,4)
      unfolding reifies_s_def reifies_heap_def Let_def smem_ind_def
      by simp_all
    have ass_sat_is:"ass_sat ([] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvar lv (t_length t) lv32 off) [] h' st"
      using vcs_is(2,3) ass_is(7) m'_def(2)
      by (simp add: bytes_takefill_def stack_ass_sat_def is_n_locs_from_lvar32_off_lvar_def is_n_locs_from_lvar32_off_def var_st_get_lvar_def split: prod.splits)
    have reifies_s_is:"reifies_s s' i (heap_merge h' hf) st fs"
      using ass_is(3) res_is(1,2) 2(3,4) local_assms(1) h'_is
      unfolding reifies_s_def
      by (auto simp add: reifies_heap_def Let_def smem_ind_def)
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvar lv (t_length t) lv32 off)"
      using 2(1) local_assms(1) res_is res_wf_intro_value[OF ass_sat_is _ h'_is(1) _ reifies_s_is ass_is(4,7)]
      by simp
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Store_packed \<Gamma> assms lv32 lv tp off t a)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar32 lv32, is_lvar lv] \<^sub>s|\<^sub>h (\<lambda>h st. \<exists>bs. is_n_locs_from_lvar32_off bs (tp_length tp) lv32 off h st))::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Store t (Some tp) a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ([is_lvar32 lv32, is_lvar lv] \<^sub>s|\<^sub>h (\<lambda>h st. \<exists>bs. is_n_locs_from_lvar32_off bs (tp_length tp) lv32 off h st)) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain c v where vcs_is:"vcs = [ConstInt32 c, v]"
                            "lvar_st lv32 = Some (V_p (ConstInt32 c))"
                            "lvar_st lv = Some (V_p v)"
      using ass_is(1,7) typeof_i32
      by (fastforce simp add: list_all2_Cons1 stack_ass_sat_def is_lvar_def is_lvar32_def var_st_get_lvar_def)
    have 1:"(s, locs, ($$* vcsf) @ [$C ConstInt32 c,$C v, $Store t (Some tp) a off]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by auto
    obtain j m where  2:"locs = locs'"
                        "types_agree t v"
                        "smem_ind s i = Some j"
                        "s.mem s ! j = m"
                                 "(s = s' \<and>
                                  store (s.mem s ! j) (Wasm_Base_Defs.nat_of_int c) off (bits v) (tp_length tp) = None \<and>
                                  res = RTrap \<or>
                                  (\<exists>mem'.
                                      store (s.mem s ! j)
                                       (Wasm_Base_Defs.nat_of_int c) off
                                       (bits v) (tp_length tp) =
                                      Some mem' \<and>
                                      s' = s\<lparr>s.mem := s.mem s[j := mem']\<rparr> \<and>
                                      res = RValue vcsf))"
      using reduce_to_n_store_packed[OF 1]
      by blast
    have 6:"(tp_length tp) \<ge> 1"
      by (simp add: tp_length_def split: tp.splits)
    obtain bs where bs_is:"h = (make_bs_t ((Wasm_Base_Defs.nat_of_int c) + off) (tp_length tp) bs, None)"
                          "tp_length tp = length bs"
      using ass_is(1,7) vcs_is(2)
      apply (cases h)
      apply (auto simp add: is_n_locs_from_lvar32_off_def var_st_get_lvar_def)
      done
    obtain h' m' where m'_def:"m' =
                          write_bytes m
                           (Wasm_Base_Defs.nat_of_int c + off)
                           (bytes_takefill 0 (tp_length tp) (bits v))"
                        "h' =
                            ((make_bs_t (Wasm_Base_Defs.nat_of_int c + off)
                              (tp_length tp)
                              (bytes_takefill 0 (tp_length tp) (bits v))), None::(nat option))"
                      
      by blast
    have 7:"mem_length m \<ge> ((Wasm_Base_Defs.nat_of_int c) + off) + (tp_length tp)"
      using make_bs_t_length[OF bs_is(1,2) _ 6] ass_is(1,3) ass_is
      unfolding reifies_s_def reifies_heap_def
      by (metis 2(3,4) option.sel smem_ind_def)
    have res_is:"store (s.mem s ! j) (Wasm_Base_Defs.nat_of_int c) off (bits v) (tp_length tp) = Some m'"
         "s' = s\<lparr>s.mem := s.mem s[j := m']\<rparr>"
         "res = RValue vcsf"
      using 2(4,5) 7 m'_def(1)
      unfolding store_def
      by (simp_all split: if_splits)
    have h'_is:"heap_disj h' hf"
         "reifies_heap_contents m' (fst (heap_merge h' hf))"
         "reifies_heap_length m' (snd (heap_merge h' hf))"
      using make_bs_t_store_reifies[OF bs_is(1,2) ass_is(2) _ _ 7 m'_def(1,2)] ass_is(3) 2(2,3,4)
      unfolding reifies_s_def reifies_heap_def Let_def smem_ind_def
      by simp_all
    have ass_sat_is:"ass_sat ([] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvar lv (tp_length tp) lv32 off) [] h' st"
      using vcs_is(2,3) ass_is(7) m'_def(2)
      by (simp add: bytes_takefill_def stack_ass_sat_def is_n_locs_from_lvar32_off_lvar_def is_n_locs_from_lvar32_off_def var_st_get_lvar_def split: prod.splits)
    have reifies_s_is:"reifies_s s' i (heap_merge h' hf) st fs"
      using ass_is(3) res_is(1,2) 2(3,4) local_assms(1) h'_is
      unfolding reifies_s_def
      by (auto simp add: reifies_heap_def Let_def smem_ind_def)
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([] \<^sub>s|\<^sub>h is_n_locs_from_lvar32_off_lvar lv (tp_length tp) lv32 off)"
      using 2(1) local_assms(1) res_is res_wf_intro_value[OF ass_sat_is _ h'_is(1) _ reifies_s_is ass_is(4,7)]
      by simp
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Br j ls fs r assms Q)
  {
    fix \<Gamma> vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (ls!j)"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Br j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat ((ls!j)) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have 0:"length vcs = (labs!j)"
      using ass_is(5) local_assms(1) stack_ass_sat_len[OF ass_is(1)] Br
      unfolding reifies_lab_def
      by simp
    hence "s = s' \<and> locs = locs' \<and> res = RBreak j vcs"
      using reduce_to_n_br[OF local_assms(4)]
      by metis
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
      using ass_is local_assms(1)
      unfolding res_wf_def
      apply simp
      apply safe
      apply (metis Br.hyps)
      apply (metis prod.collapse)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (auto split: prod.splits)
    done
next
  case (Br_if \<Gamma> assms St H lv j Q)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs ((St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Br_if j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat (St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have 1:"list_all2 (\<lambda>Si v. Si v st) (St @ [is_lvar32 lv]) vcs"
      using ass_is(1)
      by (simp add: stack_ass_sat_def var_st_get_lvar_def)
    obtain vcs' v where vcs_is:"vcs = vcs'@[v]" "is_lvar32 lv v st"
                               "stack_ass_sat St vcs' st"
      using list_all2_snoc1[OF 1]
      by (fastforce simp add: stack_ass_sat_def)
    then obtain c where v_is:"v = ConstInt32 c"
      using typeof_i32
      by (fastforce simp add: is_lvar32_def var_st_get_lvar_def)
    hence 2:"(s, locs, ($$* vcsf@vcs') @ [$C ConstInt32 c, $Br_if j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by simp
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_zero lv))"
    proof (cases "int_eq c 0")
      case True
      hence true_is:"s = s' \<and> locs = locs' \<and> res = RValue (vcsf @ vcs')"
        using reduce_to_n_br_if[OF 2]
        by metis
      hence 0:"ass_sat  (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_zero lv)) vcs' h st"
        using ass_is vcs_is True v_is
        by (fastforce simp add: stack_ass_sat_def is_lvar_unop_def is_lvar_def is_lvar32_def heap_disj_def Option.is_none_def
                                option_disj_def map_disj_def disjnt_def var_st_get_lvar_def is_lvar32_zero_def sep_conj_def emp_def heap_merge_def
                      split: option.splits prod.splits)
      thus ?thesis
        using true_is local_assms(1) ass_is vcs_is
        unfolding res_wf_def
        apply (cases st)
        apply simp
        apply (metis surj_pair)
        done
    next
      case False
      hence false_is:"((s, locs, ($$* vcsf @ vcs') @ [$Br j]) \<Down>n{(labs, ret, i)} (s', locs', res))"
        using reduce_to_n_br_if[OF 2]
        by metis
      moreover
      have "\<Gamma> \<Turnstile>_n {(St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_n lv))} [$Br j] {Q}"
        using Br_if(2) local_assms
        unfolding valid_triple_defs
        by simp
      moreover
      have "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs' ((St \<^sub>s|\<^sub>h H)::('a ass))"
        using vcs_is local_assms(3)
        unfolding ass_wf_def
        by simp
      hence "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs' ((St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_n lv))::('a ass))"
        using False
        unfolding ass_wf_def
        apply (simp add: sep_conj_def is_lvar32_n_def heap_disj_def map_disj_def disjnt_def
                         option_disj_def Option.is_none_def emp_def heap_merge_def
                    split: option.splits prod.splits)
        apply (metis is_lvar32_def v_is vcs_is(2))
        apply (metis is_lvar32_def option.sel v_is vcs_is(2))
        done
      ultimately
      have 3:"res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
        apply simp
        apply (metis res_wf_valid_triple_n_intro)
        done
      show ?thesis
        using res_wf_valid_triple_n_not_rvalue[OF 3] reduce_to_n_br_imp_length[OF false_is]
        apply simp
        apply (metis res_b.simps(5))
        done
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Br_table js \<Gamma> assms St H lv Q j)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs ((St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Br_table js j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat (St @ [is_lvar32 lv] \<^sub>s|\<^sub>h H) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have 1:"list_all2 (\<lambda>Si v. Si v st) (St @ [is_lvar32 lv]) vcs"
      using ass_is(1)
      by (simp add: stack_ass_sat_def var_st_get_lvar_def)
    obtain vcs' v where vcs_is:"vcs = vcs'@[v]" "is_lvar32 lv v st"
                               "stack_ass_sat St vcs' st"
      using list_all2_snoc1[OF 1]
      by (fastforce simp add: stack_ass_sat_def)
    then obtain c where v_is:"v = ConstInt32 c"
      using typeof_i32
      by (fastforce simp add: is_lvar32_def var_st_get_lvar_def)
    hence 2:"(s, locs, ($$* vcsf@vcs') @ [$C ConstInt32 c, $Br_table js j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4) vcs_is
      by simp
    obtain c' where c'_def:"nat_of_int c = c'"
      by blast
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
    proof (cases "c' < (length js)")
      case True
      hence true_is:"(s, locs, ($$* vcsf @ vcs') @ [$Br (js !  c')]) \<Down>n{(labs, ret, i)} (s', locs', res)"
        using reduce_to_n_br_table[OF 2]
        by (metis c'_def le_antisym less_imp_le_nat nat_neq_iff)
      moreover
      have "\<Gamma> \<Turnstile>_n {(St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_eq_n lv c'))} [$Br (js!c')] {Q}"
        using Br_table(1) local_assms c'_def True
        unfolding valid_triple_defs
        by simp
      moreover
      have 0:"ass_sat (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_eq_n lv c')) vcs' h st"
        using ass_is vcs_is True v_is
        by (fastforce simp add: stack_ass_sat_def is_lvar_unop_def is_lvar_def is_lvar32_def heap_disj_def Option.is_none_def
                         c'_def is_lvar32_eq_n_def option_disj_def map_disj_def disjnt_def var_st_get_lvar_def is_lvar32_zero_def sep_conj_def emp_def heap_merge_def
                      split: option.splits prod.splits)
      hence 1:"ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs' (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_eq_n lv c'))"
        using local_assms(3)
        unfolding ass_wf_def
        by fastforce
      ultimately
      show ?thesis
        unfolding valid_triple_defs
        by (metis append.assoc map_append)
    next
      case False
      hence false_is:"(s, locs, ($$* vcsf @ vcs') @ [$Br j]) \<Down>n{(labs, ret, i)} (s', locs', res)"
        using reduce_to_n_br_table[OF 2]
        by (metis c'_def)
      moreover
      have "\<Gamma> \<Turnstile>_n {(St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_geq_n lv (length js)))} [$Br j] {Q}"
        using Br_table(2) local_assms c'_def False
        unfolding valid_triple_defs
        by simp
      moreover
      have 0:"ass_sat (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_geq_n lv (length js))) vcs' h st"
        using ass_is vcs_is False v_is
        by (fastforce simp add: stack_ass_sat_def is_lvar_unop_def is_lvar_def is_lvar32_def heap_disj_def Option.is_none_def
                         c'_def is_lvar32_geq_n_def option_disj_def map_disj_def disjnt_def var_st_get_lvar_def is_lvar32_zero_def sep_conj_def emp_def heap_merge_def
                      split: option.splits prod.splits)
      hence 1:"ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs' (St \<^sub>s|\<^sub>h (H \<^emph> is_lvar32_geq_n lv (length js)))"
        using local_assms(3)
        unfolding ass_wf_def
        by fastforce
      ultimately
      show ?thesis
        unfolding valid_triple_defs
        by (metis append.assoc map_append)
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Return fs ls r' assms Q)
  {
    fix \<Gamma> vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,Some r')"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs r'"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Return]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    have ass_is:"ass_sat (r') vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    obtain ret' where "ret = Some ret'"
                      "length vcs = ret'"
      using ass_is(6) local_assms(1) stack_ass_sat_len[OF ass_is(1)] Return
      unfolding reifies_ret_def
      by simp
    hence "s = s' \<and> locs = locs' \<and> res = RReturn vcs"
      using reduce_to_n_return[OF local_assms(4)]
      by metis
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
      using ass_is local_assms(1)
      unfolding res_wf_def
      apply simp
      apply safe
      apply (metis prod.collapse)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (auto split: prod.splits)
    done
next
  case (Size_mem \<Gamma> assms lv_l)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([] \<^sub>s|\<^sub>h is_lvar_len lv_l)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Current_memory]) \<Down>n{(labs, ret, i)} (s', locs', res)"
    obtain n j m where s_is:"s = s'"
                       "locs = locs'"
                       "res =  RValue ((vcsf@vcs) @ [ConstInt32 (Wasm_Base_Defs.int_of_nat n)])"
                       "smem_ind s i = Some j"
                       "s.mem s ! j = m \<and> mem_size m = n"
      using reduce_to_n_current_memory local_assms(4)
      by (metis append_assoc map_append)
    have ass_is:"ass_sat ([] \<^sub>s|\<^sub>h is_lvar_len lv_l) vcs h st"
                "heap_disj h hf"
                "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                "reifies_loc locs st"
                "reifies_lab labs \<Gamma>"
                "reifies_ret ret \<Gamma>"
                "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by blast+
    have 1:"vcs = []"
      using ass_is(1)
      by (simp add: stack_ass_sat_def)
    have "snd h = Some n"
      using ass_is(1,3) s_is(4,5)
      by (auto simp add: stack_ass_sat_def is_lvar_len_def pred_option_Some_def reifies_s_def Ki64_def
                         reifies_heap_def reifies_heap_length_def heap_merge_def smem_ind_def mem_size_def
               split: prod.splits if_splits)
    hence "ass_sat ([is_i32_of_lvar lv_l] \<^sub>s|\<^sub>h is_lvar_len lv_l) [ConstInt32 (Wasm_Base_Defs.int_of_nat n)] h st"
      using ass_is(1)
      by (auto simp add: stack_ass_sat_def is_lvar_len_def is_i32_of_lvar_def pred_option_Some_def)
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf ([is_i32_of_lvar lv_l] \<^sub>s|\<^sub>h is_lvar_len lv_l)"
      using ass_is s_is local_assms(1) 1
      unfolding res_wf_def
      apply simp
      apply (metis prod.collapse)
      done
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Grow_mem lv_arb lv lv_l \<Gamma> assms)
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res Q
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (([is_lvar32 lv] \<^sub>s|\<^sub>h is_lvar_len lv_l)::('a ass))"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Grow_memory]) \<Down>n{(labs, ret, i)} (s', locs', res)"
                       "(Q::'a ass) = (Ex_ass lv_arb
                     ([is_lvar32 lv_arb] \<^sub>s|\<^sub>h
                                            (\<lambda>h v_st.
                                              (lvar32_zero_pages_from_lvar_len lv lv_l \<^emph>
                                               lvar_is_i32_of_lvar lv_arb lv_l)
                                               h v_st \<or>
                                              (is_lvar32_minus_one lv_arb \<^emph> is_lvar_len lv_l) h
                                               v_st)))"
    obtain k_g where vcs_is:"vcs = [ConstInt32 k_g]"
      using local_assms(3)
      unfolding ass_wf_def
      apply (simp add: list_all2_conv_all_nth stack_ass_sat_def is_lvar32_def)
      apply (metis length_Suc_conv list_exhaust_size_eq0 nth_Cons_0 typeof_i32)
      done
    hence 0:"(s, locs, ($$* vcsf) @ [$C ConstInt32 k_g,$Grow_memory]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using local_assms(4)
      by simp
      have ass_wf_is:"ass_sat ([is_lvar32 lv] \<^sub>s|\<^sub>h is_lvar_len lv_l) [ConstInt32 k_g] h st"
                     "heap_disj h hf"
                     "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                     "reifies_loc locs st"
                     "reifies_lab labs \<Gamma>"
                     "reifies_ret ret \<Gamma>"
                     "snd (snd st) = lvar_st"
        using local_assms(3) vcs_is
        unfolding ass_wf_def
        by simp_all
    consider
      (1) "\<exists>n j m.
           (locs = locs' \<and> smem_ind s i = Some j \<and> s.mem s ! j = m \<and> mem_size m = n) \<and>
           (s = s' \<and> res = RValue (vcsf @ [ConstInt32 int32_minus_one]))"
    | (2) "\<exists>n j m.
           (locs = locs' \<and> smem_ind s i = Some j \<and> s.mem s ! j = m \<and> mem_size m = n) \<and>
           (s' = s\<lparr>s.mem := s.mem s[j := mem_grow (s.mem s ! j)(Wasm_Base_Defs.nat_of_int k_g)]\<rparr> \<and>
            res = RValue (vcsf @ [ConstInt32 (Wasm_Base_Defs.int_of_nat n)]))"
      using reduce_to_n_grow_memory[OF 0]
      by fastforce
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
    proof cases
      case 1
      then obtain j_m n_m m_m where mes_iss:"locs = locs'"
                                            "smem_ind s i = Some j_m"
                                            "s.mem s ! j_m = m_m \<and> mem_size m_m = n_m"
                                            "s = s'"
                                            "res = RValue (vcsf @ [ConstInt32 int32_minus_one])"
        by blast
      have "ass_sat (Ex_ass lv_arb ([is_lvar32 lv_arb] \<^sub>s|\<^sub>h (\<lambda>h v_st. (is_lvar32_minus_one lv_arb \<^emph> is_lvar_len lv_l) h v_st)))  [ConstInt32 int32_minus_one] h st"
        using ass_wf_is(1) Grow_mem
        unfolding local_assms(5) is_lvar32_minus_one_def is_lvar_len_def
        apply (cases st)
        apply (simp add: pred_option_Some_def stack_ass_sat_def var_st_set_lvar_def lvar32_zero_pages_from_lvar_len_def
                         typeof_def lvar_is_i32_of_lvar_def var_st_get_lvar_def is_lvar32_def disjnt_def heap_merge_def
                         sep_conj_def emp_def heap_disj_def map_disj_def option_disj_def Option.is_none_def
               split: prod.splits option.splits)
        done
      hence "ass_sat Q [ConstInt32 int32_minus_one] h st"
        using ass_wf_is(1) Grow_mem
        unfolding local_assms(5)
        by auto
      thus ?thesis
        using local_assms(1,3) mes_iss ass_wf_is
        unfolding ass_wf_def res_wf_def
        apply simp
        apply (metis prod.collapse)
        done
    next
      case 2
      then obtain j_m n_m m_m where mem_iss:"locs = locs'"
                                            "smem_ind s i = Some j_m"
                                            "s.mem s ! j_m = m_m"
                                            "mem_size m_m = n_m"
                                            "s' = s\<lparr>s.mem := s.mem s[j_m := mem_grow (s.mem s ! j_m)(Wasm_Base_Defs.nat_of_int k_g)]\<rparr>"
                                            "res = RValue (vcsf @ [ConstInt32 (int_of_nat n_m)])"
        by fastforce
      have "\<exists>h''.
                             ass_sat Q [ConstInt32 (Wasm_Base_Defs.int_of_nat n_m)] h'' st
                             \<and> heap_disj h'' hf
                             \<and> reifies_s s' i (heap_merge h'' hf) st fs
                             \<and> reifies_loc locs' st
                             \<and> snd (snd st) = lvar_st"
        using lvar32_zero_pages_from_lvar_len_reifies[OF ass_wf_is(1,2,3) mem_iss(2,3,4) _ Grow_mem(1,2)]
              mem_iss ass_wf_is local_assms(1,5)
        by auto
      thus ?thesis
        using mem_iss(6) local_assms(1)
        unfolding res_wf_def
        apply simp
        apply (metis eq_snd_iff)
        done
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Function cl tn tm tls es St St' H H' fs assms ls r)
  {
    fix \<Gamma> vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (St \<^sub>s|\<^sub>h H)"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [Callcl cl]) \<Down>n{(labs, ret, i)} (s', locs', res)"

    obtain \<Gamma>l where \<Gamma>l_def:"\<Gamma>l = (fs, []::'a ass list, Some (St' \<^sub>s|\<^sub>h  H'))"
      by blast
    obtain gs where st_is:"st = (gs, locs, lvar_st)"
      using local_assms(3)
      unfolding ass_wf_def reifies_loc_def
      by (metis prod.collapse)
    hence "ass_sat ([] \<^sub>s|\<^sub>h (\<lambda>h vl_st. H h vl_st \<and> args_ass St (length St) vl_st \<and> zeros_ass (length St) tls vl_st)) [] h (gs, vcs @ n_zeros tls, lvar_st)"
      using ass_sat_local[OF _ Function(4,6)] local_assms(3)
      unfolding ass_wf_def
      by fastforce
    hence 3:"ass_wf lvar_st (Some (length tm)) (fs, [], Some (St' \<^sub>s|\<^sub>h  H')) [] (vcs @ n_zeros tls) s hf (gs, vcs @ n_zeros tls, lvar_st) h [] ([] \<^sub>s|\<^sub>h (\<lambda>h vl_st. H h vl_st \<and> args_ass St (length tn) vl_st \<and> zeros_ass (length tn) tls vl_st))"
      using \<Gamma>l_def local_assms(1,3) Function(2,3) st_is
      unfolding ass_wf_def reifies_loc_def reifies_lab_def reifies_ret_def reifies_s_def reifies_glob_def
      by simp
    moreover
    have "length vcs = length tn"
      using Function(2) local_assms(3) list_all2_lengthD
      unfolding ass_wf_def
      by (fastforce simp add: stack_ass_sat_def)
    hence 1:"(s, locs, ($$* vcsf) @ [Local (length tm) i (vcs @ n_zeros tls) [$Block ([] _> tm) es]]) \<Down>n{(labs, ret, i)} (s', locs', res)"
      using callcl_native_imp_local[OF _ Function(1)] local_assms(4)
      by blast
    obtain lvs' lres lrvs where lres_def:
      "(s, vcs @ n_zeros tls, [$Block ([] _> tm) es]) \<Down>n{([], Some (length tm), i)} (s', lvs', lres)"
      "locs = locs'"
      "((lres = RTrap \<and> res = RTrap) \<or>
       ((lres = RValue lrvs \<or> lres = RReturn lrvs) \<and> res = RValue (vcsf @ lrvs)))"
      using local_imp_body[OF 1]         
      by blast
    have 2:"(fs, [], Some (St' \<^sub>s|\<^sub>h H')) \<Turnstile>_n {([] \<^sub>s|\<^sub>h
                             (\<lambda>h v_st.
                                 H h v_st \<and>
                                 args_ass St (length tn) v_st \<and>
                                 zeros_ass (length tn) tls v_st))}
                             [$Block ([] _> tm) es] {(St' \<^sub>s|\<^sub>h H')}"
      using local_assms(2) Function(9)
      unfolding valid_triples_assms_n_def
      by (auto simp add: valid_triples_n_def)
    have 4:"res_wf lvar_st (fs, [], Some (St' \<^sub>s|\<^sub>h H')) lres lvs' s' hf [] (St' \<^sub>s|\<^sub>h H')"
      using res_wf_valid_triple_n_intro[OF 2 3, of "[]"] lres_def(1)
      by simp
    have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf (St' \<^sub>s|\<^sub>h H')"
    proof (cases lres)
      case (RValue x1)
      obtain h' h'' gl' where h'_is:
          "ass_sat (St' \<^sub>s|\<^sub>h H') lrvs h'' (gl', lvs', lvar_st)"
          "heap_disj h'' hf"
          "h' = heap_merge h'' hf"
          "reifies_s s' i h' (gl', lvs', lvar_st) fs"
          "reifies_loc lvs' (gl', lvs', lvar_st)"
        using 4 lres_def(3)
        unfolding res_wf_def reifies_loc_def
        by fastforce
      have "ass_sat (St' \<^sub>s|\<^sub>h H') lrvs h'' (gl', locs', lvar_st)"
        using h'_is(1) ass_sat_ind_on_locals Function(5,7) lres_def(2)
        by blast
      moreover
      have "reifies_s s' i h' (gl', locs', lvar_st) fs"
        using h'_is(4)
        unfolding reifies_s_def reifies_glob_def
        by auto
      moreover
      have "reifies_loc locs' (gl', locs', lvar_st)"
        unfolding reifies_loc_def
        by simp
      ultimately
      show ?thesis
        using lres_def(3) h'_is(2,3) RValue local_assms(1)
        unfolding res_wf_def
        apply simp
        apply (metis prod.collapse)
        done
    next
      case (RBreak x21 x22)
      thus ?thesis
        using lres_def(3) Function(4,6)
        by blast
    next
      case (RReturn x3)
      obtain h' h'' gl' where h'_is:
          "ass_sat (St' \<^sub>s|\<^sub>h H') lrvs h'' (gl', lvs', lvar_st)"
          "heap_disj h'' hf"
          "h' = heap_merge h'' hf"
          "reifies_s s' i h' (gl', lvs', lvar_st) fs"
          "reifies_loc lvs' (gl', lvs', lvar_st)"
        using 4 lres_def(3)
        unfolding res_wf_def reifies_loc_def
        by fastforce
      have "ass_sat (St' \<^sub>s|\<^sub>h H') lrvs h'' (gl', locs', lvar_st)"
        using h'_is(1) ass_sat_ind_on_locals Function(5,7) lres_def(2)
        by blast
      moreover
      have "reifies_s s' i h' (gl', locs', lvar_st) fs"
        using h'_is(4)
        unfolding reifies_s_def reifies_glob_def
        by auto
      moreover
      have "reifies_loc locs' (gl', locs', lvar_st)"
        unfolding reifies_loc_def
        by simp
      ultimately
      show ?thesis
        using lres_def(3) h'_is(2,3) RReturn local_assms(1)
        unfolding res_wf_def
        apply simp
        apply (metis prod.collapse)
        done
    next
      case RTrap
      thus ?thesis
        using 4
        unfolding res_wf_def
        by simp
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply auto
    done
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
  {
    fix fs ls r vcs h st s locs labs ret lvar_st hf vcsf s' locs' res
    assume local_assms:"\<Gamma> = (fs,ls,r)"
                       "(fs,[],None) \<TTurnstile>_n assms"
                       "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ es @ es') \<Down>n{(labs, ret, i)} (s', locs', res)"
    consider (1) "(\<exists>s'' locs'' rvs. ((s,locs,($$* vcsf) @ ($$* vcs) @ es) \<Down>n{(labs, ret, i)} (s'',locs'',RValue rvs)) \<and> ((s'',locs'',($$*rvs)@es') \<Down>n{(labs, ret, i)} (s',locs',res)))"
      | (2)"(((s,locs,($$* vcsf) @ ($$* vcs) @ es) \<Down>n{(labs, ret, i)} (s',locs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
      using reduce_to_app[of s locs "($$* vcsf) @ ($$* vcs) @ es" "es'" n "(labs, ret, i)" s' locs' res]
            local_assms(4)
      by fastforce
    hence "res_wf lvar_st \<Gamma> res locs' s' hf vcsf R"
    proof (cases)
      case 1
      then obtain s'' locs'' res' rvs where res'_def:
         "(s, locs, ($$* vcsf) @ ($$* vcs) @ es) \<Down>n{(labs, ret,i)} (s'', locs'', res')"
         "(s'', locs'', ($$* rvs) @ es') \<Down>n{(labs, ret, i)} (s', locs', res)"
         "res' = RValue rvs"
        by blast
      have "res_wf lvar_st \<Gamma> res' locs'' s'' hf vcsf Q"
      proof -
        have "\<Gamma> \<TTurnstile>_n {(P, es, Q)}"
          using Seq(3) local_assms(1,2)
          unfolding valid_triples_assms_n_def
          by simp
        thus ?thesis
          using local_assms(1,3) res'_def(1)
          unfolding valid_triple_defs
          apply (cases h)
          apply (cases st)
          apply (cases hf)
          apply auto
          done
      qed
      then obtain vcs' where vcs'_def:"rvs = vcsf @ vcs'"
         "\<exists>h' h'' st'.
          ass_sat Q vcs' h'' st' \<and>
          heap_disj h'' hf \<and>
          h' = heap_merge h'' hf \<and>
          reifies_s s'' i h' st'
           fs \<and>
          reifies_loc locs'' st' \<and>
          snd (snd st') = lvar_st"
        using res'_def(3) local_assms(1)
        unfolding res_wf_def
        by fastforce
      then obtain st'' h'' where st''_def:"ass_wf lvar_st ret \<Gamma> labs locs'' s'' hf st'' h'' vcs' Q"
        using res'_def(3) encapsulated_module_axioms local_assms(1,3)
        unfolding res_wf_def ass_wf_def
        by fastforce
      have "\<Gamma> \<Turnstile>_n {Q} es' {R}"
        using Seq(4) local_assms(1,2)
        unfolding valid_triples_assms_n_def valid_triples_n_def
        by simp
      thus ?thesis
        using st''_def res'_def(2) local_assms(1)
        unfolding valid_triple_n_def
        by (metis append_assoc map_append vcs'_def(1))
    next
      case 2
      have "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
      proof -
        have "\<Gamma> \<TTurnstile>_n {(P, es, Q)}"
          using Seq(3) local_assms(1,2)
          unfolding valid_triples_assms_n_def
          by simp
        thus ?thesis
          using local_assms(1,3) 2
          unfolding valid_triple_defs
          apply (cases h)
          apply (cases st)
          apply (cases hf)
          apply auto
          done
      qed
      thus ?thesis
        using 2
        unfolding res_wf_def
        apply (cases res)
           apply auto
        done
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    apply (cases \<Gamma>)
    apply auto
    done
next
  case (Conseq fs ls' rs' assms P' es Q' ls rs P Q)
  thus ?case
    using valid_triple_assms_n_conseq
    by blast
next
  case (Exists fs ls r assms P es Q lv)
  {
    fix \<Gamma> vcs h st s locs labs ret lvar_st vcsf s' locs' res hf
    assume local_assms:"\<Gamma> = (fs, map (Ex_ass lv) ls, map_option (Ex_ass lv) r)"
                       "(fst \<Gamma>,[],None) \<TTurnstile>_n assms"
                       "(ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs (Ex_ass lv P))"
                       "(s,locs,($$*vcsf)@($$*vcs)@es) \<Down>n{(labs,ret,i)} (s',locs', res)"
    have ass_wf_is:"ass_sat (Ex_ass lv P) vcs h st"
                   "heap_disj h hf"
                   "reifies_s s i (heap_merge h hf) st (fst \<Gamma>)"
                   "reifies_loc locs st"
                   "reifies_lab labs \<Gamma>"
                   "reifies_ret ret \<Gamma>"
                   "snd (snd st) = lvar_st"
      using local_assms(3)
      unfolding ass_wf_def
      by auto
    obtain st' v where st'_is:"ass_sat P vcs h st'"
                              "st' = (var_st_set_lvar st lv v)"
      using ass_wf_is(1)
      by simp blast
    have "reifies_s s i (heap_merge h hf) st' (fst \<Gamma>)"
         "reifies_loc locs st'"
      using st'_is local_assms(1) ass_wf_is(3,4)
      by (simp_all add: reifies_loc_def var_st_set_lvar_def reifies_s_def reifies_glob_def
                   split: prod.splits)
    hence 0:"(ass_wf (snd (snd st')) ret (fs, ls, r) labs locs s hf st' h vcs P)"
      using st'_is ass_wf_is(2,5,6) local_assms(1)
      unfolding ass_wf_def
      apply (simp add: reifies_lab_def reifies_ret_def)
      apply (metis (mono_tags, lifting) ass_stack_len.simps(2) comp_def map_option_cong option.map_comp)
      done
    have 1:"(fs, ls, r) \<Turnstile>_n {P} es {Q}"
      using Exists(2) local_assms(2) local_assms(1)
      unfolding valid_triple_defs
      by auto
    have res_q:"res_wf (snd (snd st')) (fs, ls, r) res locs' s' hf vcsf Q"
      using res_wf_valid_triple_n_intro[OF 1 0 local_assms(4)]
      by -
    have "res_wf lvar_st (fs, map (Ex_ass lv) ls, map_option (Ex_ass lv) r) res locs' s' hf vcsf (Ex_ass lv Q)"
    proof (cases res)
      case (RValue x1)
      thus ?thesis
        using res_q local_assms(1) st'_is
        unfolding res_wf_def
        apply (simp add: var_st_set_lvar_def reifies_s_def reifies_loc_def reifies_glob_def split: prod.splits)
        apply (metis ass_wf_is(7) prod.sel(2))
        done
    next
      case (RBreak x21 x22)
      thus ?thesis
        using res_q local_assms(1) st'_is
        unfolding res_wf_def
        apply (simp add: var_st_set_lvar_def reifies_s_def reifies_loc_def reifies_glob_def split: prod.splits)
        apply (metis ass_wf_is(7) prod.sel(2))
        done
    next
      case (RReturn x3)
      thus ?thesis
        using res_q local_assms(1) st'_is
        unfolding res_wf_def
        apply (simp add: var_st_set_lvar_def reifies_s_def reifies_loc_def reifies_glob_def split: prod.splits)
        apply (metis ass_wf_is(7) prod.sel(2))
        done
    next
      case RTrap
      thus ?thesis
        using res_q
        unfolding res_wf_def
        by simp
    qed
  }
  thus ?case
    unfolding valid_triple_defs
    by auto
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
    by (metis valid_triple_defs(5,6) singletonD)
qed

end
end
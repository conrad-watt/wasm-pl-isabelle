theory Wasm_Assertions_Shallow imports "Wasm_Big_Step" begin

typedef lvar = "UNIV :: (nat) set" ..

(* global, local, logical variables*)
datatype var = Gl nat | Lc nat | Lv lvar

datatype 'a lvar_v = V_p v | V_n nat | V_b byte | V_a 'a

abbreviation "case_ret r r_new \<equiv> case_option r_new (\<lambda>x. Some x) r"

lemma case_ret_None[simp]:"case_ret r None = r"
  by (cases r) auto

(* variable store *)
(* global, local, logical variables*)
type_synonym 'a var_st = "global list \<times> v list \<times> (lvar, 'a lvar_v) map"

definition var_st_get_local :: "'a var_st \<Rightarrow> nat \<Rightarrow> v option" where
  "var_st_get_local st n \<equiv> let st_l = (fst (snd st)) in
                            (if (n < length st_l)
                            then Some (st_l!n)
                            else None)"

definition var_st_set_local :: "'a var_st \<Rightarrow> nat \<Rightarrow> v \<Rightarrow> 'a var_st" where
  "var_st_set_local st n v \<equiv> let (gs, vs, lvs) = st in
                             (if (n < length vs)
                             then (gs, vs[n := v], lvs)
                             else st)"

definition var_st_get_global :: "'a var_st \<Rightarrow> nat \<Rightarrow> global option" where
  "var_st_get_global st n \<equiv> let st_g = (fst st) in
                            (if (n < length st_g)
                            then Some (st_g!n)
                            else None)"

definition var_st_set_global :: "'a var_st \<Rightarrow> nat \<Rightarrow> global \<Rightarrow> 'a var_st" where
  "var_st_set_global st n g \<equiv> let (gs, vs, lvs) = st in
                              (if (n < length gs)
                              then (gs[n := g], vs, lvs)
                              else st)"

definition var_st_set_global_v :: "'a var_st \<Rightarrow> nat \<Rightarrow> v \<Rightarrow> 'a var_st" where
  "var_st_set_global_v st n v \<equiv> let (gs, vs, lvs) = st in
                                (if (n < length gs)
                                then (gs[n := ((gs!n)\<lparr>g_val := v\<rparr>)], vs, lvs)
                                else st)"

definition var_st_get_lvar :: "'a var_st \<Rightarrow> lvar \<Rightarrow> 'a lvar_v option" where
  "var_st_get_lvar st lv \<equiv> let st_lv = (snd (snd st)) in st_lv lv"

definition var_st_set_lvar :: "'a var_st \<Rightarrow> lvar \<Rightarrow> 'a lvar_v \<Rightarrow> 'a var_st" where
  "var_st_set_lvar st l lv \<equiv> let (gs, vs, lvs) = st in
                              (gs, vs, (lvs(l \<mapsto> lv)))"

(* abstract heap with max length *)
type_synonym heap = "((nat, byte) map) \<times> (nat option)"

definition map_disj :: "('a,'b) map \<Rightarrow> ('a,'b) map \<Rightarrow> bool" where
  "map_disj m1 m2 \<equiv> Set.disjnt (dom m1) (dom m2)"

definition option_disj :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "option_disj o1 o2 \<equiv> Option.is_none o1 \<or> Option.is_none o2"

definition heap_disj :: "heap \<Rightarrow> heap \<Rightarrow> bool" where
  "heap_disj h1 h2 \<equiv> map_disj (fst h1) (fst h2) \<and> option_disj (snd h1) (snd h2)"

definition heap_merge :: "heap \<Rightarrow> heap \<Rightarrow> heap" where
  "heap_merge h1 h2 \<equiv> let (m1,s1) = h1 in
                       let (m2,s2) = h2 in
                       (m1 ++ m2, case_option s2 (\<lambda>s. Some s) s1)"

lemma heap_disj_sym: "heap_disj h1 h2 = heap_disj h2 h1"
  unfolding heap_disj_def map_disj_def option_disj_def
  using disjnt_sym
  by blast

lemma heap_merge_disj_sym:
  assumes "heap_disj h1 h2"
  shows "heap_merge h1 h2 = heap_merge h2 h1"
  using assms
  unfolding heap_disj_def heap_merge_def option_disj_def heap_disj_def map_disj_def disjnt_def
  by (auto simp add: map_add_comm split: option.splits prod.splits)

lemma heap_merge_assoc:
  shows "heap_merge h1 (heap_merge h2 h3) = heap_merge (heap_merge h1 h2) h3"
  unfolding heap_merge_def
  by (auto split: option.splits prod.splits)

lemma heap_disj_merge_sub:
  assumes "heap_disj h1 (heap_merge h2 h3)"
  shows "heap_disj h1 h2"
        "heap_disj h1 h3"
  using assms
  unfolding heap_disj_def heap_merge_def option_disj_def map_disj_def disjnt_def
  by (auto split: option.splits prod.splits)

lemma heap_disj_merge_assoc:
  assumes "heap_disj h_H h_Hf"
          "heap_disj (heap_merge h_H h_Hf) hf"
  shows "heap_disj h_H (heap_merge h_Hf hf)"
  using assms
  unfolding heap_disj_def heap_merge_def map_disj_def disjnt_def
  by (auto split: option.splits prod.splits)

lemma heap_merge_dom:
  assumes "x \<in> dom (fst (heap_merge h1 h2))"
  shows "x \<in> dom (fst h1) \<or> x \<in> dom (fst h2)"
  using assms
  unfolding heap_disj_def heap_merge_def option_disj_def heap_disj_def map_disj_def disjnt_def
  by (auto simp add: map_add_comm split: option.splits prod.splits)

lemma heap_dom_merge:
  assumes "x \<in> dom (fst h1) \<or> x \<in> dom (fst h2)"
  shows "x \<in> dom (fst (heap_merge h1 h2))"
  using assms
  unfolding heap_disj_def heap_merge_def option_disj_def heap_disj_def map_disj_def disjnt_def
  by (auto simp add: map_add_comm split: option.splits prod.splits)

lemma heap_dom_merge_eq:
  assumes "dom (fst h1) = dom(fst h2)"
  shows "dom (fst (heap_merge h1 hf)) = dom (fst (heap_merge h2 hf))"
  using assms
  unfolding heap_disj_def heap_merge_def option_disj_def heap_disj_def map_disj_def disjnt_def
  apply (simp add: map_add_comm split: option.splits prod.splits)
  apply force
  done

lemma heap_disj_merge_maps1:
  assumes "heap_disj h1 h2"
          "(fst h1) x = Some y"
  shows "fst (heap_merge h1 h2) x = Some y"
  using assms
  unfolding heap_disj_def heap_merge_def option_disj_def heap_disj_def map_disj_def disjnt_def
  apply (simp add: map_add_dom_app_simps map_add_comm split: option.splits prod.splits)
  apply (metis fst_conv map_add_comm map_add_find_right)
  done

lemma heap_disj_merge_maps2:
  assumes "heap_disj h1 h2"
          "(fst h2) x = Some y"
  shows "fst (heap_merge h1 h2) x = Some y"
  using assms
  unfolding heap_disj_def heap_merge_def option_disj_def heap_disj_def map_disj_def disjnt_def
  apply (simp add: map_add_dom_app_simps map_add_comm split: option.splits prod.splits)
  apply (metis fst_conv map_add_find_right)
  done

(* local variable reification *)
definition reifies_loc :: "[v list, 'a var_st] \<Rightarrow> bool" where
  "reifies_loc locs st \<equiv> (fst (snd st)) = locs"

(* global variable reification (with respect to a partial instance) *)
definition reifies_glob :: "[global list, nat list, 'a var_st] \<Rightarrow> bool" where
  "reifies_glob gs igs st \<equiv>
     let st_g = (fst st) in
     length st_g = (length igs) \<and> (\<forall>gn < length st_g. igs!gn < (length gs) \<and> st_g!gn = (gs!(igs!gn)))"

(* function reification (with respect to a partial instance) *)
definition reifies_func :: "[cl list, nat list, cl list] \<Rightarrow> bool" where
  "reifies_func cls icls fs \<equiv> list_all2 (\<lambda>icl f. icl < (length cls) \<and> cls!icl = f) icls fs"

(* heap reification relations *)
definition reifies_heap_contents :: "[mem, ((nat, byte) map)] \<Rightarrow> bool" where
  "reifies_heap_contents m byte_m \<equiv>
     \<forall>ind \<in> (dom byte_m). ind < mem_length m \<and> byte_m(ind) = Some (byte_at m ind)"

definition reifies_heap_length :: "[mem, nat option] \<Rightarrow> bool" where
  "reifies_heap_length m l_opt \<equiv> pred_option (\<lambda>l. mem_length m = (l * Ki64)) l_opt"

definition reifies_heap :: "[mem list, nat list, heap] \<Rightarrow> bool" where
  "reifies_heap ms im_opt h \<equiv> let im = hd im_opt in
                               im < length ms
                             \<and> reifies_heap_contents (ms!im) (fst h)
                             \<and> reifies_heap_length (ms!im) (snd h)"

(* store reification relation *)
definition reifies_s :: "[s, inst, heap, 'a var_st, cl list] \<Rightarrow> bool" where
  "reifies_s s i h st fs \<equiv> reifies_glob (globs s) (inst.globs i) st
                         \<and> reifies_func (funcs s) (inst.funcs i) fs
                         \<and> reifies_heap (mems s) (inst.mems i) h"

definition var_st_agree :: "'a var_st \<Rightarrow> var \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "var_st_agree st1 var st2 \<equiv> case var of
                                 Lc n \<Rightarrow> (var_st_get_local st1 n) = (var_st_get_local st2 n)
                               | Gl n \<Rightarrow> (var_st_get_global st1 n) = (var_st_get_global st2 n)
                               | Lv lvar \<Rightarrow> (var_st_get_lvar st1 lvar) = (var_st_get_lvar st2 lvar)"

(* shallow embedding of assertions *)
type_synonym 'a stack_ass = "(v \<Rightarrow> 'a var_st \<Rightarrow> bool) list"
type_synonym 'a heap_ass = "heap \<Rightarrow> 'a var_st \<Rightarrow> bool"

datatype 'a ass = Ass "'a stack_ass" "'a heap_ass" (infix "\<^sub>s|\<^sub>h" 60) | Ex_ass lvar "'a ass" 

type_synonym 'a triple = "'a ass \<times> e list \<times> 'a ass"

(* function list, assms, label ass, return ass *)
type_synonym 'a triple_context = "cl list \<times> 'a ass list \<times> 'a ass option"

definition add_label_ass :: "'a triple_context \<Rightarrow> 'a ass \<Rightarrow> 'a triple_context" where
  "add_label_ass \<Gamma> l \<equiv> let (fs, labs, ret) = \<Gamma> in (fs, l#labs, ret)"

definition stack_ass_sat :: "'a stack_ass \<Rightarrow> v list \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "stack_ass_sat St ves v_st = list_all2 (\<lambda>Si v. Si v v_st) St ves"

fun ass_sat :: "'a ass \<Rightarrow> v list \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "ass_sat (St \<^sub>s|\<^sub>h H) ves h v_st = (stack_ass_sat St ves v_st \<and> H h v_st)"
| "ass_sat (Ex_ass lv P) ves h st = (\<exists>v. ass_sat P ves h (var_st_set_lvar st lv v))"

fun ass_stack_len :: "'a ass \<Rightarrow> nat" where
  "ass_stack_len (St \<^sub>s|\<^sub>h H) = length St"
| "ass_stack_len (Ex_ass lv P) = ass_stack_len P"

(* label reification relation *)
definition reifies_lab :: "nat list \<Rightarrow> 'a triple_context \<Rightarrow> bool" where
  "reifies_lab lns \<Gamma> \<equiv> lns = map ass_stack_len (fst (snd \<Gamma>))"

(* return reification relation *)
definition reifies_ret :: "nat option \<Rightarrow> 'a triple_context \<Rightarrow> bool" where
  "reifies_ret rn \<Gamma> \<equiv> rn = Option.map_option ass_stack_len (snd (snd \<Gamma>))"

locale encapsulated_module =
  fixes i :: inst
  assumes encapsulated_inst_globs:"\<And> j k. \<lbrakk>j \<noteq> k; (j < length (inst.globs i)); (k < length (inst.globs i))\<rbrakk>
                                    \<Longrightarrow> (inst.globs i)!j \<noteq> (inst.globs i)!k"
begin

definition ass_wf where
  "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P \<equiv>
     ass_sat P vcs h st
      \<and> heap_disj h hf
      \<and> reifies_s s i (heap_merge h hf) st (fst \<Gamma>)
      \<and> reifies_loc locs st
      \<and> reifies_lab labs \<Gamma>
      \<and> reifies_ret ret \<Gamma>
      \<and> snd (snd st) = lvar_st"

definition res_wf where
  "res_wf lvar_st' \<Gamma> res locs' s' hf vcsf Q \<equiv>
    let (fs,lasss,rass) = \<Gamma> in
    (case res of
       RTrap \<Rightarrow> False
     | RValue rvs \<Rightarrow> \<exists>h' h'' vcs' st'.
                             ass_sat Q vcs' h'' st'
                             \<and> rvs = vcsf@vcs'
                             \<and> heap_disj h'' hf
                             \<and> h' = heap_merge h'' hf
                             \<and> reifies_s s' i h' st' fs
                             \<and> reifies_loc locs' st'
                             \<and> snd (snd st') = lvar_st'
     | RBreak n rvs \<Rightarrow> \<exists>h' h'' vcs' st'.
                             n < length lasss
                             \<and> ass_sat (lasss!n) vcs' h'' st'
                             \<and> rvs = vcs'
                             \<and> heap_disj h'' hf
                             \<and> h' = heap_merge h'' hf
                             \<and> reifies_s s' i h' st' fs
                             \<and> reifies_loc locs' st'
                             \<and> snd (snd st') = lvar_st'
     | RReturn rvs \<Rightarrow> \<exists>h' h'' vcs' st' the_rass.
                             rass = Some the_rass
                             \<and> ass_sat the_rass vcs' h'' st'
                             \<and> rvs = vcs'
                             \<and> heap_disj h'' hf
                             \<and> h' = heap_merge h'' hf
                             \<and> reifies_s s' i h' st' fs
                             \<and> reifies_loc locs' st'
                             \<and> snd (snd st') = lvar_st')"

(* TODO: frame? ? ? ?*)
definition valid_triple :: "'a triple_context \<Rightarrow> 'a ass \<Rightarrow> e list \<Rightarrow> 'a ass \<Rightarrow> bool" ("_ \<Turnstile> {_}_{_}" 60) where
  "(\<Gamma> \<Turnstile> {P}es{Q}) \<equiv> \<forall>vcs h st s locs labs labsf ret retf lvar_st hf vcsf s' locs' res.
                                      ((ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P \<and>
                                      ((s,locs,($$*vcsf)@($$*vcs)@es) \<Down>{(labs@labsf,case_ret ret retf,i)} (s',locs', res))) \<longrightarrow>
                                      res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q)"

definition valid_triples :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_ \<TTurnstile> _" 60) where
  "\<Gamma> \<TTurnstile> specs \<equiv> \<forall>(P,es,Q) \<in> specs. (\<Gamma> \<Turnstile> {P}es{Q})"

(* TODO: frame? ? ? ?*)
definition valid_triple_n :: "'a triple_context \<Rightarrow> nat \<Rightarrow> 'a ass \<Rightarrow> e list \<Rightarrow> 'a ass \<Rightarrow> bool" ("_ \<Turnstile>'_ _ {_}_{_}" 60) where
  "(\<Gamma> \<Turnstile>_k {P}es{Q}) \<equiv> \<forall>vcs h st s locs labs labsf ret retf lvar_st hf vcsf s' locs' res.
                                      ((ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P \<and>
                                      ((s,locs,($$*vcsf)@($$*vcs)@es) \<Down>k{(labs@labsf,case_ret ret retf,i)} (s',locs', res))) \<longrightarrow>
                                      res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q)"

definition valid_triples_n :: "'a triple_context \<Rightarrow> nat \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_ \<TTurnstile>'_ _ _" 60) where
  "(\<Gamma> \<TTurnstile>_n specs) \<equiv> \<forall>(P,es,Q) \<in> specs. (\<Gamma> \<Turnstile>_n {P}es{Q})"

definition valid_triples_assms :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_\<bullet>_ \<TTurnstile> _" 60) where
  "(\<Gamma>\<bullet>assms \<TTurnstile> specs) \<equiv> ((fst \<Gamma>,[],None) \<TTurnstile> assms) \<longrightarrow> (\<Gamma> \<TTurnstile> specs)"

definition valid_triples_assms_n :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> nat \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_\<bullet>_ \<TTurnstile>'_ _ _" 60) where
  "(\<Gamma>\<bullet>assms \<TTurnstile>_n specs) \<equiv> ((fst \<Gamma>,[],None) \<TTurnstile>_n assms) \<longrightarrow> (\<Gamma> \<TTurnstile>_n specs)"

lemmas valid_triple_defs = valid_triple_def valid_triples_def valid_triples_assms_def
                           valid_triple_n_def valid_triples_n_def valid_triples_assms_n_def

definition ass_conseq :: "'a ass \<Rightarrow> 'a ass \<Rightarrow> v list \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "ass_conseq P P' vcs h st \<equiv> (ass_stack_len P \<le> ass_stack_len P' \<and> (ass_sat P vcs h st \<longrightarrow> ass_sat P' vcs h st))"

lemma extend_context_res_wf:
  assumes "res_wf lvar_st' (fs,[],None) res locs' s' hf vcsf Q"
  shows "res_wf lvar_st' (fs,ls,rs) res locs' s' hf vcsf Q"
  using assms
  unfolding res_wf_def
  by (auto split: res_b.splits)

lemma extend_context_res_wf_value_trap:
  assumes "res_wf lvar_st' (fs,ls,rs) res locs' s' hf vcsf Q"
          "\<exists>rvs. res = RValue rvs \<or> res = RTrap"
  shows "res_wf lvar_st' (fs,ls',rs') res locs' s' hf vcsf Q"
  using assms
  unfolding res_wf_def
  by (auto split: res_b.splits)

lemma ex_lab:"\<exists>l. lab = ass_stack_len l"
  using ass_stack_len.simps(1)
  by (metis Ex_list_of_length)

lemma ex_labs:"\<exists>ls. labs = map ass_stack_len ls"
  using ex_lab
  by (simp add: ex_lab ex_map_conv)

lemma ex_ret:"\<exists>rs. ret = map_option ass_stack_len rs"
  using ex_lab
  by (metis not_Some_eq option.simps(8) option.simps(9))

lemma res_wf_valid_triple_n_intro:
  assumes "\<Gamma> \<Turnstile>_k {P}es{Q}"
          "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P"
          "((s,locs,($$*vcsf)@($$*vcs)@es) \<Down>k{(labs@labsf,case_ret ret retf,i)} (s',locs', res))"
  shows "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
  using assms
  unfolding valid_triple_n_def
  by blast

lemma res_wf_valid_triple_n_intro_tight:
  assumes "\<Gamma> \<Turnstile>_k {P}es{Q}"
          "ass_wf lvar_st ret \<Gamma> labs locs s hf st h vcs P"
          "((s,locs,($$*vcsf)@($$*vcs)@es) \<Down>k{(labs,ret,i)} (s',locs', res))"
  shows "res_wf lvar_st \<Gamma> res locs' s' hf vcsf Q"
  using res_wf_valid_triple_n_intro[OF assms(1,2), of vcsf "[]" None] assms(3)
  by fastforce

lemma res_wf_valid_triple_n_not_rvalue:
  assumes "res_wf lvar_st \<Gamma> res locs s hf vcsf Q"
          "\<nexists>vs. res = RValue vs"
  shows "res_wf lvar_st \<Gamma> res locs s hf vcsf Q'"
  using assms
  unfolding res_wf_def
  by (cases res) auto

lemma extend_context_call:
  assumes "(fs,ls,rs) \<Turnstile>_n {P} [$Call j] {Q}"
  shows "(fs,ls',rs') \<Turnstile>_n {P} [$Call j] {Q}"
proof -
  {
    fix vcs h st s locs labs labsf ret retf lvar_st hf vcsf s' locs' res
    assume local_assms:"ass_wf lvar_st ret (fs, ls', rs') labs locs s hf st h vcs P"
                       "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Call j]) \<Down>n{(labs@labsf, case_ret ret retf, i)} (s', locs', res)"
    obtain ret' labs' where "ass_wf lvar_st ret' (fs, ls, rs) labs' locs s hf st h vcs P"
      using local_assms(1) 
      unfolding ass_wf_def reifies_s_def reifies_lab_def reifies_ret_def
      by fastforce
    moreover
    have "(s, locs, ($$* vcsf) @ ($$* vcs) @ [$Call j]) \<Down>n{(labs'@labsf, case_ret ret' retf, i)} (s', locs', res)"
      by (metis append_assoc calln_context local_assms(2) map_append)
    ultimately
    have "res_wf lvar_st (fs, ls, rs) res locs' s' hf vcsf Q"
      using assms local_assms(2)
      unfolding valid_triple_n_def
      by fastforce
    hence "res_wf lvar_st (fs, ls', rs') res locs' s' hf vcsf Q"
      using extend_context_res_wf_value_trap call_value_trap local_assms(2)
      by (metis (no_types, lifting) append_assoc map_append)
  }
  thus ?thesis
    unfolding valid_triple_n_def
    by blast
qed

lemma reifies_func_ind:
  assumes "reifies_func (funcs s) (inst.funcs i) fs"
          "j < length fs"
  shows "sfunc s i j = fs!j"
  using assms
  unfolding reifies_func_def
  by (simp add: list_all2_conv_all_nth sfunc_def sfunc_ind_def)

lemma valid_triples_n_emp: "\<Gamma> \<TTurnstile>_n {}"
  unfolding valid_triples_n_def
  by blast

lemma res_wf_conseq:
  assumes "res_wf l_st (fs,ls,rs) res locs' s' hf vcsf P"
          "\<forall>vs h v_st. (list_all2 (\<lambda>L L'. ass_conseq L L' vs h v_st) ls ls')"
          "\<forall>vs h v_st. (rel_option (\<lambda>R R'. ass_conseq R R' vs h v_st) rs rs')"
          "\<forall>vs h v_st. (ass_sat P vs h v_st \<longrightarrow> ass_sat P' vs h v_st)"
  shows "res_wf l_st (fs,ls',rs') res locs' s' hf vcsf P'"
proof (cases res)
  case (RValue x1)
  thus ?thesis
    using assms
    unfolding res_wf_def
    apply simp
    apply metis
    done
next
  case (RBreak x21 x22)
  thus ?thesis
    using assms
    unfolding res_wf_def
    apply (simp add: ass_conseq_def)
    apply (metis (no_types, lifting) list_all2_conv_all_nth)
    done
next
  case (RReturn x3)
  thus ?thesis
    using assms(1,3)
    unfolding res_wf_def
    apply (cases rs; cases rs')
    apply (simp_all add: ass_conseq_def)
    apply blast
    done
next
  case RTrap
  thus ?thesis
    using assms
    unfolding res_wf_def
    by simp
qed

lemma stack_ass_sat_len:
  assumes "ass_sat P vcs h st"
  shows "length vcs = ass_stack_len P"
  using assms
proof (induction rule: ass_sat.induct)
  case (1 St H ves h v_st)
  thus ?case
    apply (simp add: stack_ass_sat_def)
    apply (metis list_all2_lengthD)
    done
qed auto

lemma stack_ass_sat_len1:
  assumes "ass_sat P vcs h st"
          "ass_sat P vcs' h st"
  shows "length vcs = length vcs'"
  using stack_ass_sat_len[OF assms(1)] stack_ass_sat_len[OF assms(2)]
  by simp

lemma ass_sat_len_eq_lab:
  assumes "(list_all2 (\<lambda>L L'. ass_conseq L L' vcs h st) ls ls')"
  shows "(list_all2 (\<lambda>L L'. ((\<not>ass_sat L vcs h st \<and> (ass_stack_len L \<le> ass_stack_len L')) \<or> (ass_stack_len L = ass_stack_len L'))) ls ls')"
  using assms
  unfolding ass_conseq_def list_all2_conv_all_nth
  by (metis stack_ass_sat_len)

lemma ass_sat_len_eq_ret:
  assumes "(rel_option (\<lambda>R R'. ass_conseq R R' vcs h st) rs rs')"
  shows "(rel_option (\<lambda>R R'. ((\<not>ass_sat R vcs h st \<and> (ass_stack_len R \<le> ass_stack_len R')) \<or> (ass_stack_len R = ass_stack_len R'))) rs rs')"
  using assms
  unfolding ass_conseq_def
  apply (cases rs; cases rs')
  apply simp_all
  apply (metis stack_ass_sat_len)
  done

lemma ass_wf_conseq1:
  assumes "ass_wf lvar_st ret (fs,ls,rs) labs locs s hf st h vcs P"
          "(ass_sat P vcs h st \<longrightarrow> ass_sat P' vcs h st)"
  shows "ass_wf lvar_st ret (fs,ls,rs) labs locs s hf st h vcs P'"
  using assms
  unfolding ass_wf_def
  by (auto simp add: reifies_lab_def reifies_ret_def)

lemma rel_option_to_eq_map_option:
  assumes
    "rel_option f x y" and
    "\<And>a b. f a b \<Longrightarrow> g a = g b"
  shows "map_option g x = map_option g y"
  using assms
  by (induction x y rule: option.rel_induct; simp)

lemma list_all2_to_eq_map:
  assumes
    "list_all2 f xs ys" and
    "\<And>a b. f a b \<Longrightarrow> g a = g b"
  shows "map g xs = map g ys"
  using assms
  by (induction xs ys rule: list.rel_induct; simp)

lemma ass_wf_conseq2:
  assumes "ass_wf lvar_st ret (fs,ls,rs) labs locs s hf st h vcs P"
          "(list_all2 (\<lambda>L L'. (ass_stack_len L = ass_stack_len L') \<and> ass_conseq L L' vcs h st) ls ls')"
          "(rel_option (\<lambda>R R'. (ass_stack_len R = ass_stack_len R') \<and> ass_conseq R R' vcs h st) rs rs')"
        shows "ass_wf lvar_st ret (fs,ls',rs') labs locs s hf st h vcs P"
proof -
  show ?thesis
    using assms
    unfolding ass_wf_def ass_conseq_def
    unfolding reifies_lab_def reifies_ret_def
    by (auto intro: list_all2_to_eq_map rel_option_to_eq_map_option)
qed

lemma valid_triple_assms_n_label_false:
  assumes "res_wf lvar_st (fs,ls,rs) res locs' s' hf vcsf Q"
          "j \<ge> length ls \<or> (\<forall>vcs h st. \<not>ass_sat (ls!j) vcs h st)"
  shows "res \<noteq> RBreak j rvs"
  using assms
  unfolding res_wf_def
  by (auto split: res_b.splits)

lemma valid_triple_assms_n_return_false:
  assumes "res_wf lvar_st (fs,ls,rs) res locs' s' hf vcsf Q"
          "rs = None \<or> (\<forall>vcs h st. \<not>ass_sat (the rs) vcs h st)"
  shows "res \<noteq> RReturn rvs"
  using assms
  unfolding res_wf_def
  by (auto split: res_b.splits)

lemma valid_triple_n_conseq:
  assumes "(fs,ls,rs) \<Turnstile>_n {P'} es {Q'}"
          "\<forall>vs h v_st. (list_all2 (\<lambda>L L'. ass_conseq L L' vs h v_st) ls ls') \<and>
                       (rel_option (\<lambda>R R'. ass_conseq R R' vs h v_st) rs rs') \<and>
                       (ass_sat P vs h v_st \<longrightarrow> ass_sat P' vs h v_st) \<and>
                       (ass_sat Q' vs h v_st \<longrightarrow> ass_sat Q vs h v_st)"
  shows "(fs,ls',rs') \<Turnstile>_n {P} es {Q}"
proof -
  {
    fix vcs h st s locs labs' labsf' ret' retf' lvar_st hf vcsf s' locs' res
    assume local_assms:"ass_wf lvar_st ret' (fs,ls',rs') labs' locs s hf st h vcs P"
                       "(s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs'@labsf', case_ret ret' retf', i)} (s', locs', res)"
    have "ass_wf lvar_st ret' (fs,ls',rs') labs' locs s hf st h vcs P'"
      using ass_wf_conseq1[OF local_assms(1)] assms(2)
      by blast
    then obtain labs ret where labs_def:"ass_wf lvar_st ret (fs,ls,rs) labs locs s hf st h vcs P'"
                                        "length labs = length labs'"
                                        "length ls = length ls'"
                                        "length (labs'@labsf') = length (labs@labsf')"
      unfolding ass_wf_def reifies_lab_def reifies_ret_def
      by simp (meson assms(2) list_all2_conv_all_nth)
    have "res_wf lvar_st (fs,ls',rs') res locs' s' hf vcsf Q"
    proof (cases res)
      case (RValue x1)
      hence "(s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs@labsf', case_ret ret retf', i)} (s', locs', res)"
        using reduce_to_n_not_break_n_return[OF local_assms(2)] labs_def(2)
        by simp
      hence "res_wf lvar_st (fs,ls,rs) res locs' s' hf vcsf Q'"
        using assms(1) labs_def
        unfolding valid_triple_n_def
        by fastforce
      thus ?thesis
        using assms(2) RValue
        unfolding res_wf_def
        by fastforce
    next
      case (RBreak ib vbs)
      have 0:"ib < length (labs'@labsf')"
        using local_assms(2) RBreak reduce_to_n_break_n
        by fastforce
      have b0:"(s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs'@labsf', case_ret ret' retf', i)} (s', locs', RBreak ib vbs)"
        using local_assms(2) RBreak
        by simp
      show ?thesis
      proof (cases "labs!ib \<noteq> labs'!ib")
        case True
        have "\<And>vs h v_st. list_all2 (\<lambda>L L'. \<not> ass_sat L vs h v_st \<and> ass_stack_len L \<le> ass_stack_len L' \<or> ass_stack_len L = ass_stack_len L') ls ls'"
          using ass_sat_len_eq_lab assms(2)
          by blast
        hence 1:"\<And>vcs h st. ib < length labs' \<Longrightarrow> \<not> ass_sat (ls!ib) vcs h st"
                "ib < length labs' \<Longrightarrow> labs!ib \<le> labs'!ib"
                "ib < length labs' \<Longrightarrow> labs!ib = ass_stack_len (ls!ib)"
                "ib < length labs' \<Longrightarrow> labs'!ib = ass_stack_len (ls'!ib)"
          using True 0 labs_def local_assms(1)
          unfolding list_all2_conv_all_nth ass_wf_def reifies_lab_def
          by fastforce+
        obtain vbs' where 2:"((s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs@labsf', case_ret ret retf', i)} (s', locs', RBreak ib vbs'))"
          using reduce_to_n_break_n2[OF reduce_to_n_not_return[OF b0] labs_def(4)] 0 1(2)
          by simp (metis True append_Nil2 labs_def(2) nth_append)
        thus ?thesis
          using res_wf_valid_triple_n_intro[OF assms(1) labs_def(1) 2] 1(1) RBreak
          unfolding res_wf_def
          by (simp split: res_b.splits) (metis True append_Nil2 labs_def(2) nth_append)
      next
        case False
        hence "(s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs@labsf', case_ret ret retf', i)} (s', locs', res)"
          using reduce_to_n_not_break_n_return[OF local_assms(2), of "labs@labsf'"] RBreak
                labs_def(2)
          by simp (metis nth_append)
        hence "res_wf lvar_st (fs,ls,rs) res locs' s' hf vcsf Q'"
          using assms(1) labs_def
          unfolding valid_triple_n_def
          by fastforce
        thus ?thesis
          using assms(2) RBreak
          unfolding res_wf_def ass_conseq_def
          by simp (metis (mono_tags, lifting) list_all2_conv_all_nth)
      qed
    next
      case (RReturn vrs)
      show ?thesis
      proof (cases "(pred_option (\<lambda>r_r. (case_ret ret retf') \<noteq> Some r_r) (case_ret ret' retf'))")
        case True
        obtain r_r r_r' rs'_r rs_r where r_r'_def:"ret = Some r_r"
                                                  "ret' = Some r_r'"
                                                  "rs' = Some rs'_r"
                                                  "rs = Some rs_r"

          using reduce_to_n_return1 local_assms(1,2) RReturn assms(2) labs_def True
          unfolding ass_wf_def reifies_ret_def
          by (fastforce split: option.splits)
        have "ass_stack_len rs_r \<noteq> ass_stack_len rs'_r"
          using local_assms(1) labs_def r_r'_def True
          unfolding ass_wf_def reifies_ret_def
          by simp
        moreover
        have "\<And>vs h v_st. rel_option (\<lambda>R R'. (\<not>ass_sat R vs h v_st \<and> (ass_stack_len R \<le> ass_stack_len R')) \<or> ass_stack_len R = ass_stack_len R') rs rs'"
          using ass_sat_len_eq_ret assms(2)
          by blast
        ultimately
        have 1:"\<And>vcs h st. \<not> ass_sat rs_r vcs h st \<and> ass_stack_len rs_r \<le> ass_stack_len rs'_r"
          using r_r'_def
          by simp
        hence "r_r \<le> r_r'"
          using r_r'_def local_assms(1)
          unfolding ass_wf_def reifies_ret_def
          by (metis (mono_tags, lifting) ass_wf_def eq_snd_iff labs_def(1) option.inject option.map(2) reifies_ret_def)
        then obtain vrs' where "((s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs@labsf', case_ret ret retf', i)} (s', locs', RReturn vrs'))"
          using local_assms(2) RReturn reduce_to_n_return2 reduce_to_n_not_break_n r_r'_def(1,2)
          by (metis labs_def(4) option.simps(5) res_b.distinct(7))
        thus ?thesis
          using assms(1) labs_def 1 r_r'_def RReturn
          unfolding valid_triple_n_def res_wf_def
          apply (cases "hf")
          apply (cases "st")
          apply (cases "h")
          apply (simp split: res_b.splits option.splits)
          apply metis
          done
      next
        case False
        hence "(s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs@labsf', case_ret ret retf', i)} (s', locs', res)"
          using reduce_to_n_not_break_n_return[OF local_assms(2), of "labs@labsf'" "case_ret ret retf'"] RReturn labs_def(2)
          by auto
        hence "res_wf lvar_st (fs,ls,rs) res locs' s' hf vcsf Q'"
          using assms(1) labs_def
          unfolding valid_triple_n_def
          by fastforce
        thus ?thesis
          using assms(2) RReturn
          unfolding res_wf_def ass_conseq_def
          by simp (metis (no_types, lifting) option.rel_cases option.sel)
      qed
    next
      case RTrap
      hence "(s, locs, ($$*vcsf)@($$*vcs)@es) \<Down>n{(labs@labsf', case_ret ret retf', i)} (s', locs', res)"
        using reduce_to_n_not_break_n_return[OF local_assms(2)] labs_def(2)
        by auto
      hence "res_wf lvar_st (fs,ls,rs) res locs' s' hf vcsf Q'"
        using assms(1) labs_def
        unfolding valid_triple_n_def
        by fastforce
      thus ?thesis
        using assms(2) RTrap
        unfolding res_wf_def
        by fastforce
    qed
  }
  thus ?thesis
    unfolding valid_triple_n_def
    by blast
qed

lemma valid_triple_assms_n_conseq:
  assumes "((fs,ls,rs)\<bullet>assms \<TTurnstile>_n {(P',es,Q')})"
          "\<forall>vs h v_st. (list_all2 (\<lambda>L L'. ass_conseq L L' vs h v_st) ls ls') \<and>
                       (rel_option (\<lambda>R R'. ass_conseq R R' vs h v_st) rs rs') \<and>
                       (ass_sat P vs h v_st \<longrightarrow> ass_sat P' vs h v_st) \<and>
                       (ass_sat Q' vs h v_st \<longrightarrow> ass_sat Q vs h v_st)"
  shows "((fs,ls',rs')\<bullet>assms \<TTurnstile>_n {(P,es,Q)})"
  using valid_triple_n_conseq[OF _ assms(2)] assms(1)
  unfolding valid_triples_assms_n_def valid_triples_n_def
  by simp
end

end
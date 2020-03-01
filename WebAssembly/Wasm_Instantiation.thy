theory Wasm_Instantiation imports Wasm_Module_Checker Wasm_Interpreter_Properties begin

fun alloc_Xs :: "(s \<Rightarrow> 'a \<Rightarrow> (s \<times> i)) \<Rightarrow> s \<Rightarrow> 'a list \<Rightarrow> (s \<times> i list)" where
  "alloc_Xs f s [] = (s,[])"
| "alloc_Xs f s (m_X#m_Xs) = (let (s'', i_X) = f s m_X in
                              let (s',i_Xs) = alloc_Xs f s'' m_Xs in
                              (s',i_X#i_Xs))"

definition alloc_func :: "s \<Rightarrow> module_func \<Rightarrow> inst \<Rightarrow> (s \<times> i)" where
  "alloc_func s m_f inst =
     (case m_f of (i_t, loc_ts, b_es) \<Rightarrow>
        (s\<lparr>s.funcs := (funcs s)@[Func_native inst ((types inst)!i_t) loc_ts b_es]\<rparr>,length (funcs s)))"

abbreviation "alloc_funcs s m_fs i \<equiv> alloc_Xs (\<lambda>s m_f. alloc_func s m_f i) s m_fs"

definition alloc_tab :: "s \<Rightarrow> tab_t \<Rightarrow> (s \<times> i)" where
  "alloc_tab s m_t = (s\<lparr>s.tabs := (tabs s)@[(replicate (l_min m_t) None, (l_max m_t))]\<rparr>,length (tabs s))"

abbreviation "alloc_tabs \<equiv> alloc_Xs alloc_tab"

definition alloc_mem :: "s \<Rightarrow> mem_t \<Rightarrow> (s \<times> i)" where
  "alloc_mem s m_m = (s\<lparr>s.mems := (mems s)@[mem_mk m_m]\<rparr>,length (mems s))"

abbreviation "alloc_mems \<equiv> alloc_Xs alloc_mem"

definition alloc_glob :: "s \<Rightarrow> (module_glob \<times> v) \<Rightarrow> (s \<times> i)" where
  "alloc_glob s m_g_v = 
    (case m_g_v of (m_g, v) \<Rightarrow>
      (s\<lparr>s.globs := (globs s)@[\<lparr>g_mut=(tg_mut (module_glob.g_type m_g)), g_val=v\<rparr>]\<rparr>,length (globs s)))"

abbreviation "alloc_globs s m_gs vs \<equiv> alloc_Xs alloc_glob s (zip m_gs vs)"

lemma alloc_func_length:
  assumes "alloc_func s m_f i = (s', i_f)"
  shows "length (funcs s) = i_f"
        "length (funcs s') = Suc i_f"
        "(tabs s) = (tabs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
  using assms[symmetric]
  unfolding alloc_func_def
  by (simp_all split: prod.splits)

lemma alloc_tab_length:
  assumes "alloc_tab s m_t = (s', i_t)"
  shows "length (tabs s) = i_t"
        "length (tabs s') = Suc i_t"
        "(funcs s) = (funcs s')"
        "(mems s) = (mems s')"
        "(globs s) = (globs s')"
  using assms[symmetric]
  unfolding alloc_tab_def
  by (simp_all split: prod.splits)

lemma alloc_mem_length:
  assumes "alloc_mem s m_m = (s', i_m)"
  shows "length (mems s) = i_m"
        "length (mems s') = Suc i_m"
        "(funcs s) = (funcs s')"
        "(tabs s) = (tabs s')"
        "(globs s) = (globs s')"
  using assms[symmetric]
  unfolding alloc_mem_def
  by (simp_all split: prod.splits)

lemma alloc_glob_length:
  assumes "alloc_glob s (m_g, v) = (s', i_g)"
  shows "length (globs s) = i_g"
        "length (globs s') = Suc i_g"
        "(funcs s) = (funcs s')"
        "(tabs s) = (tabs s')"
        "(mems s) = (mems s')"
  using assms[symmetric]
  unfolding alloc_glob_def
  by (simp_all split: prod.splits)

lemma alloc_funcs_range:
  assumes "alloc_funcs s m_fs i = (s', i_fs)"
  shows "i_fs = [length (funcs s) ..< (length (funcs s) + length m_fs)] \<and>
         (tabs s) = (tabs s') \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s')"
  using assms
proof (induction m_fs arbitrary: s i_fs)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_f m_fs)
  obtain s'' i_f' i_fs' where s''_is:"alloc_func s m_f i = (s'', i_f')"
                                     "alloc_funcs s'' m_fs i = (s', i_fs')"
                                     "i_f' # i_fs' = i_fs"
    using Cons(2)
    by (simp split: prod.splits)
  thus ?case
    using Cons(1)[OF s''_is(2)] using alloc_func_length[OF s''_is(1)] upt_rec
    by (simp split: prod.splits if_splits)    
qed

lemma alloc_tabs_range:
  assumes "alloc_tabs s m_ts = (s', i_ts)"
  shows "i_ts = [length (tabs s) ..< (length (tabs s) + length m_ts)] \<and>
         (funcs s) = (funcs s') \<and>
         (mems s) = (mems s') \<and>
         (globs s) = (globs s')"
  using assms
proof (induction m_ts arbitrary: s i_ts)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_t m_ts)
  obtain s'' i_t' i_ts' where s''_is:"alloc_tab s m_t = (s'', i_t')"
                                     "alloc_tabs s'' m_ts = (s', i_ts')"
                                     "i_t' # i_ts' = i_ts"
    using Cons(2)
    by (simp split: prod.splits)
  thus ?case
    using Cons(1)[OF s''_is(2)] using alloc_tab_length[OF s''_is(1)] upt_rec
    by (simp split: prod.splits if_splits)
qed

lemma alloc_mems_range:
  assumes "alloc_mems s m_ms = (s', i_ms)"
  shows "i_ms = [length (mems s) ..< (length (mems s) + length m_ms)] \<and>
         (funcs s) = (funcs s') \<and>
         (tabs s) = (tabs s') \<and>
         (globs s) = (globs s')"
  using assms
proof (induction m_ms arbitrary: s i_ms)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_m m_ms)
  obtain s'' i_m' i_ms' where s''_is:"alloc_mem s m_m = (s'', i_m')"
                                     "alloc_mems s'' m_ms = (s', i_ms')"
                                     "i_m' # i_ms' = i_ms"
    using Cons(2)
    by (simp split: prod.splits)
  thus ?case
    using Cons(1)[OF s''_is(2)] using alloc_mem_length[OF s''_is(1)] upt_rec
    by (simp split: prod.splits if_splits)    
qed

lemma alloc_globs_range:
  assumes "alloc_globs s m_gs vs = (s', i_gs)"
  shows "i_gs = [length (globs s) ..< (length (globs s) + min (length m_gs) (length vs))] \<and>
         (funcs s) = (funcs s') \<and>
         (tabs s) = (tabs s') \<and>
         (mems s) = (mems s')"
  using assms
proof (induction m_gs arbitrary: s i_gs vs)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_g m_gs)
  note outer_Cons = Cons
  show ?case
  proof (cases vs)
    case Nil
    thus ?thesis
      using Cons
      by simp
  next
    case (Cons v vs')
    then obtain s'' i_g' i_gs' where s''_is:"alloc_glob s (m_g, v) = (s'', i_g')"
                                       "alloc_globs s'' m_gs vs' = (s', i_gs')"
                                       "i_g' # i_gs' = i_gs"
      using outer_Cons(2)
      by (simp split: prod.splits)
    thus ?thesis
      using outer_Cons(1)[OF s''_is(2)] using alloc_glob_length[OF s''_is(1)] upt_rec Cons
      by simp
  qed
qed

lemma length_alloc_Xs:
  assumes "alloc_Xs f s m_Xs = (s', i_Xs)"
  shows "length i_Xs = length m_Xs"
  using assms
proof (induction m_Xs arbitrary: s i_Xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons m_X m_Xs)
  thus ?case
    by (fastforce split: prod.splits)
qed

lemma alloc_Xs_app:
  assumes  "alloc_Xs f s (m_Xs@m_Ys) = (s', i_XYs)"
  shows "\<exists>s'' i_Xs i_Ys. i_XYs = i_Xs@i_Ys \<and>
              alloc_Xs f s m_Xs = (s'', i_Xs) \<and>
              alloc_Xs f s'' m_Ys = (s', i_Ys)"
  using assms
proof (induction f s "(m_Xs@m_Ys)" arbitrary: m_Xs i_XYs rule: alloc_Xs.induct)
  case (1 f s)
  thus ?case
    by simp
next
  case (2 f s m_X' m_XYs')
  consider (a) "m_Xs = []" "m_X' # m_XYs' = m_Ys"
         | (b) m_Xs' where "m_X' # m_Xs' = m_Xs" "m_XYs' = m_Xs' @ m_Ys"
    using Cons_eq_append_conv[of m_X' m_XYs' m_Xs m_Ys]
          2(2)
    by blast
  thus ?case
  proof cases
    case a
    thus ?thesis
      using 2
      by fastforce
  next
    case b
    obtain s'' i_XY i_XYs' where s''_is:
      "m_Xs = m_X' # m_Xs'"
      "f s m_X' = (s'', i_XY)"
      "alloc_Xs f s'' (m_Xs' @ m_Ys) = (s', i_XYs')"
      "i_XY # i_XYs' = i_XYs"
      using 2(3) b(1)[symmetric]
      by (simp split: prod.splits)
    thus ?thesis
      using 2(1)[OF _ _ b(2) s''_is(3), of _ i_XY]
      by (fastforce split: prod.splits)
  qed
qed

lemma alloc_Xs_snoc:
  assumes  "alloc_Xs f s (m_Xs@[m_X]) = (s', i_XYs)"
  shows "\<exists>s'' i_Xs i_X. i_XYs = i_Xs@[i_X] \<and>
              alloc_Xs f s m_Xs = (s'', i_Xs) \<and>
              f s'' m_X = (s', i_X)"
  using alloc_Xs_app[OF assms]
  apply (simp split: prod.splits)
  apply (metis prod.exhaust_sel)
  done

inductive alloc_module :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> v list \<Rightarrow> (s \<times> inst \<times> module_export list) \<Rightarrow> bool" where
  "\<lbrakk>inst = \<lparr>types=(m_types m),
           funcs=(ext_funcs imps)@i_fs,
           tabs=(ext_tabs imps)@i_ts,
           mems=(ext_mems imps)@i_ms,
           globs=(ext_globs imps)@i_gs\<rparr>;
    alloc_funcs s (m_funcs m) inst = (s1,i_fs);
    alloc_tabs s1 (m_tabs m) = (s2,i_ts);
    alloc_mems s2 (m_mems m) = (s3,i_ms);
    alloc_globs s3 (m_globs m) gvs = (s',i_gs);
    exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)
     \<rbrakk> \<Longrightarrow> alloc_module s m imps gvs (s',inst,exps)"

definition interp_alloc_module :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> v list \<Rightarrow> (s \<times> inst \<times> module_export list)" where
  "interp_alloc_module s m imps gvs =
   (let i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))] in
    let i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))] in
    let i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))] in
    let i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))] in
    let inst = \<lparr>types=(m_types m),
                funcs=(ext_funcs imps)@i_fs,
                tabs=(ext_tabs imps)@i_ts,
                mems=(ext_mems imps)@i_ms,
                globs=(ext_globs imps)@i_gs\<rparr> in
    let (s1,_) = alloc_funcs s (m_funcs m) inst in
    let (s2,_) = alloc_tabs s1 (m_tabs m) in
    let (s3,_) = alloc_mems s2 (m_mems m) in
    let (s',_) = alloc_globs s3 (m_globs m) gvs in
    let exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m) in
    (s', inst, exps))"

lemma alloc_module_imp_interp_alloc_module:
  assumes "alloc_module s m imps gvs (s',inst,exps)"
  shows "(interp_alloc_module s m imps gvs = (s',inst,exps))"
proof -
  obtain s1 s2 s3 i_fs i_ts i_ms i_gs where s'_is:
    "inst = \<lparr>types=(m_types m),
             funcs=(ext_funcs imps)@i_fs,
             tabs=(ext_tabs imps)@i_ts,
             mems=(ext_mems imps)@i_ms,
             globs=(ext_globs imps)@i_gs\<rparr>"
    "alloc_funcs s (m_funcs m) inst = (s1,i_fs)"
    "alloc_tabs s1 (m_tabs m) = (s2,i_ts)"
    "alloc_mems s2 (m_mems m) = (s3,i_ms)"
    "alloc_globs s3 (m_globs m) gvs = (s',i_gs)"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms
    unfolding alloc_module.simps
    by blast
  have "i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
       "i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))]"
       "i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))]"
       "i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))]"
    using alloc_funcs_range[OF s'_is(2)] alloc_tabs_range[OF s'_is(3)]
          alloc_mems_range[OF s'_is(4)] alloc_globs_range[OF s'_is(5)]
    by auto
  thus ?thesis
    using s'_is
    unfolding interp_alloc_module_def
    by (simp add: Let_def split: prod.splits)
qed

lemma interp_alloc_module_imp_alloc_module:
  assumes "(interp_alloc_module s m imps gvs = (s',inst,exps))"
  shows "alloc_module s m imps gvs (s',inst,exps)"
proof -
  obtain i_fs i_ts i_ms i_gs i_fs' i_ts' i_ms' i_gs' s1 s2 s3 where s'_is:
    "i_fs = [length (funcs s) ..< (length (funcs s) + length (m_funcs m))]"
    "i_ts = [length (tabs s) ..< (length (tabs s) + length (m_tabs m))]"
    "i_ms = [length (mems s) ..< (length (mems s) + length (m_mems m))]"
    "i_gs = [length (globs s) ..< (length (globs s) + min (length (m_globs m)) (length gvs))]"
    "inst = \<lparr>types=(m_types m),
                funcs=(ext_funcs imps)@i_fs,
                tabs=(ext_tabs imps)@i_ts,
                mems=(ext_mems imps)@i_ms,
                globs=(ext_globs imps)@i_gs\<rparr>"
    "(s1,i_fs') = alloc_funcs s (m_funcs m) inst"
    "(s2,i_ts') = alloc_tabs s1 (m_tabs m)"
    "(s3,i_ms') = alloc_mems s2 (m_mems m)"
    "(s',i_gs') = alloc_globs s3 (m_globs m) gvs"
    "exps = map (\<lambda>m_exp. \<lparr>E_name=(E_name m_exp), E_desc=(export_get_v_ext inst (E_desc m_exp))\<rparr>) (m_exports m)"
    using assms
    unfolding interp_alloc_module_def
    by (auto simp add: Let_def split: prod.splits)
  have "i_fs = i_fs'"
       "i_ts = i_ts'"
       "i_ms = i_ms'"
       "i_gs = i_gs'"
    using s'_is(1,2,3,4)
          alloc_funcs_range[OF s'_is(6)[symmetric]]
          alloc_tabs_range[OF s'_is(7)[symmetric]]
          alloc_mems_range[OF s'_is(8)[symmetric]]
          alloc_globs_range[OF s'_is(9)[symmetric]]
    by metis+
  thus ?thesis
    using alloc_module.intros[OF s'_is(5) _ _ _ _ s'_is(10)]
    by (metis (no_types, lifting) s'_is(6,7,8,9))
qed

lemma alloc_module_equiv_interp_alloc_module:
  "alloc_module s m imps gvs (s',inst,exps) = (interp_alloc_module s m imps gvs = (s',inst,exps))"
  using alloc_module_imp_interp_alloc_module interp_alloc_module_imp_alloc_module
  by blast

definition init_tab :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> module_elem \<Rightarrow> s" where
  "init_tab s inst e_ind e = (let t_ind = ((inst.tabs inst)!(e_tab e)) in
                               let (tab_e,max) = (tabs s)!t_ind in
                               let e_pay = map (\<lambda>i. Some ((inst.funcs inst)!i)) (e_init e) in
                               let tab'_e = ((take e_ind tab_e) @ e_pay @ (drop (e_ind + length e_pay) tab_e)) in
                               s\<lparr>tabs := (tabs s)[e_ind := (tab'_e,max)]\<rparr>)"

definition init_tabs :: "s \<Rightarrow> inst \<Rightarrow> nat list \<Rightarrow> module_elem list \<Rightarrow> s" where
  "init_tabs s inst e_inds es = foldl (\<lambda>s' (e_ind,e). init_tab s' inst e_ind e) s (zip e_inds es)"

definition init_mem :: "s \<Rightarrow> inst \<Rightarrow> nat \<Rightarrow> module_data \<Rightarrow> s" where
  "init_mem s inst d_ind d = (let m_ind = ((inst.mems inst)!(d_data d)) in
                               let mem = (mems s)!m_ind in
                               let mem' = write_bytes mem d_ind (d_init d) in
                               s\<lparr>mems := (mems s)[m_ind := mem']\<rparr>)"

definition init_mems :: "s \<Rightarrow> inst \<Rightarrow> nat list \<Rightarrow> module_data list \<Rightarrow> s" where
  "init_mems s inst d_inds ds = foldl (\<lambda>s' (d_ind,d). init_mem s' inst d_ind d) s (zip d_inds ds)"

inductive instantiate :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> ((s \<times> inst \<times> (module_export list)) \<times> (nat option)) \<Rightarrow> bool" where
  "\<lbrakk>module_typing m t_imps t_exps;
    list_all2 (external_typing s) v_imps t_imps;
    alloc_module s m v_imps g_inits (s', inst, v_exps);
    list_all2 (\<lambda>g v. reduce_trans inst (s',[],$*(g_init g)) (s',[],[$C v])) (m_globs m) g_inits;
    list_all2 (\<lambda>e c. reduce_trans inst (s',[],$*(e_off e)) (s',[],[$C ConstInt32 c])) (m_elem m) e_offs;
    list_all2 (\<lambda>d c. reduce_trans inst (s',[],$*(d_off d)) (s',[],[$C ConstInt32 c])) (m_data m) d_offs;
    list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m);
    list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s)!((inst.mems inst)!(d_data d)))) d_offs (m_data m);
    map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m) = start;
    init_tabs s' inst (map nat_of_int e_offs) (m_elem m) = s'';
    init_mems s' inst (map nat_of_int d_offs) (m_data m) = s_end
    \<rbrakk> \<Longrightarrow> instantiate s m v_imps ((s_end, inst, v_exps), start)"

definition interp_get_v :: "s \<Rightarrow> inst \<Rightarrow> b_e list \<Rightarrow> v" where
  "interp_get_v s inst b_es = 
     (case run_v 2 0 inst (s,[],$*b_es) of
        (_,RValue [v]) \<Rightarrow> v)"

definition interp_get_i32 :: "s \<Rightarrow> inst \<Rightarrow> b_e list \<Rightarrow> i32" where
  "interp_get_i32 s inst b_es = 
     (case interp_get_v s inst b_es of
        ConstInt32 c \<Rightarrow> c)"

fun interp_instantiate :: "s \<Rightarrow> m \<Rightarrow> v_ext list \<Rightarrow> ((s \<times> inst \<times> (module_export list)) \<times> (nat option)) option" where
  "interp_instantiate s m v_imps =
     (case (module_type_checker m) of
        Some (t_imps, t_exps) \<Rightarrow>
          if (list_all2 (external_typing s) v_imps t_imps) then
            let g_inits = 
              map (\<lambda>g. interp_get_v s \<lparr>types=[],funcs=[],tabs=[],mems=[],globs=ext_globs v_imps\<rparr> (g_init g)) (m_globs m) in
            let (s', inst, v_exps) = interp_alloc_module s m v_imps g_inits in
            let e_offs = map (\<lambda>e. interp_get_i32 s' inst (e_off e)) (m_elem m) in
            let d_offs = map (\<lambda>d. interp_get_i32 s' inst (d_off d)) (m_data m) in
            if (list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m) \<and>
                list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s)!((inst.mems inst)!(d_data d)))) d_offs (m_data m)) then
              let start = map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m) in
              let s'' = init_tabs s' inst (map nat_of_int e_offs) (m_elem m) in
              let s_end = init_mems s' inst (map nat_of_int d_offs) (m_data m) in
              Some ((s_end, inst, v_exps), start)
            else None
          else None
      | _ \<Rightarrow> None)"

lemma const_expr_is:
  assumes "const_expr \<C> b_e"
          "\<C> \<turnstile> [b_e] : (ts _> ts')"
        shows "\<exists>t. (\<C> \<turnstile> [b_e] : ([] _> [t])) \<and> ts' = ts@[t] \<and> 
         ((\<exists>v. b_e = (C v) \<and> typeof v = t) \<or>
         (\<exists>j. b_e = (Get_global j) \<and> j < length (global \<C>) \<and>
              tg_mut ((global \<C>)!j) = T_immut \<and>
              tg_t ((global \<C>)!j) = t))"
  using assms(2,1)
proof (induction "\<C>" "[b_e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct)
  case (const \<C> v)
  thus ?case
    using b_e_typing.const
    by blast
next
  case (get_global i \<C> t)
  thus ?case
    using b_e_typing.get_global const_expr.cases
    by fastforce
next
  case (weakening \<C> t1s t2s ts)
  thus ?case
    by simp
qed (auto simp add: const_expr.simps)

lemma const_exprs_empty:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [])"
  shows "b_es = []"
  using assms(2,1)
proof (induction "([] _> [])" rule: b_e_typing.induct)
  case (composition \<C> es t2s e)
  thus ?case
    by (metis (no_types, lifting) Nil_is_append_conv const_expr_is list.pred_inject(2) list_all_append)
next
  case (weakening \<C> es t1s t2s ts)
  thus ?case
    by blast
qed (auto simp add: const_expr.simps)

lemma const_exprs_is:
  assumes "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
  shows "(\<exists>v. b_es = [C v] \<and> typeof v = t) \<or>
         (\<exists>j. b_es = [Get_global j] \<and> j < length (global \<C>) \<and>
              tg_mut ((global \<C>)!j) = T_immut \<and>
              tg_t ((global \<C>)!j) = t)"
  using assms(2,1)
proof (induction "\<C>" "b_es" "([] _> [t])" rule: b_e_typing.induct)
  case (composition \<C> es t2s e)
  have 1:"const_exprs \<C> es" "const_expr \<C> e"
    using composition(5)
    by simp_all
  have "t2s = []" "es = []"
    using const_expr_is[OF 1(2) composition(3)]  composition(1) const_exprs_empty 1(1)
    by auto
  thus ?case
    using composition
    by simp
qed (auto simp add: const_expr.simps)

lemma const_exprs_run_v:
  assumes "\<C> = \<lparr>types_t=[], func_t=[], global=tgs, table=[], memory=[], local=[], label=[], return=None\<rparr>"
          "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
          "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs tgs"
          "inst = \<lparr>types=arb1,funcs=arb2,tabs=arb3,mems=arb4,globs=igs@arb5\<rparr>"
  shows "run_v 2 0 inst (s,[],$*b_es) = (s, RValue [v]) \<and> typeof v = t"
  sorry

lemma const_exprs_reduce_trans:
  assumes "\<C> = \<lparr>types_t=[], func_t=[], global=tgs, table=[], memory=[], local=[], label=[], return=None\<rparr>"
          "const_exprs \<C> b_es"
          "\<C> \<turnstile> b_es : ([] _> [t])"
          "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs tgs"
          "inst = \<lparr>types=arb1,funcs=arb2,tabs=arb3,mems=arb4,globs=igs@arb5\<rparr>"
          "reduce_trans inst (s,vs,$*b_es) (s',vs',[$C v])"
  shows "s = s' \<and> vs = vs' \<and> typeof v = t \<and> run_v 2 0 inst (s,[],$*b_es) = (s, RValue [v])"
  sorry

lemma const_exprs_inst:
  assumes "\<C> = \<lparr>types_t=[], func_t=[], global=tgs, table=[], memory=[], local=[], label=[], return=None\<rparr>"
          "const_expr \<C> b_e"
          "list_all2 (\<lambda>ig tg. external_typing s (Ext_glob ig) (Te_glob tg)) igs tgs"
          "inst = \<lparr>types=[],funcs=[],tabs=[],mems=[],globs=igs\<rparr>"
          "inst' = \<lparr>types=arb1,funcs=arb2,tabs=arb3,mems=arb4,globs=igs@arb5\<rparr>"
  shows "\<lparr>s;vs;[$b_e]\<rparr> \<leadsto>_inst \<lparr>s;vs;[$C v]\<rparr> = \<lparr>s;vs;[$b_e]\<rparr> \<leadsto>_inst' \<lparr>s;vs;[$C v]\<rparr>"
  sorry

lemma interp_instantiate_imp_instantiate:
  assumes "(interp_instantiate s m v_imps = Some ((s_end, inst, v_exps), start))"
  shows "(instantiate s m v_imps ((s_end, inst, v_exps), start))"
proof -
  obtain t_imps t_exps g_inits s' e_offs d_offs s'' where m_is:
    "module_type_checker m = Some (t_imps, t_exps)"
    "(list_all2 (external_typing s) v_imps t_imps)"
    "g_inits = map (\<lambda>g. interp_get_v s \<lparr>types=[],funcs=[],tabs=[],mems=[],globs=ext_globs v_imps\<rparr> (g_init g)) (m_globs m)"
    "(s', inst, v_exps) = interp_alloc_module s m v_imps g_inits"
    "e_offs = map (\<lambda>e. interp_get_i32 s' inst (e_off e)) (m_elem m)"
    "d_offs = map (\<lambda>d. interp_get_i32 s' inst (d_off d)) (m_data m)"
    "list_all2 (\<lambda>e_off e. ((nat_of_int e_off) + (length (e_init e))) \<le> length (fst ((tabs s)!((inst.tabs inst)!(e_tab e))))) e_offs (m_elem m)"
    "list_all2 (\<lambda>d_off d. ((nat_of_int d_off) + (length (d_init d))) \<le> mem_length ((mems s)!((inst.mems inst)!(d_data d)))) d_offs (m_data m)"
    "start = map_option (\<lambda>i_s. ((inst.funcs inst)!i_s)) (m_start m)"
    "s'' = init_tabs s' inst (map nat_of_int e_offs) (m_elem m)"
    "s_end = init_mems s' inst (map nat_of_int d_offs) (m_data m)"
    using assms
    by (fastforce simp add: Let_def split: if_splits option.splits prod.splits)

  have 1:"module_typing m t_imps t_exps"
    using m_is(1) module_type_checker_imp_module_typing
    by blast
  have 2:"alloc_module s m v_imps g_inits (s', inst, v_exps)"
    using m_is(4) interp_alloc_module_imp_alloc_module
    by metis
  have 3:"list_all2 (\<lambda>g v. reduce_trans inst (s',[],$*(g_init g)) (s',[],[$C v])) (m_globs m) g_inits"
         "list_all2 (\<lambda>e c. reduce_trans inst (s',[],$*(e_off e)) (s',[],[$C ConstInt32 c])) (m_elem m) e_offs"
         "list_all2 (\<lambda>d c. reduce_trans inst (s',[],$*(d_off d)) (s',[],[$C ConstInt32 c])) (m_data m) d_offs"
    sorry
  show ?thesis
    using instantiate.intros[OF 1 m_is(2) 2 3 m_is(7,8) m_is(9,10,11)[symmetric]]
    by blast
qed
end
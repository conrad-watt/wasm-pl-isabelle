section {* Auxiliary Type System Properties *}

theory Wasm_Properties_Aux imports Wasm_Axioms begin

lemma typeof_i32:
  assumes "typeof v = T_i32"
  shows "\<exists>c. v = ConstInt32 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma typeof_i64:
  assumes "typeof v = T_i64"
  shows "\<exists>c. v = ConstInt64 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma typeof_f32:
  assumes "typeof v = T_f32"
  shows "\<exists>c. v = ConstFloat32 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma typeof_f64:
  assumes "typeof v = T_f64"
  shows "\<exists>c. v = ConstFloat64 c"
  using assms
  unfolding typeof_def
  by (cases v) auto

lemma typeof_app_unop:
  assumes "typeof v = t"
  shows "typeof (app_unop op v) = t"
  using assms
  unfolding typeof_def app_unop_def app_unop_i_v_def app_unop_f_v_def
  by (simp split: unop.splits unop_i.splits unop_f.splits v.splits)

lemma typeof_app_testop:
  shows "typeof (app_testop op v) = T_i32"
  unfolding typeof_def app_testop_def
  by (auto split: v.splits)

lemma typeof_app_binop:
  assumes "typeof v1 = t"
          "typeof v2 = t"
          "(app_binop op v1 v2) = Some v"
  shows "typeof v = t"
  using assms
  unfolding typeof_def app_binop_def app_binop_i_v_def app_binop_f_v_def
  by (auto split: binop.splits binop_i.splits binop_f.splits v.splits)

lemma typeof_app_relop:
  shows "typeof (app_relop op v1 v2) = T_i32"
  unfolding typeof_def app_relop_def app_relop_i_v_def app_relop_f_v_def
  by (auto split: relop.splits relop_i.splits relop_f.splits v.splits)


lemma exists_v_typeof: "\<exists>v v. typeof v = t"
proof (cases t)
  case T_i32
  fix v
  have "typeof (ConstInt32 v) = t"
    using T_i32
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_i32
    by fastforce
next
  case T_i64
  fix v
  have "typeof (ConstInt64 v) = t"
    using T_i64
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_i64
    by fastforce
next
  case T_f32
  fix v
  have "typeof (ConstFloat32 v) = t"
    using T_f32
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_f32
    by fastforce
next
  case T_f64
  fix v
  have "typeof (ConstFloat64 v) = t"
    using T_f64
    unfolding typeof_def
    by simp
  thus ?thesis
    using T_f64
    by fastforce
qed

lemma set_local_access: 
  assumes "j < Suc (length vi + length vs)"
          "j \<noteq> length vi"
  shows "(vi @ [v] @ vs) ! j = (vi @ [v'] @ vs) ! j"
proof -
  consider (1) "j < length vi" | (2) "j \<ge> length (vi @ [v])" "j \<ge> length (vi @ [v'])"
    using assms(2)
    by fastforce
  thus ?thesis
    using assms(1)
    apply (cases)
    apply (simp add: nth_append)
    apply (simp add: nth_append)
    done
qed

lemma lfilled_collapse1:
  assumes "Lfilled n lholed (vs@es) LI"
          "const_list vs"
          "length vs \<ge> l"
  shows "\<exists>lholed'. Lfilled n lholed' ((drop (length vs - l) vs)@es) LI"
  using assms(1)
proof (induction "vs@es" LI rule: Lfilled.induct)
  case (L0 vs' lholed es')
  obtain vs1 vs2 where "vs = vs1@vs2" "length vs2 = l"
    using assms(3)
    by (metis append_take_drop_id diff_diff_cancel length_drop)
  moreover
  hence "const_list (vs'@vs1)"
    using L0(1) assms(2)
    unfolding const_list_def
    by simp
  ultimately
  show ?case
    using Lfilled.intros(1)[of "vs'@vs1" _ es' "vs2@es"]
      by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma lfilled_collapse2:
  assumes "Lfilled n lholed (es@es') LI"
  shows "\<exists>lholed' vs'. Lfilled n lholed' es LI"
  using assms
proof (induction "es@es'" LI rule: Lfilled.induct)
  case (L0 vs lholed es')
  thus ?case
    using Lfilled.intros(1)
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma lfilled_collapse3:
  assumes "Lfilled k lholed [Label n les es] LI"
  shows "\<exists>lholed'. Lfilled (Suc k) lholed' es LI"
  using assms
proof (induction "[Label n les es]" LI rule: Lfilled.induct)
  case (L0 vs lholed es')
  have "Lfilled 0 (LBase [] []) es es"
    using Lfilled.intros(1)
    unfolding const_list_def
    by (metis append.left_neutral append_Nil2 list_all_simps(2))
  thus ?case
    using Lfilled.intros(2) L0
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed


lemma unlift_b_e: assumes "\<S>\<bullet>\<C> \<turnstile> $*b_es : tf" shows "\<C> \<turnstile> b_es : tf"
using assms proof (induction "\<S>" "\<C>" "($*b_es)" "tf" arbitrary: b_es)
  case (1 \<C> b_es tf \<S>)
  then show ?case
    using inj_basic map_injective
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  obtain es' e' where "es' @ [e'] = b_es"
    using 2(5)
    by (simp add: snoc_eq_iff_butlast)
  then show ?case using 2
    using b_e_typing.composition
    by fastforce
next                            
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    using b_e_typing.weakening
    by blast
qed auto

lemma stab_typed_some_imp_member:
  assumes "stab s i c = Some cl"
          "inst_typing s i \<C>"
        shows "Some cl \<in> set (concat (s.tab s))"
proof -
  show ?thesis
  proof (cases "inst.tab i")
    case None
    thus ?thesis
      using assms stab_def
      by auto
  next
    case (Some a)
    hence "a < length (tab s)"
      using assms(2) inst_typing.simps
      unfolding tabi_agree_def
      by (auto split: option.splits)
    thus ?thesis
      using assms(1) Some
      unfolding stab_def stab_s_def
      apply simp
      apply (metis (full_types) nth_mem option.distinct(1))
      done
  qed
qed

lemma stab_typed_some_imp_cl_typed:
  assumes "stab s i c = Some cl"
          "inst_typing s i \<C>"
          "store_typing s"
  shows "\<exists>tf. cl_typing s cl tf"
proof -
  have "Some cl \<in> set (concat (s.tab s))"
    using assms stab_typed_some_imp_member
    by auto
  moreover
  have "list_all (list_all (tab_agree s)) (tab s)"
    using assms(3)
    unfolding store_typing.simps
    by simp
  ultimately
  have "tab_agree s (Some cl)"
    by (simp, meson Ball_set_list_all)
  thus ?thesis
    unfolding tab_agree_def
    by fastforce
qed

lemma b_e_type_empty1[dest]: assumes "\<C> \<turnstile> [] : (ts _> ts')" shows "ts = ts'"
  using assms
  by (induction "[]::(b_e list)" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, simp_all)

lemma b_e_type_empty: "(\<C> \<turnstile> [] : (ts _> ts')) = (ts = ts')"
proof (safe)
  assume "\<C> \<turnstile> [] : (ts _> ts')"
  thus "ts = ts'"
    by blast
next
  assume "ts = ts'"
  thus "\<C> \<turnstile> [] : (ts' _> ts')"
    using b_e_typing.empty b_e_typing.weakening
    by fastforce
qed

lemma b_e_type_value:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = C v"
  shows "ts' = ts @ [typeof v]"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_load:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Load t tp_sx a off"
  shows "\<exists>ts'' sec n. ts = ts''@[T_i32] \<and> ts' = ts''@[t] \<and> (memory \<C>) = True"
        "load_store_t_bounds a (option_projl tp_sx) t"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_store:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Store t tp a off"
    shows "ts = ts'@[T_i32, t]"
          "\<exists>sec n. (memory \<C>) = True"
          "load_store_t_bounds a tp t"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_current_memory:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Current_memory"
  shows "\<exists>sec n. ts' = ts @ [T_i32] \<and> (memory \<C>) = True"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_grow_memory:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Grow_memory"
  shows "\<exists>ts''. ts = ts''@[T_i32] \<and> ts = ts' \<and> (\<exists>n. (memory \<C>) = True)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct) auto

lemma b_e_type_nop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Nop"
  shows "ts = ts'"
  using assms
  by (induction "[e]"  "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

definition arity_2_result :: "b_e \<Rightarrow> t" where
  "arity_2_result op2 = (case op2 of
                           Binop t _ \<Rightarrow> t
                         | Relop t _ \<Rightarrow> T_i32)"

lemma b_e_type_binop_relop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Binop t bop \<or> e = Relop t rop"
  shows "\<exists>ts''. ts = ts''@[t,t] \<and> ts' = ts''@[arity_2_result(e)]"
        "e =  Binop t bop \<Longrightarrow> binop_t_agree bop t"
        "e = Relop t rop \<Longrightarrow> relop_t_agree rop t"
  using assms
  unfolding arity_2_result_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_testop_drop_cvt0:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Testop t testop \<or> e = Drop \<or> e = Cvtop t1 cvtop t2 sx"
  shows "ts \<noteq> []"
  using assms
  by (induction "[e]" "ts _> ts'" arbitrary: ts' rule: b_e_typing.induct, auto)

definition arity_1_result :: "b_e \<Rightarrow> t" where
  "arity_1_result op1 = (case op1 of
                           Unop t _ \<Rightarrow> t
                         | Testop t _ \<Rightarrow> T_i32
                         | Cvtop t1 _ _ _ \<Rightarrow> t1)"

lemma b_e_type_unop_testop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Unop t uop \<or> e = Testop t top'"
  shows "\<exists>ts''. ts = ts''@[t] \<and> ts' = ts''@[arity_1_result e]"
        "e = Unop t uop \<Longrightarrow> unop_t_agree uop t"
        "e = Testop t top' \<Longrightarrow> is_int_t t"
  using assms
  unfolding arity_1_result_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_cvtop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Cvtop t1 cvtop t sx"
  shows "\<exists>ts''. ts = ts''@[t] \<and> ts' = ts''@[arity_1_result e]"
        "cvtop = Convert \<Longrightarrow> (t1 \<noteq> t) \<and> (sx = None) = ((is_float_t t1 \<and> is_float_t t) \<or> (is_int_t t1 \<and> is_int_t t \<and> (t_length t1 < t_length t)))"
        "cvtop = Reinterpret \<Longrightarrow> (t1 \<noteq> t) \<and> t_length t1 = t_length t"
  using assms
  unfolding arity_1_result_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_drop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Drop"
  shows "\<exists>t. ts = ts'@[t]"
  using assms b_e_type_testop_drop_cvt0
by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_select:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Select"
  shows "\<exists>ts'' t. ts = ts''@[t,t,T_i32] \<and> ts' = ts''@[t]"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_call:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Call i"
  shows  "i < length (func_t \<C>)"
         "\<exists>ts'' tf1 tf2. ts = ts''@tf1 \<and> ts' = ts''@tf2 \<and> (func_t \<C>)!i = (tf1 _> tf2)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_call_indirect:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Call_indirect i"
  shows "i < length (types_t \<C>)"
        "\<exists>ts'' tf1 tf2. ts = ts''@tf1@[T_i32] \<and> ts' = ts''@tf2 \<and> (types_t \<C>)!i = (tf1 _> tf2)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_get_local:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Get_local i"
  shows "\<exists>t. ts' = ts@[t] \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_set_local:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Set_local i"
  shows "\<exists>t. ts = ts'@[t] \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_tee_local:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Tee_local i"
  shows "\<exists>ts'' t. ts = ts''@[t] \<and> ts' = ts''@[t] \<and> (local \<C>)!i = t" "i < length(local \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_get_global:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Get_global i"
  shows "\<exists>t. ts' = ts@[t] \<and> tg_t((global \<C>)!i) = t" "i < length(global \<C>)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_set_global:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Set_global i"
  shows "\<exists>t. ts = ts'@[t] \<and> (global \<C>)!i = \<lparr>tg_mut = T_mut, tg_t = t\<rparr> \<and> i < length(global \<C>)"
  using assms is_mut_def
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct) auto

lemma b_e_type_block:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Block tf es"
  shows "\<exists>ts'' tfn tfm. tf = (tfn _> tfm) \<and> (ts = ts''@tfn) \<and> (ts' = ts''@tfm) \<and>
                        (\<C>\<lparr>label :=  [tfm] @ label \<C>\<rparr> \<turnstile> es : tf)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_loop:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Loop tf es"
  shows "\<exists>ts'' tfn tfm. tf = (tfn _> tfm) \<and> (ts = ts''@tfn) \<and> (ts' = ts''@tfm) \<and>
                        (\<C>\<lparr>label :=  [tfn] @ label \<C>\<rparr> \<turnstile> es : tf)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_if:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = If tf es1 es2"
  shows "\<exists>ts'' tfn tfm. tf = (tfn _> tfm) \<and> (ts = ts''@tfn @ [T_i32]) \<and> (ts' = ts''@tfm) \<and>
                        (\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es1 : tf) \<and>
                        (\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es2 : tf)"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_br:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br i"
        shows "i < length(label \<C>)"
              "\<exists>ts_c ts''. ts = ts_c @ ts'' \<and> (label \<C>)!i = ts''"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_br_if:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br_if i"
        shows "i < length(label \<C>)"
              "\<exists>ts_c ts''. ts = ts_c @ ts'' @ [T_i32] \<and> ts' = ts_c @ ts'' \<and> (label \<C>)!i = ts''"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_br_table:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Br_table is i"
  shows "\<exists>ts_c ts''. list_all (\<lambda>i. i < length(label \<C>) \<and> (label \<C>)!i = ts'') (is@[i]) \<and> ts = ts_c @ ts''@[T_i32]"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, fastforce+)

lemma b_e_type_return:
  assumes "\<C> \<turnstile> [e] : (ts _> ts')"
          "e = Return"
        shows "\<exists>ts_c ts''. ts = ts_c @ ts'' \<and> (return \<C>) = Some ts''"
  using assms
  by (induction "[e]" "(ts _> ts')" arbitrary: ts ts' rule: b_e_typing.induct, auto)

lemma b_e_type_comp:
  assumes "\<C> \<turnstile> es@[e] : (t1s _> t4s)"
  shows "\<exists>ts'. (\<C> \<turnstile> es : (t1s _> ts')) \<and> (\<C> \<turnstile> [e] : (ts' _> t4s))"
proof (cases es rule: List.rev_cases)
  case Nil
  then show ?thesis
    using assms b_e_typing.empty b_e_typing.weakening
    by fastforce
next
  case (snoc es' e')
  show ?thesis using assms snoc b_e_typing.weakening
    by (induction "es@[e]" "(t1s _> t4s)" arbitrary: t1s t4s, fastforce+)
qed

(* Two special cases - useful for inductions over reduce. *)
lemma b_e_type_comp2_unlift:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$e1, $e2] : (t1s _> t2s)"
  shows "\<exists>ts'. (\<C> \<turnstile> [e1] : (t1s _> ts')) \<and> (\<C> \<turnstile> [e2] : (ts' _> t2s))"
  using assms
        unlift_b_e[of \<S> \<C> "([e1, e2])" "(t1s _> t2s)"]
        b_e_type_comp[of \<C> "[e1]" e2 t1s t2s]
  by simp

lemma b_e_type_comp2_relift:
  assumes "\<C> \<turnstile> [e1] : (t1s _> ts')" "\<C> \<turnstile> [e2] : (ts' _> t2s)"
  shows "\<S>\<bullet>\<C> \<turnstile> [$e1, $e2] : (ts@t1s _> ts@t2s)"
  using assms
        b_e_typing.composition[OF assms]
        e_typing_s_typing.intros(1)[of \<C> "[e1, e2]" "(t1s _> t2s)"]
        e_typing_s_typing.intros(3)[of \<S> \<C> "([$e1,$e2])" t1s t2s ts]
  by simp

lemma b_e_type_value2:
  assumes "\<C> \<turnstile> [C v1, C v2] : (t1s _> t2s)"
  shows "t2s = t1s @ [typeof v1, typeof v2]"
proof -
  obtain ts' where ts'_def:"\<C> \<turnstile> [C v1] : (t1s _> ts')"
                           "\<C> \<turnstile> [C v2] : (ts' _> t2s)"
    using b_e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last_ConsL last_ConsR list.distinct(1))
  have "ts' = t1s @ [typeof v1]"
    using b_e_type_value ts'_def(1)
    by fastforce
  thus ?thesis
    using b_e_type_value ts'_def(2)
    by fastforce
qed

(* Lifting the previous results to all expressions. *)
lemma e_type_comp:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@[e] : (t1s _> t3s)"
  shows "\<exists>ts'. (\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts')) \<and> (\<S>\<bullet>\<C> \<turnstile> [e] : (ts' _> t3s))"
proof (cases es rule: List.rev_cases)
  case Nil
  thus ?thesis
    using assms e_typing_s_typing.intros(1)
    by (metis append_Nil b_e_type_empty list.simps(8))
next
  case (snoc es' e')
  show ?thesis using assms snoc
  proof (induction "es@[e]" "(t1s _> t3s)" arbitrary: t1s t3s)
    case (1 \<C> b_es \<S>)
    obtain es'' e'' where b_e_defs:"($* (es'' @ [e''])) = ($* b_es)"
      using 1(1,2)
      by (metis Nil_is_map_conv append_is_Nil_conv not_Cons_self2 rev_exhaust)
    hence "($*es'') = es" "($e'') = e"
      using 1(2) inj_basic map_injective
      by auto
    moreover
    have "\<C> \<turnstile> (es'' @ [e'']) : (t1s _> t3s)" using 1(1)
      using inj_basic map_injective b_e_defs
      by blast
    then obtain t2s where "\<C> \<turnstile> es'' : (t1s _> t2s)" "\<C> \<turnstile> [e''] : (t2s _> t3s)"
      using b_e_type_comp
      by blast
    ultimately
    show ?case
      using e_typing_s_typing.intros(1)
      by fastforce
  next
    case (3 \<S> \<C> t1s t2s ts)
    thus ?case
      using e_typing_s_typing.intros(3)
      by fastforce
  qed auto
qed

lemma e_type_comp_conc:
  assumes "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> t2s)"
          "\<S>\<bullet>\<C> \<turnstile> es' : (t2s _> t3s)"
  shows "\<S>\<bullet>\<C> \<turnstile> es@es' : (t1s _> t3s)"
  using assms(2)
proof (induction es' arbitrary: t3s rule: List.rev_induct)
  case Nil
  hence "t2s = t3s"
    using unlift_b_e[of _ _ "[]"] b_e_type_empty[of _ t2s t3s]
    by fastforce
  then show ?case
    using Nil assms(1) e_typing_s_typing.intros(2)
    by fastforce
next
  case (snoc x xs)
  then obtain ts' where "\<S>\<bullet>\<C> \<turnstile> xs : (t2s _> ts')" "\<S>\<bullet>\<C> \<turnstile> [x] : (ts' _> t3s)"
    using e_type_comp[of _ _ xs x]
    by fastforce
  then show ?case
    using snoc(1)[of ts'] e_typing_s_typing.intros(2)[of _ _ "es @ xs" t1s ts' x t3s]
    by simp
qed

(* This isn't needed here, but we unlift for convenience. *)
lemma b_e_type_comp_conc:
  assumes "\<C> \<turnstile> es : (t1s _> t2s)"
          "\<C> \<turnstile> es' : (t2s _> t3s)"
  shows "\<C> \<turnstile> es@es' : (t1s _> t3s)"
proof -
  fix \<S>
  have 1:"\<S>\<bullet>\<C> \<turnstile> $*es : (t1s _> t2s)"
    using e_typing_s_typing.intros(1)[OF assms(1)]
    by fastforce
  have 2:"\<S>\<bullet>\<C> \<turnstile> $*es' : (t2s _> t3s)"
    using e_typing_s_typing.intros(1)[OF assms(2)]
    by fastforce
  show ?thesis
    using e_type_comp_conc[OF 1 2]
    by (simp add:  unlift_b_e)
qed

lemma e_type_comp_conc1:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@es' : (ts _> ts')"
  shows "\<exists>ts''. (\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts'')) \<and> (\<S>\<bullet>\<C> \<turnstile> es' : (ts'' _> ts'))"
  using assms
proof (induction es' arbitrary: ts ts' rule: List.rev_induct)
  case Nil
  thus ?case
    using b_e_type_empty[of _ ts' ts'] e_typing_s_typing.intros(1)
    by fastforce
next
  case (snoc x xs)
  then show ?case
    using e_type_comp[of \<S> \<C> "es @ xs" x ts ts'] e_typing_s_typing.intros(2)[of \<S> \<C> xs _ _ x ts']
    by fastforce
qed

lemma e_type_comp_conc2:
  assumes "\<S>\<bullet>\<C> \<turnstile> es@es'@es'' : (t1s _> t2s)"
  shows "\<exists>ts' ts''. (\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts'))
                     \<and> (\<S>\<bullet>\<C> \<turnstile> es' : (ts' _> ts''))
                     \<and> (\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s))"
proof -
  obtain ts' where "\<S>\<bullet>\<C> \<turnstile> es : (t1s _> ts')" "\<S>\<bullet>\<C> \<turnstile> es'@es'' : (ts' _> t2s)"
    using assms(1) e_type_comp_conc1
    by fastforce
  moreover
  then obtain ts'' where "\<S>\<bullet>\<C> \<turnstile> es' : (ts' _> ts'')" "\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s)"
    using e_type_comp_conc1
    by fastforce
  ultimately
  show ?thesis
    by fastforce
qed

lemma b_e_type_value_list:
  assumes "(\<C> \<turnstile> es@[C v] : (ts _> ts'@[t]))"
  shows "(\<C> \<turnstile> es : (ts _> ts'))"
        "(typeof v = t)"
proof -
  obtain ts'' where "(\<C> \<turnstile> es : (ts _> ts''))" "(\<C> \<turnstile> [C v] : (ts'' _> ts' @ [t]))"
    using b_e_type_comp assms
    by blast
  thus "(\<C> \<turnstile> es : (ts _> ts'))" "(typeof v = t)"
    using b_e_type_value[of \<C> "C v" "ts''" "ts' @ [t]"]
    by auto
qed

lemma e_type_label:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Label n es0 es] : (ts _> ts')"
  shows "\<exists>tls t2s. (ts' = (ts@t2s))
                \<and> length tls = n
                \<and> (\<S>\<bullet>\<C> \<turnstile> es0 : (tls _> t2s))
                \<and> (\<S>\<bullet>\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr> \<turnstile> es : ([] _> t2s))"
  using assms
proof (induction "\<S>" "\<C>" "[Label n es0 es]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  then show ?case
    by (simp add: map_eq_Cons_conv)
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  then show ?case
    by (metis append_self_conv2 b_e_type_empty last_snoc list.simps(8) unlift_b_e)
next
  case (3 \<S> \<C> t1s t2s ts)
  then show ?case
    by simp
next
  case (7 \<S> \<C> t2s)
  then show ?case
    by fastforce
qed

lemma e_type_callcl_native:
  assumes "s\<bullet>\<C> \<turnstile> [Callcl cl] : (t1s' _> t2s')"
          "cl = Func_native i tf ts es"
  shows "\<exists>t1s t2s ts_c \<C>i. (t1s' = ts_c @ t1s)
                         \<and> (t2s' = ts_c @ t2s)
                         \<and> tf = (t1s _> t2s)
                         \<and> inst_typing s i \<C>i
                         \<and> (\<C>i\<lparr>local := (local \<C>i) @ t1s @ ts, label := ([t2s] @ (label \<C>i)), return := Some t2s\<rparr>  \<turnstile> es : ([] _> t2s))"
  using assms
proof (induction "s" "\<C>" "[Callcl cl]" "(t1s' _> t2s')" arbitrary: t1s' t2s')
  case (1 \<C> b_es \<S>)
  thus ?case
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  have "\<C> \<turnstile> [] : (t1s _> t2s)"
    using 2(1,5) unlift_b_e
    by (metis Nil_is_map_conv append_Nil butlast_snoc)
  thus ?case
    using 2(4,5,6)
    by fastforce
next
  case (3 \<S> \<C> t1s t2s ts)
    thus ?case
    by fastforce
next
  case (6 \<S> \<C>)
  thus ?case
    unfolding cl_typing.simps
    by fastforce
qed

lemma e_type_callcl_host:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (t1s' _> t2s')"
          "cl = Func_host tf f"
  shows "\<exists>t1s t2s ts_c. (t1s' = ts_c @ t1s)
                        \<and> (t2s' = ts_c @ t2s)
                        \<and> tf = (t1s _> t2s)"
  using assms
proof (induction "\<S>" "\<C>" "[Callcl cl]" "(t1s' _> t2s')" arbitrary: t1s' t2s')
  case (1 \<C> b_es \<S>)
  thus ?case
    by auto
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  have "\<C> \<turnstile> [] : (t1s _> t2s)"
    using 2(1,5) unlift_b_e
    by (metis Nil_is_map_conv append_Nil butlast_snoc)
  thus ?case
    using 2(4,5,6)
    by fastforce
next
  case (3 \<S> \<C> t1s t2s ts)
    thus ?case
    by fastforce
next
  case (6 \<S> \<C>)
  thus ?case
    unfolding cl_typing.simps
    by fastforce
qed

lemma e_type_callcl:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (t1s' _> t2s')"
  shows "\<exists>t1s t2s ts_c. (t1s' = ts_c @ t1s)
                        \<and> (t2s' = ts_c @ t2s)
                        \<and> cl_type cl = (t1s _> t2s)"
proof (cases cl)
  case (Func_native x11 x12 x13 x14)
  thus ?thesis
    using e_type_callcl_native[OF assms]
    unfolding cl_type_def
    by (cases x12) fastforce
next
  case (Func_host x21 x22)
  thus ?thesis
    using e_type_callcl_host[OF assms]
    unfolding cl_type_def
    by fastforce
qed

lemma s_type_unfold:
  assumes "s\<bullet>rs \<tturnstile>_i vs;es : ts"
  shows "(rs = Some ts) \<or> rs = None"
        "\<exists>\<C>i. inst_typing s i \<C>i
              \<and> (s\<bullet>\<C>i\<lparr>local := (local \<C>i) @ (map typeof vs), return := rs\<rparr> \<turnstile> es : ([] _> ts))"
  using assms s_typing.simps
  by auto

lemma e_type_local:
  assumes "s\<bullet>\<C> \<turnstile> [Local n i vs es] : (ts _> ts')"
  shows "\<exists>tls \<C>i. inst_typing s i \<C>i
                \<and> length tls = n
                \<and> (s\<bullet>\<C>i\<lparr>local := (local \<C>i) @ (map typeof vs), return := Some tls\<rparr> \<turnstile> es : ([] _> tls))
                \<and> ts' = ts @ tls"
  using assms
proof (induction "s" "\<C>" "[Local n i vs es]" "(ts _> ts')" arbitrary: ts ts')
  case (2 \<S> \<C> es' t1s t2s e t3s)
  have "t1s = t2s"
    using 2 unlift_b_e
    by force
  thus ?case
    using 2
    by simp
qed (auto simp add: unlift_b_e s_typing.simps)

lemma e_type_local_shallow:
  assumes "\<S>\<bullet>\<C> \<turnstile> [Local n i vs es] : (ts _> ts')"
  shows "\<exists>tls. length tls = n \<and> ts' = ts@tls \<and> (\<S>\<bullet>(Some tls) \<tturnstile>_i vs;es : tls)"
  using assms
proof (induction "\<S>" "\<C>" "[Local n i vs es]" "(ts _> ts')" arbitrary: ts ts')
  case (1 \<C> b_es \<S>)
  thus ?case
  by (metis e.distinct(7) map_eq_Cons_D)
next
  case (2 \<S> \<C> es t1s t2s e t3s)
  thus ?case
  by simp (metis append_Nil append_eq_append_conv e_type_comp_conc e_type_local)
qed simp_all

(* Some proofs treat (lists of) consts as an opaque (typed) arrangement. *)
lemma e_type_const_unwrap:
  assumes "is_const e"
  shows "\<exists>v. e = $C v"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConst x23)
      thus ?thesis
        using Basic e_typing_s_typing.intros(1,3)
        by fastforce
  qed  (simp_all add: is_const_def)
qed (simp_all add: is_const_def)

lemma is_const_list1:
  assumes "ves = map (Basic \<circ> EConst) vs"
  shows "const_list ves"
  using assms
proof (induction vs arbitrary: ves)
  case Nil
  then show ?case
    unfolding const_list_def
    by simp
next
  case (Cons a vs)
  then obtain ves' where "ves' = map (Basic \<circ> EConst) vs"
    by blast
  moreover
  have "is_const ((Basic \<circ> EConst) a)"
    unfolding is_const_def
    by simp
  ultimately
  show ?case
    using Cons
    unfolding const_list_def
      (* WHYYYYYY *)
    by auto
qed

lemma is_const_list:
  assumes "ves = $$* vs"
  shows "const_list ves"
  using assms is_const_list1
  unfolding comp_def
  by auto

lemma const_list_cons_last:
  assumes "const_list (es@[e])"
  shows "const_list es"
        "is_const e"
  using assms list_all_append[of is_const es "[e]"]
  unfolding const_list_def
  by auto

lemma consts_cons_last:
  assumes "es@[e] = $$* ves"
  shows "const_list es"
        "is_const e"
  using assms is_const_list const_list_cons_last
  by blast+

lemma consts_cons_last2:
  assumes "es@[e,e'] = $$* ves"
  shows "const_list es"
        "is_const e"
        "is_const e'"
  apply (metis assms const_list_def is_const_list list_all_append)
  apply (metis (full_types) assms const_list_def is_const_list list_all_append list_all_simps(1))+
  done

lemma consts_cons_last3:
  assumes "es@[e,e',e''] = $$* ves"
  shows "const_list es"
        "is_const e"
        "is_const e'"
        "is_const e'"
  apply (metis assms const_list_def is_const_list list_all_append)
  apply (metis (full_types) assms const_list_def is_const_list list_all_append list_all_simps(1))+
  done

lemma consts_cons:
  assumes "e#es = $$* ves"
  shows "\<exists>ves. es = $$* ves"
        "is_const e"
  apply (metis assms map_eq_Cons_conv)
  apply (metis assms const_list_def is_const_list list_all_simps(1))
  done

lemma consts_app_ex:
  assumes "es@es' = $$* ves"
  shows "\<exists>ves'. es = $$*ves'"
        "\<exists>ves''. es' = $$*ves''"
  using assms
proof (induction es arbitrary: ves)
  case Nil
  fix ves
  assume "[] @ es' = $$* ves"
  thus "\<exists>ves'. [] = $$*ves'"
       "\<exists>ves''. es' = $$*ves''"
    by auto
next
  case (Cons a es)
  fix ves
  assume "(\<And>ves. es @ es' = $$* ves \<Longrightarrow> \<exists>ves'. es = $$* ves')"
         "(\<And>ves. es @ es' = $$* ves \<Longrightarrow> \<exists>ves''. es' = $$* ves'')"
         "(a # es) @ es' = $$* ves"
  thus "\<exists>ves'. a # es = $$* ves'"
       "\<exists>ves''. es' = $$* ves''"
    using map_eq_Cons_D[of "(\<lambda>v. $C v)" ves a]
    by (metis append_Cons list.simps(9),(metis append_Cons))
qed

lemma consts_app_snoc:
  assumes "es @ es' = ($$* ves) @ [e]"
  shows "(es = ($$* ves) @ [e] \<and> es' = []) \<or>
           (\<exists>ves' ves''. es = ($$* ves') \<and> es' = ($$* ves'')@[e] \<and> ves = ves'@ves'')"
proof (cases es' rule: rev_cases)
  case Nil
  thus ?thesis
    using assms
    by simp
next
  case (snoc ys y)
  then obtain ves' ves'' where "es = ($$* ves') \<and> ys = ($$* ves'') \<and> y = e"
    using assms
    using consts_app_ex
    by (metis append.assoc butlast_snoc snoc_eq_iff_butlast)
  moreover
  hence "ves = ves'@ves''"
    using assms snoc map_injective[OF _ inj_basic_econst]
    by auto
  ultimately
  show ?thesis
    using snoc
    by auto
qed

lemma consts_app_snoc3:
  assumes "es @ es' @ es'' = ($$* ves) @ [e]"
  shows "(es = ($$* ves) @ [e] \<and> es' = [] \<and> es'' = []) \<or> 
         (\<exists>ves' ves''. es = ($$*ves') \<and> es' = ($$* ves'') @ [e] \<and> es'' = [] \<and> ves = ves'@ves'') \<or>
           (\<exists>ves' ves'' ves'''. es = ($$* ves') \<and> es' = ($$* ves'') \<and> es'' = ($$* ves''')@[e] \<and> ves = ves'@ves''@ves''')"
proof -
  consider (1) "es @ es' = ($$* ves) @ [e]" "es'' = []"
         | (2) "(\<exists>ves' ves''.
                  es @ es' = ($$* ves') \<and>
                  es'' = ($$* ves'') @ [e] \<and>
                  ves = ves' @ ves'')"
    using assms consts_app_snoc[of "es@es'" "es''" ves e]
    by fastforce
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using consts_app_snoc[OF 1(1)]
      by blast
  next
    case 2
    thus ?thesis
      using consts_app_ex[of es es']
      by (metis (no_types, lifting) append.assoc inj_basic_econst map_append map_injective)
  qed
qed

lemma consts_app_snoc_1:
  assumes "($$* ves) @ es = ($$* ves') @ [$C v, e]"
          "\<not>is_const e"
  shows "(es = [e] \<and> ves = ves' @ [v]) \<or>
         (\<exists>ves''. es = ($$*ves'')@[$C v, e] \<and> ves' = ves@ves'')"
proof -
  consider (1) "($$* ves) = ($$* ves' @ [v]) @ [e]" "es = []"
         | (2) "(\<exists>ves'a ves''. ($$* ves) = ($$* ves'a) \<and> es = ($$* ves'') @ [e] \<and> ves' @ [v] = ves'a @ ves'')"
    using consts_app_snoc[of "$$*ves" es "ves'@[v]" e] assms
    by fastforce
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      using consts_cons_last(2)[of "($$* ves' @ [v])" e] assms(2)
      by metis
  next
    case 2
    then obtain ves'a ves'' where
         "($$* ves) = ($$* ves'a)"
         "es = ($$* ves'') @ [e]"
         "ves' @ [v] = ves'a @ ves''"
      by blast
    thus ?thesis
      apply (cases ves'' rule : rev_cases)
       apply (auto simp add: inj_basic_econst)
      done
  qed
qed

lemma consts_app_snoc_2:
  assumes "($$* ves) @ es = ($$* ves') @ [$C v1, $C v2, e]"
          "\<not>is_const e"
  shows "(es = [e] \<and> ves = ves' @ [v1, v2]) \<or>
         (es = [$C v2, e] \<and> ves = ves'@[v1]) \<or>
         (\<exists>ves''. es = ($$*ves'')@[$C v1, $C v2, e] \<and> ves' = ves@ves'')"
proof -
  consider (1) "es = [e] \<and> ves = (ves' @ [v1]) @ [v2]"
         | (2) ves'' where "(es = ($$* ves'') @ [$C v2, e] \<and>  ves' @ [v1] = ves @ ves'')"
  using consts_app_snoc_1[of ves es "ves'@[v1]" v2 e] assms
  by fastforce
  thus ?thesis
  proof cases
    case 2
    thus ?thesis
      apply (cases ves'' rule: rev_cases)
       apply simp_all
      done
  qed simp_all
qed

lemma consts_app_snoc_1_const_list:
  assumes "es @ es' = ($$* ves') @ [$C v, e]"
          "\<not>is_const e"
          "\<not> const_list es"
  shows "es' = []"
  using consts_app_snoc[of es es' "ves'@[v]" e] assms is_const_list
  apply simp
  apply safe
   apply blast
  apply blast
  done

lemma consts_app_snoc_2_const_list:
  assumes "es @ es' = ($$* ves') @ [$C v1, $C v2, e]"
          "\<not>is_const e"
          "\<not> const_list es"
  shows "es' = []"
  using consts_app_snoc[of es es' "ves'@[v1,v2]" e] assms is_const_list
  apply simp
  apply safe
   apply blast
  apply blast
  done

lemma consts_app_snoc_3_const_list:
  assumes "es @ es' = ($$* ves') @ [$C v1, $C v2, $C v3, e]"
          "\<not>is_const e"
          "\<not> const_list es"
  shows "es' = []"
  using consts_app_snoc[of es es' "ves'@[v1,v2,v3]" e] assms is_const_list
  apply simp
  apply safe
   apply blast
  apply blast
  done

lemma consts_app:
  assumes "es @ es' = ($$* ves) @ es''"
  shows "(\<exists>ves' ves''. es = ($$* ves') \<and> es' = ($$* ves'')@es'' \<and> ves = ves'@ves'') \<or>
           (\<exists>es_1 es_2. es = ($$* ves)@es_1 \<and> es' = es_2 \<and> es'' = es_1@es_2)"
proof -
  obtain us where us_def:"(es = ($$* ves) @ us \<and> us @ es' = es'') \<or> (es @ us = ($$* ves) \<and> es' = us @ es'')"
    using append_eq_append_conv2[of es es' "($$* ves)" es''] assms
    by blast
  show ?thesis
  proof -
    obtain vvs :: "e list \<Rightarrow> v list" where
      f2: "\<forall>es esa vs. es @ esa \<noteq> $$* vs \<or> es = $$* vvs es"
      by (metis consts_app_ex(1))
    obtain vvsa :: "e list \<Rightarrow> v list" where
      f3: "\<forall>x1. (\<exists>v3. x1 = $$* v3) = (x1 = $$* vvsa x1)"
      by moura
    moreover
    { assume "ves \<noteq> vvs es @ vvsa us"
      then have "$$* ves \<noteq> $$* vvs es @ vvsa us"
        using inj_basic_econst map_injective by blast
      then have "es @ us \<noteq> $$* ves \<or> es' \<noteq> us @ es''"
        using f3 f2 by (metis (no_types) consts_app_ex(2) map_append) }
    ultimately show ?thesis
      using f2 us_def by (metis (no_types) consts_app_ex(2))
  qed
qed

lemma e_type_const1:
  assumes "is_const e"
  shows "\<exists>t. (\<S>\<bullet>\<C> \<turnstile> [e] : (ts _> ts@[t]))"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConst x23)
      hence "\<C> \<turnstile> [x1] : ([] _> [typeof x23])"
        by (simp add: b_e_typing.intros(1))
      thus ?thesis
        using Basic e_typing_s_typing.intros(1,3)
        by (metis append_Nil2 to_e_list_1)
  qed  (simp_all add: is_const_def)
qed (simp_all add: is_const_def)

lemma e_type_const:
  assumes "is_const e"
          "\<S>\<bullet>\<C> \<turnstile> [e] : (ts _> ts')"
  shows  "\<exists>t. (ts' = ts@[t]) \<and> (\<S>\<bullet>\<C>' \<turnstile> [e] : ([] _> [t]))"
  using assms
proof (cases e)
  case (Basic x1)
  then show ?thesis
    using assms
  proof (cases x1)
    case (EConst x23)
      then have "ts' = ts @ [typeof x23]"
        by (metis (no_types) Basic assms(2) b_e_type_value list.simps(8,9) unlift_b_e)
      moreover
      have "\<S>\<bullet>\<C>' \<turnstile> [e] : ([] _> [typeof x23])"
        using Basic EConst b_e_typing.intros(1) e_typing_s_typing.intros(1)
        by fastforce
      ultimately
      show ?thesis
        by simp
  qed  (simp_all add: is_const_def)
qed (simp_all add: is_const_def)

lemma const_typeof:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
  shows "typeof v = t"
  using assms
proof -
  have "\<C> \<turnstile> [C v] : ([] _> [t])"
    using unlift_b_e assms
    by fastforce
  thus ?thesis
    by (induction "[C v]" "([] _> [t])" rule: b_e_typing.induct, auto)
qed

lemma e_type_const_list:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts')"
  shows   "\<exists>tvs. ts' = ts @ tvs \<and> length vs = length tvs \<and> (\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tvs))"
  using assms
proof (induction vs arbitrary: ts ts' rule: List.rev_induct)
  case Nil
  have "\<S>\<bullet>\<C>' \<turnstile> [] : ([] _> [])"
    using b_e_type_empty[of \<C>' "[]" "[]"] e_typing_s_typing.intros(1)
    by fastforce
  thus ?case
    using Nil
    by (metis append_Nil2 b_e_type_empty list.map(1) list.size(3) unlift_b_e)
next
  case (snoc x xs)
  hence v_lists:"list_all is_const xs" "is_const x"
  unfolding const_list_def
  by simp_all
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> xs : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [x] : (ts'' _> ts')"
    using snoc(3) e_type_comp
    by fastforce
  then obtain ts_b where ts_b_def:"ts'' = ts @ ts_b" "length xs = length ts_b" "\<S>\<bullet>\<C>' \<turnstile> xs : ([] _> ts_b)"
    using snoc(1) v_lists(1)
    unfolding const_list_def
    by fastforce
  then obtain t where t_def:"ts' = ts @ ts_b @ [t]" "\<S>\<bullet>\<C>' \<turnstile> [x] : ([] _> [t])"
    using e_type_const v_lists(2) ts''_def
    by fastforce
  moreover
  then have "length (ts_b@[t]) = length (xs@[x])"
    using ts_b_def(2)
    by simp
  moreover
  have "\<S>\<bullet>\<C>' \<turnstile> (xs@[x]) : ([] _> ts_b@[t])"
    using ts_b_def(3) t_def e_typing_s_typing.intros(2,3)
    by fastforce
  ultimately
  show ?case
    by simp
qed

lemma e_type_const_list_snoc:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : ([] _> ts@[t])"
  shows "\<exists>vs1 v2. (\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts))
                   \<and> (\<S>\<bullet>\<C> \<turnstile> [v2] : (ts _> ts@[t]))
                   \<and> (vs = vs1@[v2])
                   \<and> const_list vs1
                   \<and> is_const v2"
  using assms
proof -
  obtain vs' v where vs_def:"vs = vs'@[v]"
    using e_type_const_list[OF assms(1,2)]
    by (metis append_Nil append_eq_append_conv list.size(3) snoc_eq_iff_butlast)
  hence consts_def:"const_list vs'" "is_const v"
    using assms(1)
    unfolding const_list_def
    by auto
  obtain ts' where ts'_def:"\<S>\<bullet>\<C> \<turnstile> vs' : ([] _> ts')" "\<S>\<bullet>\<C> \<turnstile> [v] : (ts' _> ts@[t])"
    using vs_def assms(2) e_type_comp[of \<S> \<C> vs' v "[]" "ts@[t]"]
    by fastforce
  obtain c where "v = $C c"
    using e_type_const_unwrap consts_def(2)
    by fastforce
  hence "ts' = ts"
    using ts'_def(2) unlift_b_e[of \<S> \<C> "[C c]"] b_e_type_value
    by fastforce
  thus ?thesis using ts'_def vs_def consts_def
    by simp
qed
    
lemma e_type_const_list_cons:
  assumes "const_list vs"
          "\<S>\<bullet>\<C> \<turnstile> vs : ([] _> (ts1@ts2))"
  shows "\<exists>vs1 vs2. (\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts1))
                   \<and> (\<S>\<bullet>\<C> \<turnstile> vs2 : (ts1 _> (ts1@ts2)))
                   \<and> vs = vs1@vs2
                   \<and> const_list vs1
                   \<and> const_list vs2"
  using assms
proof (induction "ts1@ts2" arbitrary: vs ts1 ts2 rule: List.rev_induct)
  case Nil
  thus ?case
    using e_type_const_list
    by fastforce
next
  case (snoc t ts)
  note snoc_outer = snoc
  show ?case
  proof (cases ts2 rule: List.rev_cases)
    case Nil
    have "\<S>\<bullet>\<C> \<turnstile> [] : (ts1 _> ts1 @ [])"
      using b_e_typing.empty b_e_typing.weakening e_typing_s_typing.intros(1)
      by fastforce
    then show ?thesis
      using snoc(3,4) Nil
      unfolding const_list_def
      by auto
  next
    case (snoc ts2' a)
    obtain vs1 v2 where vs1_def:"(\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts1 @ ts2'))"
                                "(\<S>\<bullet>\<C> \<turnstile> [v2] : (ts1 @ ts2' _> ts1 @ ts2' @[t]))"
                                "(vs = vs1@[v2])"
                                "const_list vs1"
                                "is_const v2"
                                "ts = ts1 @ ts2'"
      using e_type_const_list_snoc[OF snoc_outer(3), of \<S> \<C> "ts1@ts2'" t]
            snoc_outer(2,4) snoc
      by fastforce
    show ?thesis
      using snoc_outer(1)[OF vs1_def(6,4,1)] snoc_outer(2) vs1_def(3,5)
            e_typing_s_typing.intros(2)[OF _ vs1_def(2), of _ ts1]
            snoc
      unfolding const_list_def
      by fastforce
  qed
qed

lemma e_type_const_conv_vs:
  assumes "const_list ves"
  shows "\<exists>vs. ves = $$* vs"
  using assms
proof (induction ves)
  case Nil
  thus ?case
    by simp
next
  case (Cons a ves)
  thus ?case
  using e_type_const_unwrap
  unfolding const_list_def
  by (metis (no_types, lifting) list.pred_inject(2) list.simps(9)) 
qed

lemma types_exist_lfilled:
  assumes "Lfilled k lholed es lfilled"
          "\<S>\<bullet>\<C> \<turnstile> lfilled : (ts _> ts')"
  shows "\<exists>t1s t2s \<C>' arb_label. (\<S>\<bullet>\<C>\<lparr>label := arb_label@(label \<C>)\<rparr> \<turnstile> es : (t1s _> t2s))"
  using assms
proof (induction arbitrary: \<C> ts ts' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  hence "\<S>\<bullet>(\<C>\<lparr>label := label \<C>\<rparr>) \<turnstile> vs @ es @ es' : (ts _> ts')"
    by simp
  thus ?case
    using e_type_comp_conc2
    by (metis append_Nil)
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk]  : (ts'' _> ts''')"
    using e_type_comp_conc2[OF LN(5)]
    by fastforce
  then obtain t1s t2s ts where test:"\<S>\<bullet>\<C>\<lparr>label := [ts] @ (label \<C>)\<rparr> \<turnstile> lfilledk  : (t1s _> t2s)"
    using e_type_label
    by metis
  show ?case
    using LN(4)[OF test(1)]
    by simp (metis append.assoc append_Cons append_Nil)
qed

lemma types_exist_lfilled_weak:
  assumes "Lfilled k lholed es lfilled"
          "\<S>\<bullet>\<C> \<turnstile> lfilled : (ts _> ts')"
  shows "\<exists>t1s t2s \<C>' arb_label arb_return. (\<S>\<bullet>\<C>\<lparr>label := arb_label, return := arb_return\<rparr> \<turnstile> es : (t1s _> t2s))"
proof -
  have "\<exists>t1s t2s \<C>' arb_label. (\<S>\<bullet>\<C>\<lparr>label := arb_label, return := (return \<C>)\<rparr> \<turnstile> es : (t1s _> t2s))"
    using types_exist_lfilled[OF assms]
    by fastforce
  thus ?thesis
    by fastforce
qed

lemma global_extension_refl:
  shows "global_extension g g"
  unfolding global_extension_def
  by auto

lemma mem_extension_refl:
  shows "mem_extension m m"
  unfolding mem_extension_def
  by auto

lemma store_extension_refl:
  shows "store_extension s s"
  using global_extension_refl mem_extension_refl
  unfolding store_extension.simps list_all2_conv_all_nth
  by (metis (full_types) unit.exhaust s.surjective)

lemma store_extension_mem_leq:
  assumes "s.mem s ! j = m"
          "mem_size m \<le> mem_size m'"
  shows "store_extension s (s\<lparr>s.mem := s.mem s[j := m']\<rparr>)"
proof -
  obtain s' where s'_def:"s' = (s\<lparr>s.mem := s.mem s[j := m']\<rparr>)"
    by blast
  hence "funcs s = funcs s'"
        "tab s = tab s'"
        "globs s = globs s'"
    by simp_all
  moreover
  have "mem_extension m m'"
    using assms(2)
    unfolding mem_extension_def
    by simp
  hence "list_all2 mem_extension (mem s) (mem s')"
    using assms(1) s'_def
    by (simp, metis eq_iff list.rel_refl list_all2_update_cong list_update_id mem_extension_def)
  ultimately
  show ?thesis
    using s'_def store_extension.intros global_extension_refl
    by (metis (full_types) list_all2_refl unit.exhaust s.surjective)
qed

lemma global_extension_update:
  assumes "g_mut g = T_mut"
          "typeof (g_val g) = typeof v"
  shows "global_extension g (g\<lparr>g_val := v\<rparr>)"
  using assms
  unfolding global_extension_def
  by auto

lemma update_glob_store_extension:
  assumes "supdate_glob s i j v = s'"
          "(globs s)!sglob_ind s i j = g"
          "g_mut g = T_mut"
          "typeof (g_val g) = typeof v"
  shows "store_extension s s'"
proof -
  obtain k where k_def:"k = (sglob_ind s i j)"
    by blast
  hence s'_def:"s' = s\<lparr>s.globs := s.globs s[k := (s.globs s ! k)\<lparr>g_val := v\<rparr>]\<rparr>"
    using assms(1)
    unfolding supdate_glob_def sglob_ind_def supdate_glob_s_def
    by metis
  hence "global_extension ((globs s)!k) ((globs s')!k)"
    using global_extension_update assms(2,3,4)
    by (simp, metis global.surjective global.update_convs(2) k_def length_list_update nth_equalityI nth_list_update nth_list_update_neq)
  hence "list_all2 global_extension (globs s) (globs s')"
    using s'_def global_extension_refl
    by (simp, metis list_all2_refl list_all2_update_cong list_update_id list_update_overwrite)
  moreover
  have "(funcs s) = (funcs s')"
       "(tab s) = (tab s')"
       "list_all2 mem_extension (mem s) (mem s')"
    using s'_def mem_extension_refl list_all2_refl
    by auto
  ultimately
  show ?thesis
    using s'_def store_extension.intros
    by (metis (full_types) unit.exhaust s.surjective)
qed

lemma inst_typing_glob_length:
  assumes "inst_typing s i \<C>"
  shows "length (global \<C>) = length (inst.globs i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by force

lemma inst_typing_func_length:
  assumes "inst_typing s i \<C>"
  shows "length (func_t \<C>) = length (inst.funcs i)"
  using assms list_all2_lengthD
  unfolding inst_typing.simps
  by force

lemma store_typing_imp_glob_agree:
  assumes "inst_typing s i \<C>"
          "j < length (global \<C>)"
  shows "(sglob_ind s i j) < length (globs s)"
        "glob_agree (sglob s i j) ((global \<C>)!j)"
proof -
  show "glob_agree (sglob s i j) ((global \<C>)!j)"
       "(sglob_ind s i j) < length (globs s)"
    using assms
    unfolding inst_typing.simps sglob_def sglob_ind_def list_all2_conv_all_nth
    by (metis globi_agree_def inst.select_convs(5) t_context.select_convs(3))+
qed

lemma store_typing_imp_types_eq:
  assumes "inst_typing s i \<C>"
          "j < length (types_t \<C>)"
  shows "(types_t \<C>)!j = (types i)!j"
  using assms
  unfolding inst_typing.simps
  by auto

lemma cl_type_exists:
  assumes "cl_typing s cl tf"
  shows "tf = cl_type cl"
  using assms
  unfolding cl_type_def
  by (induction) auto

lemma store_typing_imp_func_agree:
  assumes "store_typing s"
          "inst_typing s i \<C>"
          "j < length (inst.funcs i)"
  shows "funci_agree (funcs s) (sfunc_ind s i j) ((func_t \<C>)!j)"
        "cl_typing s (sfunc s i j) ((func_t \<C>)!j)"
proof -
  show 1:"funci_agree (funcs s) (sfunc_ind s i j) ((func_t \<C>)!j)"
    using assms(2,3) list_all2_nthD
    unfolding inst_typing.simps sfunc_ind_def
    by fastforce
  hence "\<exists>t. cl_typing s (sfunc s i j) t"
    using assms
    unfolding store_typing.simps sfunc_ind_def sfunc_def funci_agree_def
    by (simp add: list_all_length)
  thus "cl_typing s (sfunc s i j) ((func_t \<C>)!j)"
    using cl_type_exists 1
    unfolding funci_agree_def sfunc_def
    by auto
qed
(*
lemma store_typing_imp_func_agree:
  assumes "store_typing s"
          "inst_typing s i \<C>"
  shows "(sfunc_ind s i j) < length (s_funcs \<S>)"
        "cl_typing \<S> (sfunc s i j) ((s_funcs \<S>)!(sfunc_ind s i j))"
        "((s_funcs \<S>)!(sfunc_ind s i j)) = (func_t ((s_inst \<S>)!i))!j"
proof -
  have funcs_agree:"list_all2 (cl_typing \<S>) (funcs s) (s_funcs \<S>)"
    using assms(1)
    unfolding store_typing.simps
    by auto
  have "list_all2 (funci_agree (s_funcs \<S>)) (inst.funcs ((inst s)!i)) (func_t ((s_inst \<S>)!i))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  hence "funci_agree (s_funcs \<S>) ((inst.funcs ((inst s)!i))!j) ((func_t ((s_inst \<S>)!i))!j)"
    using assms(3) list_all2_nthD2
    by blast
  thus "(sfunc_ind s i j) < length (s_funcs \<S>)"
       "((s_funcs \<S>)!(sfunc_ind s i j)) = (func_t ((s_inst \<S>)!i))!j"
    unfolding funci_agree_def sfunc_ind_def
    by auto
  thus "cl_typing \<S> (sfunc s i j) ((s_funcs \<S>)!(sfunc_ind s i j))"
    using funcs_agree list_all2_nthD2
    unfolding sfunc_def
    by fastforce
qed

lemma store_typing_imp_glob_agree:
  assumes "store_typing s \<S>"
          "i < length (s_inst \<S>)"
          "j < length (global ((s_inst \<S>)!i))"
  shows "(sglob_ind s i j) < length (s_globs \<S>)"
        "glob_agree (sglob s i j) ((s_globs \<S>)!(sglob_ind s i j))"
        "((s_globs \<S>)!(sglob_ind s i j)) = (global ((s_inst \<S>)!i))!j"
proof -
  have globs_agree:"list_all2 glob_agree (globs s) (s_globs \<S>)"
    using assms(1)
    unfolding store_typing.simps
    by auto
  have "list_all2 (globi_agree (s_globs \<S>)) (inst.globs ((inst s)!i)) (global ((s_inst \<S>)!i))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  hence "globi_agree (s_globs \<S>) ((inst.globs ((inst s)!i))!j) ((global ((s_inst \<S>)!i))!j)"
    using assms(3) list_all2_nthD2
    by blast
  thus "(sglob_ind s i j) < length (s_globs \<S>)"
       "((s_globs \<S>)!(sglob_ind s i j)) = (global ((s_inst \<S>)!i))!j"
    unfolding globi_agree_def sglob_ind_def
    by auto
  thus "glob_agree (sglob s i j) ((s_globs \<S>)!(sglob_ind s i j))"
    using globs_agree list_all2_nthD2
    unfolding sglob_def
    by fastforce
qed

lemma store_typing_imp_mem_agree_Some:
  assumes "store_typing s \<S>"
          "i < length (s_inst \<S>)"
          "smem_ind s i = Some j"
  shows "j < length (s_mem \<S>)"
        "mem_agree ((mem s)!j) ((s_mem \<S>)!j)"
        "\<exists>x. ((s_mem \<S>)!j) = x \<and> (memory ((s_inst \<S>)!i)) = Some x"
proof -
  have mems_agree:"list_all2 mem_agree (mem s) (s_mem \<S>)"
  using assms(1)
  unfolding store_typing.simps
  by auto
  hence "memi_agree (s_mem \<S>) ((inst.mem ((inst s)!i))) ((memory ((s_inst \<S>)!i)))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  thus "j < length (s_mem \<S>)"
       "\<exists>x. ((s_mem \<S>)!j) = x \<and> (memory ((s_inst \<S>)!i)) = Some x"
    using assms(3)
    unfolding memi_agree_def smem_ind_def
    by auto
  thus "mem_agree ((mem s)!j) ((s_mem \<S>)!j)"
    using mems_agree list_all2_nthD2
    unfolding sglob_def
    by fastforce
qed

lemma store_typing_imp_mem_agree_None:
  assumes "store_typing s \<S>"
          "i < length (s_inst \<S>)"
          "smem_ind s i = None"
  shows "(memory ((s_inst \<S>)!i)) = None"
proof -
  have mems_agree:"list_all2 mem_agree (mem s) (s_mem \<S>)"
  using assms(1)
  unfolding store_typing.simps
  by auto
  hence "memi_agree (s_mem \<S>) ((inst.mem ((inst s)!i))) ((memory ((s_inst \<S>)!i)))"
    using assms(1,2) store_typing_imp_inst_length_eq store_typing_imp_inst_typing
    by (fastforce simp add: inst_typing.simps)
  thus ?thesis
    using assms(3)
    unfolding memi_agree_def smem_ind_def
    by auto
qed

lemma store_mem_exists:
  assumes "i < length (s_inst \<S>)"
          "store_typing s \<S>"
  shows "Option.is_none (memory ((s_inst \<S>)!i)) = Option.is_none (inst.mem ((inst s)!i))"
proof -
  obtain j where j_def:"j = (inst.mem ((inst s)!i))"
    by blast
  obtain m where m_def:"m = (memory ((s_inst \<S>)!i))"
    by blast
  have inst_typ:"inst_typing \<S> ((inst s)!i) ((s_inst \<S>)!i)"
    using assms
    unfolding store_typing.simps list_all2_conv_all_nth
    by auto
  thus ?thesis
    unfolding inst_typing.simps memi_agree_def
    by auto
qed
*)

lemma store_mem_exists:
  assumes "inst_typing s i \<C>"
  shows "(memory \<C>) = (\<not>Option.is_none (inst.mem i))"
  using assms
  unfolding inst_typing.simps memi_agree_def
  by (cases "(inst.mem i)")  auto
  
lemma inst_typing_store_extension_inv:
  assumes "inst_typing s i \<C>"
          "store_extension s s'" 
    shows "inst_typing s' i \<C>"
proof -
  have 1:"list_all2 (globi_agree (globs s)) (inst.globs i) (global \<C>)"
         "memi_agree (mem s) (inst.mem i) (memory \<C>)"
    using assms(1)
    unfolding inst_typing.simps
    by auto
  have "funcs s = funcs s'"
       "tab s = tab s'"
    using assms(2)
    unfolding store_extension.simps
    by auto
  hence "list_all2 (funci_agree (funcs s')) (inst.funcs i) (func_t \<C>)"
        "tabi_agree (tab s') (inst.tab i) (table \<C>)"
    using assms(1)
    unfolding inst_typing.simps
    by auto
  moreover
  have "\<And>tg i. i < length (globs s) \<Longrightarrow> glob_agree ((globs s)!i) tg \<Longrightarrow> glob_agree ((globs s')!i) tg"
       "length (globs s) = length (globs s')"
    using assms(2)
    unfolding glob_agree_def store_extension.simps global_extension_def list_all2_conv_all_nth
    by auto
  hence "list_all2 (globi_agree (globs s')) (inst.globs i) (global \<C>)"
    using 1(1)
    unfolding globi_agree_def list_all2_conv_all_nth
    by fastforce
  moreover
  have "memi_agree (mem s') (inst.mem i) (memory \<C>)"
    using 1(2) assms(2)
    unfolding memi_agree_def
    by (auto simp add: list_all2_lengthD store_extension.simps split: option.split)
  ultimately
  show ?thesis
    using assms(1)
    unfolding inst_typing.simps
    by auto
qed

lemma cl_typing_store_extension_inv:
  assumes "store_extension s s'"
          "cl_typing s cl tf"
  shows "cl_typing s' cl tf"
proof (cases cl)
  case (Func_native x11 x12 x13 x14)
  thus ?thesis
    using assms
    unfolding cl_typing.simps
    by (simp, metis (no_types, lifting) inst_typing_store_extension_inv)
next
  case (Func_host x21 x22)
  thus ?thesis
    using assms
    unfolding cl_typing.simps
    by auto
qed


lemma e_typing_s_typing_store_extension_inv:
  assumes"store_extension s s'"
  shows "s\<bullet>\<C> \<turnstile> es : tf \<Longrightarrow> s'\<bullet>\<C> \<turnstile> es : tf"
        "s\<bullet>rs \<tturnstile>_i vs;es : ts \<Longrightarrow> s'\<bullet>rs \<tturnstile>_i vs;es : ts"
  using assms
proof (induction s \<C> es tf and s rs i vs es ts rule: e_typing_s_typing.inducts)
  case (6 s cl tf \<C>)
  thus ?case
    using cl_typing_store_extension_inv e_typing_s_typing.intros(6)
    by blast
next
  case (8 tvs vs s i \<C>i \<C> rs es ts)
  show ?case
    using inst_typing_store_extension_inv[OF 8(2) 8(7)]
          e_typing_s_typing.intros(8)[OF 8(1) _ 8(3) 8(6)[OF 8(7)] 8(5)]
    by blast
qed (auto simp add: e_typing_s_typing.intros)

lemma tab_agree_store_extension_inv:
  assumes "store_extension s s'"
          "tab_agree s t"
  shows "tab_agree s' t"
  using assms cl_typing_store_extension_inv
  unfolding tab_agree_def
  by (fastforce split: option.splits)

lemma store_extension_imp_store_typing:
  assumes "store_extension s s'"
          "store_typing s"
  shows "store_typing s'"
proof -
  have 1:"funcs s = funcs s'"
         "tab s = tab s"
    using assms(1)
    unfolding store_extension.simps
    by auto
  moreover
  have "list_all (\<lambda>cl. \<exists>tf. cl_typing s cl tf) (funcs s)"
       "list_all (list_all (tab_agree s)) (tab s)"
    using assms(2)
    unfolding store_typing.simps
    by auto
  hence "list_all (list_all (tab_agree s')) (tab s')"
        "list_all (\<lambda>cl. \<exists>tf. cl_typing s' cl tf) (funcs s')"
    using cl_typing_store_extension_inv[OF assms(1)]
          tab_agree_store_extension_inv[OF assms(1)] 1
          assms(1) store_extension.simps
    unfolding list_all_length
    by fastforce+
  ultimately
  show ?thesis
    using assms(2)
    unfolding store_typing.simps
    by auto
qed

lemma types_agree_imp_e_typing:
  assumes "types_agree t v"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
  using assms e_typing_s_typing.intros(1)[OF b_e_typing.intros(1)]
  unfolding types_agree_def
  by fastforce

lemma list_types_agree_imp_e_typing:
  assumes "list_all2 types_agree ts vs"
  shows "\<S>\<bullet>\<C> \<turnstile> $$* vs : ([] _> ts)"
  using assms
proof (induction rule: list_all2_induct)
  case Nil
  thus ?case
    using b_e_typing.empty e_typing_s_typing.intros(1)
    by fastforce
next
  case (Cons t ts v vs)
  hence "\<S>\<bullet>\<C> \<turnstile> [$C v] : ([] _> [t])"
    using types_agree_imp_e_typing
    by fastforce
  thus ?case
    using e_typing_s_typing.intros(3)[OF Cons(3), of "[t]"] e_type_comp_conc
    by fastforce
qed

lemma b_e_typing_imp_list_types_agree:
  assumes "\<C> \<turnstile> (map (\<lambda>v. C v) vs) : (ts' _> ts'@ts)"
  shows "list_all2 types_agree ts vs"
  using assms
proof (induction "(map (\<lambda>v. C v) vs)" "(ts' _> ts'@ts)" arbitrary: ts ts' vs rule: b_e_typing.induct)
  case (composition \<C> es t1s t2s e)
  obtain vs1 vs2 where es_e_def:"es = map EConst vs1" "[e] = map EConst vs2" "vs1@vs2=vs"  
    using composition(5)
    by (metis (no_types) last_map list.simps(8,9) map_butlast snoc_eq_iff_butlast)
  have "const_list ($*es)"
    using es_e_def(1) is_const_list1
    by auto
  then obtain tvs1 where "t2s = t1s@tvs1"
    using e_type_const_list e_typing_s_typing.intros(1)[OF composition(1)]
    by fastforce
  moreover
  have "const_list ($*[e])"
    using es_e_def(2) is_const_list1
    by auto
  then obtain tvs2 where "t1s @ ts = t2s @ tvs2"
    using e_type_const_list e_typing_s_typing.intros(1)[OF composition(3)]
    by fastforce
  ultimately
  show ?case
    using composition(2,4,5) es_e_def
    by (auto simp add: list_all2_appendI)
qed (auto simp add: types_agree_def)

lemma e_typing_imp_list_types_agree:
  assumes "\<S>\<bullet>\<C> \<turnstile> ($$* vs) : (ts' _> ts'@ts)"
  shows "list_all2 types_agree ts vs"
proof -
  have "($$* vs) = $* (map (\<lambda>v. C v) vs)"
    by simp
  thus ?thesis
    using assms unlift_b_e b_e_typing_imp_list_types_agree
    by (fastforce simp del: map_map)
qed

lemma lfilled_deterministic:
  assumes "Lfilled k lfilled es les"
          "Lfilled k lfilled es les'"
  shows "les = les'"
  using assms
proof (induction arbitrary: les' rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    by (fastforce simp add: Lfilled.simps[of 0])
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  thus ?case
    unfolding Lfilled.simps[of "(k + 1)"]
    by fastforce
qed

lemma types_preserved_set_global_aux:
  assumes "s\<bullet>\<C> \<turnstile> [$C v, $Set_global j] : (ts _> ts')"
  shows "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "tg_t (global \<C> ! j) = typeof v"
        "tg_mut (global \<C> ! j) = T_mut"
        "j < length(global \<C>)"
proof -
  obtain ts'' where ts''_def:"s\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts'')" 
                             "s\<bullet>\<C> \<turnstile> [$Set_global j] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence "ts'' = ts@[typeof v]"
    using b_e_type_value unlift_b_e[of s \<C> "[C v]"]
    by fastforce
  hence "ts = ts'" "tg_t (global \<C> ! j) = typeof v" "tg_mut (global \<C> ! j) = T_mut"  "j < length(global \<C>)"
    using b_e_type_set_global ts''_def(2) unlift_b_e[of s \<C> "[Set_global j]"]
    by fastforce+
  thus "s'\<bullet>\<C> \<turnstile> [] : (ts _> ts')" "tg_t (global \<C> ! j) = typeof v" "tg_mut (global \<C> ! j) = T_mut" "j < length(global \<C>)"
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_s_typing.intros(1)
    by fastforce+
qed
end
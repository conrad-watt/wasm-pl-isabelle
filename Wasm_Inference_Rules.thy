theory Wasm_Inference_Rules imports Wasm_Assertions_Shallow begin

definition stack_ass_ind_on_glob :: "'a stack_ass \<Rightarrow> nat \<Rightarrow> bool" where
  "stack_ass_ind_on_glob St n \<equiv>
     (\<forall>vs v_st g. stack_ass_sat St vs v_st = (stack_ass_sat St vs (var_st_set_global v_st n g)))"

definition stack_ass_ind_on_loc :: "'a stack_ass \<Rightarrow> nat \<Rightarrow> bool" where
  "stack_ass_ind_on_loc St n \<equiv>
     (\<forall>vs v_st l. stack_ass_sat St vs v_st = (stack_ass_sat St vs (var_st_set_local v_st n l)))"

definition stack_ass_ind_on :: "'a stack_ass \<Rightarrow> var \<Rightarrow> bool" where
  "stack_ass_ind_on H var \<equiv> case var of
                             Gl n \<Rightarrow> stack_ass_ind_on_glob H n
                           | Lc n \<Rightarrow> stack_ass_ind_on_loc H n
                           | Lv n \<Rightarrow> True"

definition heap_ass_ind_on_glob :: "'a heap_ass \<Rightarrow> nat \<Rightarrow> bool" where
  "heap_ass_ind_on_glob H n \<equiv>
     (\<forall>h v_st g. H h v_st = (H h (var_st_set_global v_st n g)))"

definition heap_ass_ind_on_loc :: "'a heap_ass \<Rightarrow> nat \<Rightarrow> bool" where
  "heap_ass_ind_on_loc H n \<equiv>
     (\<forall>h v_st l. H h v_st = (H h (var_st_set_local v_st n l)))"

definition heap_ass_ind_on :: "'a heap_ass \<Rightarrow> var \<Rightarrow> bool" where
  "heap_ass_ind_on H var \<equiv> case var of
                             Gl n \<Rightarrow> heap_ass_ind_on_glob H n
                           | Lc n \<Rightarrow> heap_ass_ind_on_loc H n
                           | Lv n \<Rightarrow> True"

fun modset_b_e :: "b_e \<Rightarrow> var set"
and modsets_b_e :: "b_e list \<Rightarrow> var set" where
  "modsets_b_e es = fold (\<lambda>e vs. (modset_b_e e) \<union> vs) es {}"
| "modset_b_e (Set_local i) = {Lc i}"
| "modset_b_e (Tee_local i) = {Lc i}"
| "modset_b_e (Set_global i) = {Gl i}"
| "modset_b_e (Block _ b_es) = modsets_b_e b_es"
| "modset_b_e (Loop _ b_es) = modsets_b_e b_es"
| "modset_b_e (If _ b_es1 b_es2) = modsets_b_e b_es1 \<union> modsets_b_e b_es2"
| "modset_b_e _ = {}"

fun modset :: "e \<Rightarrow> var set"
and modsets:: "e list \<Rightarrow> var set" where
  "modsets es = fold (\<lambda>e vs. (modset e) \<union> vs) es {}"
| "modset ($ b_e) = modset_b_e b_e"
| "modset (Label n les es) = modsets les \<union> modsets es"
| "modset (Local n i lvs es) = modsets es"
| "modset _ = {}"

context encapsulated_module
begin

definition pred_option_Some :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool" where
  "pred_option_Some pred opt \<equiv> opt \<noteq> None \<and> pred_option pred opt"

(* separating conjuction *)
definition sep_conj :: "'a heap_ass \<Rightarrow> 'a heap_ass \<Rightarrow> 'a heap_ass" (infixr "\<^emph>" 60) where
  "ha' \<^emph> ha'' \<equiv> \<lambda>h st. \<exists>h' h''. heap_disj h' h'' \<and> ha' h' st \<and> ha'' h'' st \<and> heap_merge h' h'' = h"

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
| Frame:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} es {St' \<^sub>s|\<^sub>h H'}; (\<forall>v \<in> modsets es. heap_ass_ind_on Hf v)\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h (H \<^emph> Hf)} es {St' \<^sub>s|\<^sub>h (H' \<^emph> Hf)}"
| Ext:"\<lbrakk>\<Gamma>\<bullet>assms \<turnstile> {St \<^sub>s|\<^sub>h H} es {St' \<^sub>s|\<^sub>h H'}; (\<forall>v \<in> modsets es. stack_ass_ind_on Stf v)\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {(Stf @ St) \<^sub>s|\<^sub>h H} es {(Stf @ St') \<^sub>s|\<^sub>h H'}"
| Call:"\<lbrakk>(fs,[],None)\<bullet>specs \<tturnstile> ({(P,c,Q). \<exists>i. (P, [$Call i], Q) \<in> specs \<and> i< length fs \<and> c = [Callcl (fs!i)]}); \<forall>(P,c,Q) \<in> specs. \<exists>i. c = [$Call i] \<and> i < length fs\<rbrakk> \<Longrightarrow> (fs,[],None)\<bullet>({}) \<tturnstile> specs"
| ConjI:"\<forall>(P,es,Q) \<in> specs. (\<Gamma>\<bullet>assms \<turnstile> {P} es {Q}) \<Longrightarrow> \<Gamma>\<bullet>assms \<tturnstile> specs"
| ConjE:"\<lbrakk>\<Gamma>\<bullet>assms \<tturnstile> specs; (P,es,Q) \<in> specs\<rbrakk> \<Longrightarrow> \<Gamma>\<bullet>assms \<turnstile> {P} es {Q}"

lemma treeee: assumes "AA \<Longrightarrow> (BB = CC)"
  shows "(AA \<and> BB) = (AA \<and> CC)"
  using assms
  by metis

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
  thus ?case
    by (metis valid_triple_defs(5) valid_triples_assms_n_def singletonD)
next
  case (Seq \<Gamma> assms P es Q es' R)
  then show ?case sorry
next
  case (Conseq \<Gamma> assms P' es Q' P Q)
  thus ?case
    using valid_triple_assms_n_conseq
    by blast
next
  case (Frame \<Gamma> assms St H es St' H' Hf)
  thus ?case
    sorry
next
  case (Ext \<Gamma> assms St H es St' H' Stf)
  thus ?case
    sorry
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
      then have "res_wf (fs, []::'a ass list, None::'a ass option) res locs' s' (ae, bc) vcsf b"
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
      using Suc(3)[of n] valid_triples_n_emp
      unfolding valid_triples_assms_n_def
      by blast
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
theory Wasm_Assertions_Shallow imports "Wasm_Big_Step" begin

typedef lvar = "UNIV :: (nat) set" ..

(* global, local, logical variables*)
datatype var = Gl nat | Lc nat | Lv lvar

datatype 'a lvar_v = V_p v | V_a 'a

(* variable store *)
(* global, local, logical variables*)
type_synonym 'a var_st = "global list \<times> v list \<times> (lvar, 'a lvar_v) map"

definition var_st_get_local :: "'a var_st \<Rightarrow> nat \<Rightarrow> v option" where
  "var_st_get_local st n \<equiv> let st_l = (fst (snd st)) in
                            (if (n < length st_l)
                            then Some (st_l!n)
                            else None)"

definition var_st_get_global :: "'a var_st \<Rightarrow> nat \<Rightarrow> global option" where
  "var_st_get_global st n \<equiv> let st_g = (fst st) in
                            (if (n < length st_g)
                            then Some (st_g!n)
                            else None)"

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

(* local variable reification *)
definition reifies_loc :: "[v list, 'a var_st] \<Rightarrow> bool" where
  "reifies_loc locs st \<equiv> (fst (snd st)) = locs"

(* global variable reification (with respect to a partial instance) *)
definition reifies_glob :: "[global list, nat list, 'a var_st] \<Rightarrow> bool" where
  "reifies_glob gs igs st \<equiv>
     let st_g = (fst st) in
     \<forall>gn < length st_g.
       gn < (length igs) \<and> igs!gn < (length gs) \<and> st_g!gn = (gs!(igs!gn))"

(* function reification (with respect to a partial instance) *)
definition reifies_func :: "[cl list, nat list, cl list] \<Rightarrow> bool" where
  "reifies_func cls icls fs \<equiv> list_all2 (\<lambda>icl f. icl < (length cls) \<and> cls!icl = f) icls fs"

(* heap reification relations *)
definition reifies_heap_contents :: "[mem, ((nat, byte) map)] \<Rightarrow> bool" where
  "reifies_heap_contents m byte_m \<equiv>
     \<forall>ind \<in> (dom byte_m). ind < mem_length m \<and> byte_m(ind) = Some (byte_at m ind)"

definition reifies_heap_length :: "[mem, nat option] \<Rightarrow> bool" where
  "reifies_heap_length m l_opt \<equiv> pred_option (\<lambda>l. mem_size m = l) l_opt"

definition reifies_heap :: "[mem list, nat option, heap] \<Rightarrow> bool" where
  "reifies_heap ms im_opt h \<equiv> let im = the im_opt in
                               im < length ms
                             \<and> reifies_heap_contents (ms!im) (fst h)
                             \<and> reifies_heap_length (ms!im) (snd h)"

(* store reification relation *)
definition reifies_s :: "[s, inst, heap, 'a var_st, cl list] \<Rightarrow> bool" where
  "reifies_s s i h st fs \<equiv> reifies_glob (globs s) (inst.globs i) st
                         \<and> reifies_func (funcs s) (inst.funcs i) fs
                         \<and> reifies_heap (mem s) (inst.mem i) h"

(* shallow embedding of assertions *)
type_synonym 'a stack_ass = "(v \<Rightarrow> 'a var_st \<Rightarrow> bool) list"
type_synonym 'a heap_ass = "heap \<Rightarrow> 'a var_st \<Rightarrow> bool"

datatype 'a ass = Ass "'a stack_ass" "'a heap_ass" (infix "\<^sub>s|\<^sub>h" 60) | Ex_ass lvar "'a ass" 

type_synonym 'a triple = "'a ass \<times> e list \<times> 'a ass"

(* function list, assms, label ass, return ass *)
type_synonym 'a triple_context = "cl list \<times> 'a ass list \<times> 'a ass"

definition add_label_ass :: "'a triple_context \<Rightarrow> 'a ass \<Rightarrow> 'a triple_context" where
  "add_label_ass \<Gamma> l \<equiv> let (fs, labs, ret) = \<Gamma> in (fs, l#labs, ret)"

fun ass_sat :: "'a ass \<Rightarrow> v list \<Rightarrow> heap \<Rightarrow> 'a var_st \<Rightarrow> bool" where
  "ass_sat (St \<^sub>s|\<^sub>h H) ves h st = (list_all2 (\<lambda>Si v. Si v st) St ves \<and> H h st)"
| "ass_sat (Ex_ass lv P) ves h st = (\<exists>v. ass_sat P ves h (var_st_set_lvar st lv v))"

fun ass_stack_len :: "'a ass \<Rightarrow> nat" where
  "ass_stack_len (St \<^sub>s|\<^sub>h H) = length St"
| "ass_stack_len (Ex_ass lv P) = ass_stack_len P"

(* label reification relation *)
definition reifies_lab :: "nat list \<Rightarrow> 'a triple_context \<Rightarrow> bool" where
  "reifies_lab lns \<Gamma> \<equiv> lns = map ass_stack_len (fst (snd \<Gamma>))"

(* label reification relation *)
definition reifies_ret :: "nat \<Rightarrow> 'a triple_context \<Rightarrow> bool" where
  "reifies_ret rn \<Gamma> \<equiv> rn = ass_stack_len (snd (snd \<Gamma>))"

(* TODO: frame? ? ? ?*)
definition valid_triple :: "'a triple_context \<Rightarrow> 'a ass \<Rightarrow> e list \<Rightarrow> 'a ass \<Rightarrow> bool" ("_ \<Turnstile> {_}_{_}" 60) where
  "(\<Gamma> \<Turnstile> {P}es{Q}) \<equiv> let (fs,lasss,rass) = \<Gamma> in
                     \<forall>vcs h st s i locs labs ret lvar_st.
                                        ass_sat P vcs h st
                                      \<and> reifies_s s i h st fs
                                      \<and> reifies_loc locs st
                                      \<and> reifies_lab labs \<Gamma>
                                      \<and> reifies_ret ret \<Gamma>
                                      \<and> snd (snd st) = lvar_st \<longrightarrow>
                                      (\<forall>s' locs' res. ((s,locs,($$*vcs)@es) \<Down>{(labs,ret,i)} (s',locs', res)) \<longrightarrow>
                                      (case res of
                                         RTrap \<Rightarrow> False
                                       | RValue rvs \<Rightarrow> \<exists>h' vcs' st'.
                                                               ass_sat Q vcs' h' st'
                                                               \<and> rvs = vcs'
                                                               \<and> reifies_s s' i h' st' fs
                                                               \<and> reifies_loc locs' st'
                                       | RBreak n rvs \<Rightarrow> \<exists>h' vcs' st'.
                                                               n < length lasss
                                                               \<and> ass_sat (lasss!n) vcs' h' st'
                                                               \<and> rvs = vcs'
                                                               \<and> reifies_s s' i h' st' fs
                                                               \<and> reifies_loc locs' st'
                                       | RReturn rvs \<Rightarrow> \<exists>h' vcs' st'.
                                                               ass_sat rass vcs' h' st'
                                                               \<and> rvs = vcs'
                                                               \<and> reifies_s s' i h' st' fs
                                                               \<and> reifies_loc locs' st'))"

definition valid_triples :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_ \<TTurnstile> _" 60) where
  "\<Gamma> \<TTurnstile> specs \<equiv> \<forall>(P,es,Q) \<in> specs. (\<Gamma> \<Turnstile> {P}es{Q})"

(* TODO: frame? ? ? ?*)
definition valid_triple_n :: "'a triple_context \<Rightarrow> nat \<Rightarrow> 'a ass \<Rightarrow> e list \<Rightarrow> 'a ass \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>_ {_}_{_}" 60) where
  "(\<Gamma> \<Turnstile>\<^sub>k {P}es{Q}) \<equiv> let (fs,lasss,rass) = \<Gamma> in
                     \<forall>vcs h st s i locs labs ret lvar_st.
                                        ass_sat P vcs h st
                                      \<and> reifies_s s i h st fs
                                      \<and> reifies_loc locs st
                                      \<and> reifies_lab labs \<Gamma>
                                      \<and> reifies_ret ret \<Gamma>
                                      \<and> snd (snd st) = lvar_st \<longrightarrow>
                                      (\<forall>s' locs' res. ((s,locs,($$*vcs)@es)\<Down>k{(labs,ret,i)} (s',locs', res)) \<longrightarrow>
                                      (case res of
                                         RTrap \<Rightarrow> False
                                       | RValue rvs \<Rightarrow> \<exists>h' vcs' st'.
                                                               ass_sat Q vcs' h' st'
                                                               \<and> rvs = vcs'
                                                               \<and> reifies_s s' i h' st' fs
                                                               \<and> reifies_loc locs' st'
                                                               \<and> snd (snd st') = lvar_st
                                       | RBreak n rvs \<Rightarrow> \<exists>h' vcs' st'.
                                                               n < length lasss
                                                               \<and> ass_sat (lasss!n) vcs' h' st'
                                                               \<and> rvs = vcs'
                                                               \<and> reifies_s s' i h' st' fs
                                                               \<and> reifies_loc locs' st'
                                                               \<and> snd (snd st') = lvar_st
                                       | RReturn rvs \<Rightarrow> \<exists>h' vcs' st'.
                                                               ass_sat rass vcs' h' st'
                                                               \<and> rvs = vcs'
                                                               \<and> reifies_s s' i h' st' fs
                                                               \<and> reifies_loc locs' st'
                                                               \<and> snd (snd st') = lvar_st))"

definition valid_triples_n :: "'a triple_context \<Rightarrow> nat \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_ \<TTurnstile>\<^sub>_ _" 60) where
  "(\<Gamma> \<TTurnstile>\<^sub>n specs) \<equiv> \<forall>(P,es,Q) \<in> specs. (\<Gamma> \<Turnstile>\<^sub>n {P}es{Q})"

definition cvalids :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_\<bullet>_ \<TTurnstile> _" 60) where
  "(\<Gamma>\<bullet>assms \<TTurnstile> specs) \<equiv> (\<Gamma> \<TTurnstile> assms) \<longrightarrow> (\<Gamma> \<TTurnstile> specs)"

definition cvalids_n :: "'a triple_context \<Rightarrow> 'a triple set \<Rightarrow> nat \<Rightarrow> 'a triple set \<Rightarrow> bool" ("_\<bullet>_ \<TTurnstile>\<^sub>_ _" 60) where
  "(\<Gamma>\<bullet>assms \<TTurnstile>\<^sub>n specs) \<equiv> (\<Gamma> \<TTurnstile>\<^sub>n assms) \<longrightarrow> (\<Gamma> \<TTurnstile>\<^sub>n specs)"

end
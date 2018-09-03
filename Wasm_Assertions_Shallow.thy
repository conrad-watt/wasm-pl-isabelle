theory Wasm_Assertions_Shallow imports "WebAssembly/Wasm_Base_Defs" begin

typedef lvar = "UNIV :: (nat) set" ..

(* global, local, logical variables*)
datatype var = Gl nat | Lc nat | Lv lvar

(* variable store *)
type_synonym var_st = "(var, v) map"

definition var_st_locals :: "var_st \<Rightarrow> nat set" where
  "var_st_locals st = {n. Lc n \<in> (dom st)}"

definition var_st_globals :: "var_st \<Rightarrow> nat set" where
  "var_st_globals st = {n. Gl n \<in> (dom st)}"

(* abstract heap with max length *)
type_synonym heap = "((nat, byte) map) \<times> (nat option)"

(* local variable reification *)
definition reifies_loc :: "[v list, var_st] \<Rightarrow> bool" where
  "reifies_loc locs st \<equiv> \<forall>ln \<in> var_st_locals st. ln < (length locs) \<and> st (Lc ln) = Some (locs!ln)"

(* global variable reification (with respect to a partial instance) *)
definition reifies_glob :: "[global list, nat list, var_st] \<Rightarrow> bool" where
  "reifies_glob gs igs st \<equiv>
     \<forall>gn \<in> var_st_globals st.
       gn < (length igs) \<and> igs!gn < (length gs) \<and> st (Gl gn) = Some (g_val (gs!(igs!gn)))"

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
definition reifies_s :: "[s, inst, heap, var_st, cl list] \<Rightarrow> bool" where
  "reifies_s s i h st fs \<equiv> reifies_glob (globs s) (inst.globs i) st
                         \<and> reifies_func (funcs s) (inst.funcs i) fs
                         \<and> reifies_heap (mem s) (inst.mem i) h"
end
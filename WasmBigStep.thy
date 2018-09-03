theory WasmBigStep imports "WebAssembly/Wasm" begin

datatype res_b =
  RValue "v list" 
| RBreak nat "v list"
| RReturn "v list"
| RTrap

inductive reduce_to :: "[(s \<times> v list \<times> e list), (nat list \<times> nat \<times> inst), (s \<times> v list \<times> res_b)] \<Rightarrow> bool" ("_ \<Down>{_} _" 60) where
  \<comment> \<open>\<open>constant values\<close>\<close>
  const:"(s,vs,[$C v]) \<Down>{\<Gamma>} (s,vs,RValue [v])"
  \<comment> \<open>\<open>unary ops\<close>\<close>
| unop:"(s,vs,[$C v, $(Unop t op)]) \<Down>{\<Gamma>} (s,vs,RValue [(app_unop op v)])"
  \<comment> \<open>\<open>binary ops\<close>\<close>
| binop_Some:"\<lbrakk>app_binop op v1 v2 = (Some v)\<rbrakk> \<Longrightarrow> (s,vs,[$C v1, $C v2, $(Binop t op)]) \<Down>{\<Gamma>} (s,vs,RValue [v])"
| binop_None:"\<lbrakk>app_binop op v1 v2 = None\<rbrakk> \<Longrightarrow> (s,vs,[$C v1, $C v2, $(Binop t op)]) \<Down>{\<Gamma>} (s,vs,RTrap)"
  \<comment> \<open>\<open>testops\<close>\<close>
| testop:"(s,vs,[$C v, $(Testop t op)]) \<Down>{\<Gamma>} (s,vs,RValue [(app_testop op v)])"
  \<comment> \<open>\<open>relops\<close>\<close>
| relop:"(s,vs,[$C v1, $C v2, $(Relop t op)]) \<Down>{\<Gamma>} (s,vs,RValue [(app_relop op v1 v2)])"
  \<comment> \<open>\<open>convert\<close>\<close>
| convert_Some:"\<lbrakk>types_agree t1 v; cvt t2 sx v = (Some v')\<rbrakk> \<Longrightarrow> (s,vs,[$(C v), $(Cvtop t2 Convert t1 sx)]) \<Down>{\<Gamma>} (s,vs,RValue [v'])"
| convert_None:"\<lbrakk>types_agree t1 v; cvt t2 sx v = None\<rbrakk> \<Longrightarrow> (s,vs,[$(C v), $(Cvtop t2 Convert t1 sx)]) \<Down>{\<Gamma>} (s,vs,RTrap)"
  \<comment> \<open>\<open>reinterpret\<close>\<close>
| reinterpret:"types_agree t1 v \<Longrightarrow> (s,vs,[$(C v), $(Cvtop t2 Reinterpret t1 None)]) \<Down>{\<Gamma>} (s,vs,RValue [(wasm_deserialise (bits v) t2)])"
  \<comment> \<open>\<open>unreachable\<close>\<close>
| unreachable:"(s,vs,[$ Unreachable]) \<Down>{\<Gamma>} (s,vs,RTrap)"
  \<comment> \<open>\<open>nop\<close>\<close>
| nop:"(s,vs,[$ Nop]) \<Down>{\<Gamma>} (s,vs,RValue [])"
  \<comment> \<open>\<open>drop\<close>\<close>
| drop:"(s,vs,[$(C v), ($ Drop)]) \<Down>{\<Gamma>} (s,vs,RValue [])"
  \<comment> \<open>\<open>select\<close>\<close>
| select_false:"int_eq n 0 \<Longrightarrow> (s,vs,[$(C v1), $(C v2), $C (ConstInt32 n), ($ Select)]) \<Down>{\<Gamma>} (s,vs, RValue [v2])"
| select_true:"int_ne n 0 \<Longrightarrow> (s,vs,[$(C v1), $(C v2), $C (ConstInt32 n), ($ Select)]) \<Down>{\<Gamma>} (s,vs,RValue [v1])"
  \<comment> \<open>\<open>block\<close>\<close>
| block:"\<lbrakk>const_list ves; length ves = n; length t1s = n; length t2s = m; (s,vs,[Label m [] (ves @ ($* es))]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [$(Block (t1s _> t2s) es)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>loop\<close>\<close>
| loop:"\<lbrakk>const_list ves; length ves = n; length t1s = n; length t2s = m; (s,vs,[Label n [] (ves @ ($* es))]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [$(Loop (t1s _> t2s) es)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>if\<close>\<close>
| if_false:"\<lbrakk>int_eq n 0; const_list ves; (s,vs,ves@[$(Block tf e2s)]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>{\<Gamma>} (s',vs',res)"
| if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Block tf e1s)]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>length vcs = n; k < length ls; ls!k = n\<rbrakk> \<Longrightarrow> (s,vs,(($$*vcs) @ [$(Br k)])) \<Down>{(ls,r,i)} (s,vs,RBreak k vcs)"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if_false:"int_eq n 0 \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Br_if k)]) \<Down>{\<Gamma>} (s,vs,RValue [])"
| br_if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Br k)]) \<Down>{\<Gamma>} (s',vs',res) \<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(Br_if k)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>length ks > (nat_of_int c); const_list ves; (s,vs,ves@[$(Br (ks!(nat_of_int c)))]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table ks k)]) \<Down>{\<Gamma>} (s',vs',res)"
| br_table_length:"\<lbrakk>length ks \<le> (nat_of_int c); const_list ves; (s,vs,ves@[$(Br k)]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table ks k)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>length vs = r\<rbrakk>  \<Longrightarrow> (s,vs,($$*vcs) @ [$Return]) \<Down>{(ls,r,i)} (s',vs',RReturn vcs)"
  \<comment> \<open>\<open>get_local\<close>\<close>
| get_local:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> (s,(vi @ [v] @ vs),[$(Get_local j)]) \<Down>{\<Gamma>} (s,(vi @ [v] @ vs),RValue [v])"
  \<comment> \<open>\<open>set_local\<close>\<close>
| set_local:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> (s,(vi @ [v] @ vs),[$(C v'), $(Set_local j)]) \<Down>{\<Gamma>} (s,(vi @ [v'] @ vs),RValue [])"
  \<comment> \<open>\<open>tee_local\<close>\<close>
| tee_local:"\<lbrakk>is_const v; (s,vs,[v, v, $(Set_local i)]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,[v, $(Tee_local i)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>get_global\<close>\<close>
| get_global:"(s,vs,[$(Get_global j)]) \<Down>{(ls,r,i)} (s,vs,RValue [(sglob_val s i j)])"
  \<comment> \<open>\<open>set_global\<close>\<close>
| set_global:"supdate_glob s i j v = s' \<Longrightarrow> (s,vs,[$(C v), $(Set_global j)]) \<Down>{(ls,r,i)} (s',vs,RValue [])"
  \<comment> \<open>\<open>load\<close>\<close>
| load_Some:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load m (nat_of_int k) off (t_length t) = Some bs\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $(Load t None a off)]) \<Down>{(ls,r,i)} (s,vs,RValue [(wasm_deserialise bs t)])"
| load_None:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load m (nat_of_int k) off (t_length t) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $(Load t None a off)]) \<Down>{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>load packed\<close>\<close>
| load_packed_Some:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load_packed sx m (nat_of_int k) off (tp_length tp) (t_length t) = Some bs\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]) \<Down>{(ls,r,i)} (s,vs,RValue [(wasm_deserialise bs t)])"
| load_packed_None:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load_packed sx m (nat_of_int k) off (tp_length tp) (t_length t) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $(Load t (Some (tp, sx)) a off)]) \<Down>{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>store\<close>\<close>
| store_Some:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store m (nat_of_int k) off (bits v) (t_length t) = Some mem'\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $C v, $(Store t None a off)]) \<Down>{(ls,r,i)} (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>,vs,RValue [])"
| store_None:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store m (nat_of_int k) off (bits v) (t_length t) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $C v, $(Store t None a off)]) \<Down>{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>store packed\<close>\<close> (* take only (tp_length tp) lower order bytes *)
| store_packed_Some:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store_packed m (nat_of_int k) off (bits v) (tp_length tp) = Some mem'\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $C v, $(Store t (Some tp) a off)]) \<Down>{(ls,r,i)} (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>,vs,RValue [])"
| store_packed_None:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store_packed m (nat_of_int k) off (bits v) (tp_length tp) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 k), $C v, $(Store t (Some tp) a off)]) \<Down>{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>current_memory\<close>\<close>
| current_memory:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> (s,vs,[ $(Current_memory)]) \<Down>{(ls,r,i)} (s,vs,RValue [(ConstInt32 (int_of_nat n))])"
  \<comment> \<open>\<open>grow_memory\<close>\<close>
| grow_memory:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n; mem_grow m (nat_of_int c) = mem'\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 c), $(Grow_memory)]) \<Down>{(ls,r,i)} (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>,vs, RValue [(ConstInt32 (int_of_nat n))])"
  \<comment> \<open>\<open>grow_memory fail\<close>\<close>
| grow_memory_fail:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 c),$(Grow_memory)]) \<Down>{(ls,r,i)} (s,vs,RValue [(ConstInt32 int32_minus_one)])"
  \<comment> \<open>\<open>call\<close>\<close>
| call:"\<lbrakk>const_list ves; (s,vs,ves@[Callcl (sfunc s i j)]) \<Down>{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$(Call j)]) \<Down>{(ls,r,i)} (s',vs',res)"
  \<comment> \<open>\<open>call_indirect\<close>\<close>
| call_indirect_Some:"\<lbrakk>stab s i (nat_of_int c) = Some cl; stypes s i j = tf; cl_type cl = tf; const_list ves; (s,vs,ves@[Callcl cl]) \<Down>{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Call_indirect j)]) \<Down>{(ls,r,i)} (s',vs',res)"
| call_indirect_None:"\<lbrakk>(stab s i (nat_of_int c) = Some cl \<and> stypes s i j \<noteq> cl_type cl) \<or> stab s i (nat_of_int c) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 c), $(Call_indirect j)]) \<Down>{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>call\<close>\<close>
| callcl_native:"\<lbrakk>cl = Func_native j (t1s _> t2s) ts es; ves = ($$* vcs); length vcs = n; length ts = k; length t1s = n; length t2s = m; (n_zeros ts = zs); (s,vs,[Local m j (vcs@zs) [$(Block ([] _> t2s) es)]]) \<Down>{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [Callcl cl]) \<Down>{(ls,r,i)} (s',vs',res)"
| callcl_host_Some:"\<lbrakk>cl = Func_host (t1s _> t2s) f; ves = ($$* vcs); length vcs = n; length t1s = n; length t2s = m; host_apply s (t1s _> t2s) f vcs hs = Some (s', vcs')\<rbrakk> \<Longrightarrow> (s,vs,ves @ [Callcl cl]) \<Down>{(ls,r,i)} (s',vs,RValue vcs')"
| callcl_host_None:"\<lbrakk>cl = Func_host (t1s _> t2s) f; ves = ($$* vcs); length vcs = n; length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> (s,vs,ves @ [Callcl cl]) \<Down>{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>value congruence\<close>\<close>
| seq_value:"\<lbrakk>(s,vs,es) \<Down>{\<Gamma>} (s'',vs'',RValue res''); (s'',vs'',($$* res'') @ es') \<Down>{\<Gamma>} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,es @ es') \<Down>{\<Gamma>} (s',vs',RValue res)"
| label_value:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RValue res)"
| local_value:"\<lbrakk>(s,lls,es) \<Down>{([],n,j)} (s',lls',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RValue res)"
  \<comment> \<open>\<open>trap congruence\<close>\<close>
| seq_trap:"\<lbrakk>const_list ves; (s,vs,es) \<Down>{\<Gamma>} (s',vs',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,ves @ es @ es') \<Down>{\<Gamma>} (s',vs',RTrap)"
| label_trap:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RTrap)"
| local_trap:"\<lbrakk>(s,lls,es) \<Down>{([],n,j)} (s',lls',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RTrap)"
  \<comment> \<open>\<open>break congruence\<close>\<close>
| seq_break:"\<lbrakk>const_list ves; (s,vs,es) \<Down>{\<Gamma>} (s',vs',RBreak n bvs)\<rbrakk> \<Longrightarrow> (s,vs,ves @ es @ es') \<Down>{\<Gamma>} (s',vs',RBreak n bvs)"
| label_break_suc:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RBreak (Suc bn) bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RBreak bn bvs)"
| label_break_nil:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RBreak 0 bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RValue bvs)"
  \<comment> \<open>\<open>return congruence\<close>\<close>
| seq_return:"\<lbrakk>const_list ves; (s,vs,es) \<Down>{\<Gamma>} (s',vs',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,ves @ es @ es') \<Down>{\<Gamma>} (s',vs',RReturn rvs)"
| label_return:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RReturn rvs)"
| local_return:"\<lbrakk>(s,lls,es) \<Down>{([],n,j)} (s',lls',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RValue rvs)"

end
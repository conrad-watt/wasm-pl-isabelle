theory Wasm_Big_Step imports "WebAssembly/Wasm_Properties" begin

datatype res_b =
  RValue "v list" 
| RBreak nat "v list"
| RReturn "v list"
| RTrap

inductive reduce_to :: "[(s \<times> v list \<times> e list), (nat list \<times> nat option \<times> inst), (s \<times> v list \<times> res_b)] \<Rightarrow> bool" ("_ \<Down>{_} _" 60) where
  \<comment> \<open>\<open>constant values\<close>\<close>
  emp:"(s,vs,[]) \<Down>{\<Gamma>} (s,vs,RValue [])"
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
| loop:"\<lbrakk>const_list ves; length ves = n; length t1s = n; length t2s = m; (s,vs,[Label n [$(Loop (t1s _> t2s) es)] (ves @ ($* es))]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [$(Loop (t1s _> t2s) es)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>if\<close>\<close>
| if_false:"\<lbrakk>int_eq n 0; const_list ves; (s,vs,ves@[$(Block tf e2s)]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>{\<Gamma>} (s',vs',res)"
| if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Block tf e1s)]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>length vcs = n; ls!k = n\<rbrakk> \<Longrightarrow> (s,vs,(($$*vcs) @ [$(Br k)])) \<Down>{(ls,r,i)} (s,vs,RBreak k vcs)"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if_false:"int_eq n 0 \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Br_if k)]) \<Down>{\<Gamma>} (s,vs,RValue [])"
| br_if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Br k)]) \<Down>{\<Gamma>} (s',vs',res) \<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(Br_if k)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>length ks > (nat_of_int c); const_list ves; (s,vs,ves@[$(Br (ks!(nat_of_int c)))]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table ks k)]) \<Down>{\<Gamma>} (s',vs',res)"
| br_table_length:"\<lbrakk>length ks \<le> (nat_of_int c); const_list ves; (s,vs,ves@[$(Br k)]) \<Down>{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table ks k)]) \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>length vs = r\<rbrakk>  \<Longrightarrow> (s,vs,($$*vcs) @ [$Return]) \<Down>{(ls,Some r,i)} (s,vs,RReturn vcs)"
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
| const_value:"\<lbrakk>(s,vs,es) \<Down>{\<Gamma>} (s',vs',RValue res); ves \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,($$*ves)@es) \<Down>{\<Gamma>} (s',vs',RValue (ves@res))"
| label_value:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RValue res)"
| local_value:"\<lbrakk>(s,lls,es) \<Down>{([],Some n,j)} (s',lls',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RValue res)"
  \<comment> \<open>\<open>seq congruence\<close>\<close>
| seq_value:"\<lbrakk>(s,vs,es) \<Down>{\<Gamma>} (s'',vs'',RValue res''); (s'',vs'',($$* res'') @ es') \<Down>{\<Gamma>} (s',vs',res); \<not> const_list es; es' \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,es @ es') \<Down>{\<Gamma>} (s',vs',res)"
| seq_nonvalue1:"\<lbrakk>const_list ves; (s,vs,es) \<Down>{\<Gamma>} (s',vs',res); \<nexists>rvs. res = RValue rvs; ves \<noteq> []; es \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,ves @ es) \<Down>{\<Gamma>} (s',vs',res)"
| seq_nonvalue2:"\<lbrakk>(s,vs,es) \<Down>{\<Gamma>} (s',vs',res); \<nexists>rvs. res = RValue rvs; es' \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,es @ es') \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>trap congruence\<close>\<close>
| label_trap:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RTrap)"
| local_trap:"\<lbrakk>(s,lls,es) \<Down>{([],Some n,j)} (s',lls',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RTrap)"
  \<comment> \<open>\<open>break congruence\<close>\<close>
| label_break_suc:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RBreak (Suc bn) bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RBreak bn bvs)"
| label_break_nil:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s'',vs'',RBreak 0 bvs); (s'',vs'',($$* bvs) @ les) \<Down>{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',res)"
  \<comment> \<open>\<open>return congruence\<close>\<close>
| label_return:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RReturn rvs)"
| local_return:"\<lbrakk>(s,lls,es) \<Down>{([],Some n,j)} (s',lls',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RValue rvs)"

inductive reduce_to_n :: "[(s \<times> v list \<times> e list), nat, (nat list \<times> nat option \<times> inst), (s \<times> v list \<times> res_b)] \<Rightarrow> bool" ("_ \<Down>_{_} _" 60) where
  \<comment> \<open>\<open>constant values\<close>\<close>
  emp:"(s,vs,[]) \<Down>k{\<Gamma>} (s,vs,RValue [])"
  \<comment> \<open>\<open>unary ops\<close>\<close>
| unop:"(s,vs,[$C v, $(Unop t op)]) \<Down>k{\<Gamma>} (s,vs,RValue [(app_unop op v)])"
  \<comment> \<open>\<open>binary ops\<close>\<close>
| binop_Some:"\<lbrakk>app_binop op v1 v2 = (Some v)\<rbrakk> \<Longrightarrow> (s,vs,[$C v1, $C v2, $(Binop t op)]) \<Down>k{\<Gamma>} (s,vs,RValue [v])"
| binop_None:"\<lbrakk>app_binop op v1 v2 = None\<rbrakk> \<Longrightarrow> (s,vs,[$C v1, $C v2, $(Binop t op)]) \<Down>k{\<Gamma>} (s,vs,RTrap)"
  \<comment> \<open>\<open>testops\<close>\<close>
| testop:"(s,vs,[$C v, $(Testop t op)]) \<Down>k{\<Gamma>} (s,vs,RValue [(app_testop op v)])"
  \<comment> \<open>\<open>relops\<close>\<close>
| relop:"(s,vs,[$C v1, $C v2, $(Relop t op)]) \<Down>k{\<Gamma>} (s,vs,RValue [(app_relop op v1 v2)])"
  \<comment> \<open>\<open>convert\<close>\<close>
| convert_Some:"\<lbrakk>types_agree t1 v; cvt t2 sx v = (Some v')\<rbrakk> \<Longrightarrow> (s,vs,[$(C v), $(Cvtop t2 Convert t1 sx)]) \<Down>k{\<Gamma>} (s,vs,RValue [v'])"
| convert_None:"\<lbrakk>types_agree t1 v; cvt t2 sx v = None\<rbrakk> \<Longrightarrow> (s,vs,[$(C v), $(Cvtop t2 Convert t1 sx)]) \<Down>k{\<Gamma>} (s,vs,RTrap)"
  \<comment> \<open>\<open>reinterpret\<close>\<close>
| reinterpret:"types_agree t1 v \<Longrightarrow> (s,vs,[$(C v), $(Cvtop t2 Reinterpret t1 None)]) \<Down>k{\<Gamma>} (s,vs,RValue [(wasm_deserialise (bits v) t2)])"
  \<comment> \<open>\<open>unreachable\<close>\<close>
| unreachable:"(s,vs,[$ Unreachable]) \<Down>k{\<Gamma>} (s,vs,RTrap)"
  \<comment> \<open>\<open>nop\<close>\<close>
| nop:"(s,vs,[$ Nop]) \<Down>k{\<Gamma>} (s,vs,RValue [])"
  \<comment> \<open>\<open>drop\<close>\<close>
| drop:"(s,vs,[$(C v), ($ Drop)]) \<Down>k{\<Gamma>} (s,vs,RValue [])"
  \<comment> \<open>\<open>select\<close>\<close>
| select_false:"int_eq n 0 \<Longrightarrow> (s,vs,[$(C v1), $(C v2), $C (ConstInt32 n), ($ Select)]) \<Down>k{\<Gamma>} (s,vs, RValue [v2])"
| select_true:"int_ne n 0 \<Longrightarrow> (s,vs,[$(C v1), $(C v2), $C (ConstInt32 n), ($ Select)]) \<Down>k{\<Gamma>} (s,vs,RValue [v1])"
  \<comment> \<open>\<open>block\<close>\<close>
| block:"\<lbrakk>const_list ves; length ves = n; length t1s = n; length t2s = m; (s,vs,[Label m [] (ves @ ($* es))]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [$(Block (t1s _> t2s) es)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>loop\<close>\<close>
| loop:"\<lbrakk>const_list ves; length ves = n; length t1s = n; length t2s = m; (s,vs,[Label n [$(Loop (t1s _> t2s) es)] (ves @ ($* es))]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [$(Loop (t1s _> t2s) es)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>if\<close>\<close>
| if_false:"\<lbrakk>int_eq n 0; const_list ves; (s,vs,ves@[$(Block tf e2s)]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>k{\<Gamma>} (s',vs',res)"
| if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Block tf e1s)]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>length vcs = n; ls!j = n\<rbrakk> \<Longrightarrow> (s,vs,(($$*vcs) @ [$(Br j)])) \<Down>k{(ls,r,i)} (s,vs,RBreak j vcs)"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if_false:"int_eq n 0 \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Br_if j)]) \<Down>k{\<Gamma>} (s,vs,RValue [])"
| br_if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Br j)]) \<Down>k{\<Gamma>} (s',vs',res) \<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(Br_if j)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>length js > (nat_of_int c); const_list ves; (s,vs,ves@[$(Br (js!(nat_of_int c)))]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table js j)]) \<Down>k{\<Gamma>} (s',vs',res)"
| br_table_length:"\<lbrakk>length js \<le> (nat_of_int c); const_list ves; (s,vs,ves@[$(Br j)]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table js j)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>length vs = r\<rbrakk>  \<Longrightarrow> (s,vs,($$*vcs) @ [$Return]) \<Down>k{(ls,Some r,i)} (s,vs,RReturn vcs)"
  \<comment> \<open>\<open>get_local\<close>\<close>
| get_local:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> (s,(vi @ [v] @ vs),[$(Get_local j)]) \<Down>k{\<Gamma>} (s,(vi @ [v] @ vs),RValue [v])"
  \<comment> \<open>\<open>set_local\<close>\<close>
| set_local:"\<lbrakk>length vi = j\<rbrakk> \<Longrightarrow> (s,(vi @ [v] @ vs),[$(C v'), $(Set_local j)]) \<Down>k{\<Gamma>} (s,(vi @ [v'] @ vs),RValue [])"
  \<comment> \<open>\<open>tee_local\<close>\<close>
| tee_local:"\<lbrakk>is_const v; (s,vs,[v, v, $(Set_local i)]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,[v, $(Tee_local i)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>get_global\<close>\<close>
| get_global:"(s,vs,[$(Get_global j)]) \<Down>k{(ls,r,i)} (s,vs,RValue [(sglob_val s i j)])"
  \<comment> \<open>\<open>set_global\<close>\<close>
| set_global:"supdate_glob s i j v = s' \<Longrightarrow> (s,vs,[$(C v), $(Set_global j)]) \<Down>k{(ls,r,i)} (s',vs,RValue [])"
  \<comment> \<open>\<open>load\<close>\<close>
| load_Some:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load m (nat_of_int n) off (t_length t) = Some bs\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Load t None a off)]) \<Down>k{(ls,r,i)} (s,vs,RValue [(wasm_deserialise bs t)])"
| load_None:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load m (nat_of_int n) off (t_length t) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Load t None a off)]) \<Down>k{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>load packed\<close>\<close>
| load_packed_Some:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load_packed sx m (nat_of_int n) off (tp_length tp) (t_length t) = Some bs\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Load t (Some (tp, sx)) a off)]) \<Down>k{(ls,r,i)} (s,vs,RValue [(wasm_deserialise bs t)])"
| load_packed_None:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; load_packed sx m (nat_of_int n) off (tp_length tp) (t_length t) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Load t (Some (tp, sx)) a off)]) \<Down>k{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>store\<close>\<close>
| store_Some:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store m (nat_of_int n) off (bits v) (t_length t) = Some mem'\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $C v, $(Store t None a off)]) \<Down>k{(ls,r,i)} (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>,vs,RValue [])"
| store_None:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store m (nat_of_int n) off (bits v) (t_length t) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $C v, $(Store t None a off)]) \<Down>k{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>store packed\<close>\<close> (* take only (tp_length tp) lower order bytes *)
| store_packed_Some:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store_packed m (nat_of_int n) off (bits v) (tp_length tp) = Some mem'\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $C v, $(Store t (Some tp) a off)]) \<Down>k{(ls,r,i)} (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>,vs,RValue [])"
| store_packed_None:"\<lbrakk>types_agree t v; smem_ind s i = Some j; ((mem s)!j) = m; store_packed m (nat_of_int n) off (bits v) (tp_length tp) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $C v, $(Store t (Some tp) a off)]) \<Down>k{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>current_memory\<close>\<close>
| current_memory:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> (s,vs,[ $(Current_memory)]) \<Down>k{(ls,r,i)} (s,vs,RValue [(ConstInt32 (int_of_nat n))])"
  \<comment> \<open>\<open>grow_memory\<close>\<close>
| grow_memory:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n; mem_grow m (nat_of_int c) = mem'\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 c), $(Grow_memory)]) \<Down>k{(ls,r,i)} (s\<lparr>mem:= ((mem s)[j := mem'])\<rparr>,vs, RValue [(ConstInt32 (int_of_nat n))])"
  \<comment> \<open>\<open>grow_memory fail\<close>\<close>
| grow_memory_fail:"\<lbrakk>smem_ind s i = Some j; ((mem s)!j) = m; mem_size m = n\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 c),$(Grow_memory)]) \<Down>k{(ls,r,i)} (s,vs,RValue [(ConstInt32 int32_minus_one)])"
  \<comment> \<open>\<open>call\<close>\<close>
| call:"\<lbrakk>const_list ves; (s,vs,ves@[Callcl (sfunc s i j)]) \<Down>k{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$(Call j)]) \<Down>(Suc k){(ls,r,i)} (s',vs',res)"
  \<comment> \<open>\<open>call_indirect\<close>\<close>
| call_indirect_Some:"\<lbrakk>stab s i (nat_of_int c) = Some cl; stypes s i j = tf; cl_type cl = tf; const_list ves; (s,vs,ves@[Callcl cl]) \<Down>k{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Call_indirect j)]) \<Down>k{(ls,r,i)} (s',vs',res)"
| call_indirect_None:"\<lbrakk>(stab s i (nat_of_int c) = Some cl \<and> stypes s i j \<noteq> cl_type cl) \<or> stab s i (nat_of_int c) = None\<rbrakk> \<Longrightarrow> (s,vs,[$C (ConstInt32 c), $(Call_indirect j)]) \<Down>k{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>call\<close>\<close>
| callcl_native:"\<lbrakk>cl = Func_native j (t1s _> t2s) ts es; ves = ($$* vcs); length vcs = n; length t1s = n; length t2s = m; (n_zeros ts = zs); (s,vs,[Local m j (vcs@zs) [$(Block ([] _> t2s) es)]]) \<Down>k{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [Callcl cl]) \<Down>k{(ls,r,i)} (s',vs',res)"
| callcl_host_Some:"\<lbrakk>cl = Func_host (t1s _> t2s) f; ves = ($$* vcs); length vcs = n; length t1s = n; length t2s = m; host_apply s (t1s _> t2s) f vcs hs = Some (s', vcs')\<rbrakk> \<Longrightarrow> (s,vs,ves @ [Callcl cl]) \<Down>k{(ls,r,i)} (s',vs,RValue vcs')"
| callcl_host_None:"\<lbrakk>cl = Func_host (t1s _> t2s) f; ves = ($$* vcs); length vcs = n; length t1s = n; length t2s = m\<rbrakk> \<Longrightarrow> (s,vs,ves @ [Callcl cl]) \<Down>k{(ls,r,i)} (s,vs,RTrap)"
  \<comment> \<open>\<open>value congruence\<close>\<close>
| const_value:"\<lbrakk>(s,vs,es) \<Down>k{\<Gamma>} (s',vs',RValue res); ves \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,($$*ves)@es) \<Down>k{\<Gamma>} (s',vs',RValue (ves@res))"
| label_value:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RValue res)"
| local_value:"\<lbrakk>(s,lls,es) \<Down>k{([],Some n,j)} (s',lls',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>k{\<Gamma>} (s',vs,RValue res)"
  \<comment> \<open>\<open>seq congruence\<close>\<close>
| seq_value:"\<lbrakk>(s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue res''); (s'',vs'',($$* res'') @ es') \<Down>k{\<Gamma>} (s',vs',res); \<not> const_list es; es' \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,es @ es') \<Down>k{\<Gamma>} (s',vs',res)"
| seq_nonvalue1:"\<lbrakk>const_list ves; (s,vs,es) \<Down>k{\<Gamma>} (s',vs',res); \<nexists>rvs. res = RValue rvs; ves \<noteq> []; es \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,ves @ es) \<Down>k{\<Gamma>} (s',vs',res)"
| seq_nonvalue2:"\<lbrakk>(s,vs,es) \<Down>k{\<Gamma>} (s',vs',res); \<nexists>rvs. res = RValue rvs; es' \<noteq> []\<rbrakk> \<Longrightarrow> (s,vs,es @ es') \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>trap congruence\<close>\<close>
| label_trap:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RTrap)"
| local_trap:"\<lbrakk>(s,lls,es) \<Down>k{([],Some n,j)} (s',lls',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>k{\<Gamma>} (s',vs,RTrap)"
  \<comment> \<open>\<open>break congruence\<close>\<close>
| label_break_suc:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RBreak (Suc bn) bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RBreak bn bvs)"
| label_break_nil:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s'',vs'',RBreak 0 bvs); (s'',vs'',($$* bvs) @ les) \<Down>k{(ls,r,i)} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',res)"
  \<comment> \<open>\<open>return congruence\<close>\<close>
| label_return:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RReturn rvs)"
| local_return:"\<lbrakk>(s,lls,es) \<Down>k{([],Some n,j)} (s',lls',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>k{\<Gamma>} (s',vs,RValue rvs)"

lemma reduce_to_n_mono:
  assumes "(c1 \<Down>k{\<Gamma>} c2)"
  shows"\<forall>k' \<ge> k. (c1 \<Down>k'{\<Gamma>} c2)"
  using assms
proof (induction rule: reduce_to_n.induct)
  case (call ves s vs i j k ls r s' vs' res)
  thus ?case
    using reduce_to_n.call
    by (metis Suc_le_D Suc_le_lessD less_Suc_eq_le)
qed (fastforce intro: reduce_to_n.intros)+

lemma reduce_to_imp_reduce_to_n:
  assumes "(c1 \<Down>{\<Gamma>} c2)"
  shows"(\<exists>k. (c1 \<Down>k{\<Gamma>} c2))"
  using assms
proof (induction rule: reduce_to.induct)
  case (seq_value s vs es \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using reduce_to_n_mono reduce_to_n.seq_value
    by (meson le_cases)
next
  case (label_break_nil s vs es n ls r i s'' vs'' bvs les s' vs' res)
  thus ?case
    using reduce_to_n_mono reduce_to_n.label_break_nil
    by (meson le_cases)
next
qed (fastforce intro: reduce_to_n.intros)+

lemma reduce_to_n_imp_reduce_to:
  assumes "(c1 \<Down>k{\<Gamma>} c2)"
  shows"(c1 \<Down>{\<Gamma>} c2)"
  using assms
  apply (induction rule: reduce_to_n.induct)
                      apply (fastforce intro: reduce_to.intros)+
  done

lemma reduce_to_n_emp:
  assumes "(s,vs,[]) \<Down>k{\<Gamma>} (s',vs',res)"
  shows "res = RValue []"
  using assms
  apply (induction "(s,vs,[]::e list)" k \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res rule: reduce_to_n.induct)
                  apply auto
  done

lemma reduce_to_iff_reduce_to_n:
  shows "(c1 \<Down>{\<Gamma>} c2) = (\<exists>k. (c1 \<Down>k{\<Gamma>} c2))"
  using reduce_to_imp_reduce_to_n reduce_to_n_imp_reduce_to
  by blast

lemma reduce_to_n_consts1: "((s,vs,($$*ves)) \<Down>k{\<Gamma>} (s,vs,RValue ves))"
  using reduce_to_n.emp reduce_to_n.const_value reduce_to_n.emp
  apply (cases "ves = []")
  apply simp_all
  apply (metis append.right_neutral)
  done

lemma reduce_to_consts:
  assumes "((s,vs,($$*ves)) \<Down>{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue ves"
  using assms
proof (induction "(s,vs,($$*ves))""\<Gamma>" "(s',vs',res)" arbitrary: s vs ves s' vs' res rule: reduce_to.induct)
  case (block ves n t1s t2s m es \<Gamma>)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by blast
next
  case (loop ves n t1s t2s m es \<Gamma>)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by blast
next
  case (if_false n ves tf e2s \<Gamma> e1s)
  thus ?case
    using consts_cons_last2(3) e_type_const_unwrap
    by (metis b_e.distinct(325) e.inject(1))
next
  case (if_true n ves tf e1s \<Gamma> e2s)
  thus ?case
    using consts_cons_last2(3) e_type_const_unwrap
    by (metis b_e.distinct(325) e.inject(1))
next
  case (br vcs n k ls r i)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by auto
next
  case (br_if_true n ves k \<Gamma>)
  thus ?case
    using consts_cons_last2(3) e_type_const_unwrap
    by (metis b_e.distinct(403) e.inject(1))
next
  case (br_table ks c ves \<Gamma> k)
  thus ?case
    using consts_cons_last2(3) e_type_const_unwrap
    by (metis b_e.distinct(439) e.inject(1))
next
  case (br_table_length ks c ves k \<Gamma>)
  thus ?case
    using consts_cons_last2(3) e_type_const_unwrap
    by (metis b_e.distinct(439) e.inject(1))
next
  case (return r vcs ls i)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by auto
next
  case (call ves i j ls r)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by blast
next
  case (call_indirect_Some i c cl j tf ves ls r)
  thus ?case
    using consts_cons_last2(3) e_type_const_unwrap
    by (metis b_e.distinct(535) e.inject(1))
next
  case (callcl_native cl j t1s t2s ts es ves vcs n k m zs ls r i)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by blast
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m hs vcs' ls r i)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by auto
next
  case (const_value s vs es \<Gamma> s' vs' res ves)
  thus ?case
    by (metis consts_app_ex(2) inj_basic_econst map_append map_injective res_b.inject(1))
next
  case (callcl_host_None cl t1s t2s f ves vcs n m ls r i)
  thus ?case
    using consts_cons_last(2) e_type_const_unwrap
    by auto
next
  case (seq_value s vs es \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_ex(1)
    by blast
next
  case (seq_nonvalue1 ves s vs es \<Gamma> s' vs' res)
  thus ?case
    using consts_app_ex
    by meson
next
  case (seq_nonvalue2 s vs es \<Gamma> s' vs' res es' ves)
  thus ?case
    using consts_app_ex
    by meson
qed auto

lemma reduce_to_n_consts:
  assumes "((s,vs,($$*ves)) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue ves"
  using assms reduce_to_consts reduce_to_n_imp_reduce_to
  by blast

lemma call0: "((s,vs,($$*ves)@[$(Call j)]) \<Down>0{\<Gamma>} (s',vs',res)) \<Longrightarrow> False"
proof (induction "(s,vs,($$*ves)@[$(Call j)])" "0::nat" \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res ves rule: reduce_to_n.induct)
  case (const_value s vs es \<Gamma> s' vs' res ves ves')
  consider (1) "es = []" | (2) "\<exists>ves'. es = ($$* ves') @ [$Call j]"
    using consts_cons_last consts_app_ex const_value(3)
    by (metis const_value.hyps(4) consts_app_snoc)
  thus ?case
    using const_value
    apply (cases)
    apply (metis append_Nil2 b_e.distinct(505) const_list_cons_last(2) e.inject(1) e_type_const_unwrap is_const_list)
    apply blast
    done
next
  case (seq_value s vs es \<Gamma> s'' vs'' res'' es' s' vs' res)
  consider (1) "es' = []" | (2) "\<exists>ves'. es' = ($$* ves') @ [$Call j]"
    using consts_cons_last consts_app_ex seq_value(7)
    by (metis consts_app_snoc seq_value.hyps(6))
  thus ?case
    using seq_value
    apply (cases)
    apply fastforce
    apply (metis append_assoc map_append)
    done
next
  case (seq_nonvalue1 ves s vs es \<Gamma> s' vs' res)
  thus ?case
    by (metis consts_app_snoc)
next
  case (seq_nonvalue2 s vs es \<Gamma> s' vs' res es' ves)
  thus ?case
    by (metis consts_app_snoc reduce_to_consts reduce_to_n_imp_reduce_to)
qed (fastforce intro: reduce_to_n.intros)+

lemma reduce_to_n_current_memory:
  assumes "((s,vs,($$*ves)@[$Current_memory]) \<Down>k{(ls,r,i)} (s',vs',res))"
  shows "\<exists>n j m. s = s' \<and> vs = vs' \<and> res = RValue (ves@[ConstInt32 (int_of_nat n)]) \<and> smem_ind s i = Some j \<and> ((mem s)!j) = m \<and> mem_size m = n"
  using assms
proof (induction "(s,vs,($$*ves)@[$Current_memory])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k s' vs' res ves)
  consider (1) "es = []" | (2) "\<exists>ves'. es = ($$* ves') @ [$Current_memory]"
    using consts_app_snoc[OF const_value(4)]
    by fastforce
  thus ?case
  proof (cases)
    case 1
    thus ?thesis
      by (metis append_Nil2 b_e.distinct(703) const_value.hyps(3) const_value.hyps(4) e.inject(1) last_map last_snoc)
  next
    case 2
    thus ?thesis
      using const_value
      by (metis (no_types, lifting) append.assoc append1_eq_conv inj_basic_econst map_append map_injective res_b.inject(1))
  qed
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    apply simp
    apply (metis (no_types, lifting) reduce_to_n_consts res_b.inject(1))
    done
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  thus ?case
    by (metis consts_app_snoc)
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    by (metis consts_app_snoc reduce_to_n_consts)
qed auto

lemma no_reduce_to_n:
  assumes "(s, vs, [e]) \<Down>k{\<Gamma>} (s', vs', res)"
          "(e = $Unop t uop) \<or> (e = $Testop t testop) \<or> (e = $Binop t bop) \<or> (e = $Relop t rop) \<or>
           (e = $(Cvtop t2 cvtop t1 sx)) \<or> (e = $Drop) \<or> e = $Select"
  shows False
  using assms
proof (induction "(s,vs,[e])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs s' vs' res k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves)
  thus ?case
    using e_type_const_unwrap consts_cons(2) append_eq_Cons_conv
    by (metis b_e.distinct(145) b_e.distinct(193) b_e.distinct(727) b_e.distinct(729) b_e.distinct(731) b_e.distinct(733) b_e.distinct(735) e.inject(1))
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    by (metis Cons_eq_append_conv append.right_neutral append_is_Nil_conv consts_app_ex(2) is_const_list)
next
  case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
  thus ?case
    by (metis Cons_eq_append_conv Nil_is_append_conv)
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  thus ?case
    by (metis append_is_Nil_conv butlast.simps(2) butlast_append reduce_to_n_emp)
qed auto

lemma no_reduce_to_n2:
  assumes "(s, vs, [$C v, e]) \<Down>k{\<Gamma>} (s', vs', res)"
          "(e = $Binop t bop) \<or> (e = $Relop t rop) \<or> (e = $Select)"
  shows False
proof -
  have 0:"\<not>is_const e"
    using assms(2)
    by (auto simp add: is_const_def)
  show ?thesis
    using assms
  proof (induction "(s,vs,[$C v, e])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs s' vs' res k rule: reduce_to_n.induct)
    case (const_value s vs es k \<Gamma> s' vs' res ves)
    hence "es = [e]"
      using consts_app_snoc_1[OF _ 0, of ves es "[]" v]
      by simp
    thus ?thesis
      using no_reduce_to_n const_value(1) assms(2)
      by blast
  next
    case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
    thus ?case
      by (metis 0 append_self_conv2 consts_app_snoc_1_const_list list.simps(8))
  next
    case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
    hence "es = [e]"
      using consts_app_snoc[of ves es "[v]" "e"] 0
      by (metis append_Cons append_is_Nil_conv butlast.simps(2) butlast_append list.simps(8,9) self_append_conv2)
    thus ?thesis
      using no_reduce_to_n seq_nonvalue1(2) assms(2)
      by blast
  next
    case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
    thus ?thesis
      using consts_app_snoc[of es es' "[v]" "e"]
      apply simp
      apply (metis reduce_to_n_consts)
      done
  qed auto
qed

lemma no_reduce_to_n3:
  assumes "(s, vs, [$C v1, $C v2, e]) \<Down>k{\<Gamma>} (s', vs', res)"
          "(e = $Select)"
  shows False
proof -
  have 0:"\<not>is_const e"
    using assms(2)
    by (auto simp add: is_const_def)
  show ?thesis
    using assms
  proof (induction "(s,vs,[$C v1, $C v2, e])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs s' vs' res k rule: reduce_to_n.induct)
    case (const_value s vs es k \<Gamma> s' vs' res ves)
    hence "es = [e] \<or> es = [$C v2, e]"
      using consts_app_snoc_2[OF _ 0, of ves es "[]" v1 v2]
      by auto
    thus ?thesis
      using no_reduce_to_n no_reduce_to_n2 const_value(1) assms(2)
      by metis
  next
    case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
    thus ?case
      by (metis "0" append_self_conv2 consts_app_snoc_2_const_list list.simps(8))
  next
    case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
    hence "es = [e] \<or> es = [$C v2, e]"
      using consts_app_snoc_2[OF _ 0, of _ es "[]" v1 v2]
      by (metis Nil_is_map_conv append_eq_append_conv2 append_is_Nil_conv e_type_const_conv_vs)
    thus ?thesis
      using no_reduce_to_n no_reduce_to_n2 seq_nonvalue1(2) assms(2)
      by metis
  next
    case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
    thus ?thesis
      using consts_app_snoc[of es es' "[v1,v2]" "e"]
      apply simp
      apply (metis reduce_to_n_consts)
      done
  qed auto
qed

lemma no_reduce_to_n_unop:
  assumes "(s, vs, [($Unop t uop)]) \<Down>k{\<Gamma>} (s', vs', res)"
  shows False
  using assms no_reduce_to_n
  by blast

lemma reduce_to_n_nop:
  assumes "((s,vs,($$*ves)@[$Nop]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue (ves)"
  using assms
proof (induction "(s,vs,($$*ves)@[$Nop])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  thus ?case
    using consts_app_snoc[OF const_value(4)]
    apply simp
    apply (metis (mono_tags, lifting) b_e.distinct(95) e.inject(1) inj_basic_econst last_map last_snoc map_injective)
    done
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    by (metis is_const_list)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc[OF seq_nonvalue1(7)]
    by (metis seq_nonvalue1.hyps(3,4,6))
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc[OF seq_nonvalue2(5)]
    by (metis is_const_list seq_nonvalue2.hyps(4))
qed auto

lemma reduce_to_n_drop:
  assumes "((s,vs,($$*ves)@[$C v, $Drop]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue (ves)"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v, $Drop])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "es = [$Drop] \<and> ves = ves' @ [v]" | (2) "(\<exists>ves''. es = ($$* ves'') @ [$C v, $Drop] \<and> ves' = ves @ ves'')"
    using consts_app_snoc_1[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n const_value(1)
      by blast
  next
    case 2
    then obtain ves'' where "es = ($$* ves'') @ [$C v, $Drop]"
                            "ves'  = ves @ ves''"
      by blast
    thus ?thesis
      using const_value(2)
      by auto
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_value(7)]
    by (metis b_e.simps(167) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_1[of _ es "ves" "v" "$Drop"] e_type_const_conv_vs[of ves']
          no_reduce_to_n seq_nonvalue1
    apply (simp add: is_const_def)
    apply blast
    done
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
next
qed auto

lemma reduce_to_n_select:
  assumes "((s,vs,($$*ves)@[$C v1, $C v2, $C ConstInt32 n, $Select]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> ((res = RValue (ves@[v2]) \<and> int_eq n 0) \<or> (res = RValue (ves@[v1]) \<and> int_ne n 0))"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v1, $C v2, $C ConstInt32 n, $Select])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "es = [$Select] \<and> ves = ves' @ [v1, v2, ConstInt32 n]"
         | (2) "es = [$C ConstInt32 n, $Select] \<and> ves = ves' @ [v1, v2]"
         | (3) "es = [$C v2, $C ConstInt32 n, $Select] \<and>  ves = ves' @ [v1]"
         | (4) ves'' where "(es = ($$* ves'') @ [$C v1, $C v2, $C ConstInt32 n, $Select] \<and> ves' = ves @ ves'')"
    using consts_app_snoc_3[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      by (metis const_value.hyps(1) no_reduce_to_n)
  next
    case 2
    thus ?thesis
      by (metis const_value.hyps(1) no_reduce_to_n2)
  next
    case 3
    thus ?thesis
      by (metis const_value.hyps(1) no_reduce_to_n3)
  next
    case 4
    thus ?thesis
      using const_value(2)
      by (metis append.assoc res_b.inject(1))
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_3_const_list[OF seq_value(7)]
    by (metis b_e.distinct(193) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_3[of _ es "ves" v1 v2 "ConstInt32 n" "$Select"] e_type_const_conv_vs[of ves']
          no_reduce_to_n seq_nonvalue1
    apply (simp add: is_const_def)
    apply (metis no_reduce_to_n2 no_reduce_to_n3)
    done
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_3_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
qed auto

lemma reduce_to_n_unop:
  assumes "((s,vs,($$*ves)@[$C v, $Unop t op]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue (ves@[(app_unop op v)])"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v, $Unop t op])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "es = [$Unop t op] \<and> ves = ves' @ [v]" | (2) "(\<exists>ves''. es = ($$* ves'') @ [$C v, $Unop t op] \<and> ves' = ves @ ves'')"
    using consts_app_snoc_1[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n_unop const_value(1)
      by blast
  next
    case 2
    then obtain ves'' where "es = ($$* ves'') @ [$C v, $Unop t op]"
                            "ves'  = ves @ ves''"
      by blast
    thus ?thesis
      using const_value(2)
      by auto
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_value(7)]
    by (metis b_e.distinct(727) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_1[of _ es "ves" "v" "$Unop t op"] e_type_const_conv_vs[of ves']
          no_reduce_to_n_unop seq_nonvalue1
    apply (simp add: is_const_def)
    apply blast
    done
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
next
qed auto

lemma no_reduce_to_n_testop:
  assumes "(s, vs, [$Testop t op]) \<Down>k{\<Gamma>} (s', vs', res)"
  shows False
  using assms no_reduce_to_n
  by blast

lemma reduce_to_n_testop:
  assumes "((s,vs,($$*ves)@[$C v, $Testop t op]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue (ves@[(app_testop op v)])"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v, $Testop t op])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "es = [$Testop t op] \<and> ves = ves' @ [v]" | (2) "(\<exists>ves''. es = ($$* ves'') @ [$C v, $Testop t op] \<and> ves' = ves @ ves'')"
    using consts_app_snoc_1[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n_testop const_value(1)
      by blast
  next
    case 2
    then obtain ves'' where "es = ($$* ves'') @ [$C v, $Testop t op]"
                            "ves'  = ves @ ves''"
      by blast
    thus ?thesis
      using const_value(2)
      by auto
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_value(7)]
    by (metis b_e.distinct(731) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_1[of _ es "ves" "v" "$Testop t op"] e_type_const_conv_vs[of ves']
          no_reduce_to_n_testop seq_nonvalue1
    apply (simp add: is_const_def)
    apply blast
    done
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
next
qed auto

lemma no_reduce_to_n_binop:
  assumes "(s, vs, [$Binop t op]) \<Down>k{\<Gamma>} (s', vs', res)"
  shows False
  using assms no_reduce_to_n
  by blast

lemma no_reduce_to_n2_binop:
  assumes "(s, vs, [$C v, $Binop t op]) \<Down>k{\<Gamma>} (s', vs', res)"
  shows False
  using assms no_reduce_to_n2
  by blast

lemma reduce_to_n_binop:
  assumes "((s,vs,($$*ves)@[$C v1, $C v2, $Binop t op]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and>
         ((\<exists>v. (app_binop op v1 v2 = Some v) \<and> res = RValue (ves@[v])) \<or>
            (\<exists>v. (app_binop op v1 v2 = None) \<and> res = RTrap))"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v1, $C v2, $Binop t op])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "(es = [$Binop t op] \<and> ves = ves' @ [v1, v2])"
         | (2) "(es = [$C v2, $Binop t op] \<and> ves = ves'@[v1])"
         | (3) "(\<exists>ves''. es = ($$*ves'')@[$C v1, $C v2, $Binop t op] \<and> ves' = ves@ves'')"
    using consts_app_snoc_2[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n_binop const_value(1)
      by blast
  next
    case 2
    thus ?thesis
      using no_reduce_to_n2_binop const_value(1)
      by blast
  next
    case 3
    thus ?thesis
      using const_value.hyps(2)
      by auto
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_2_const_list[OF seq_value(7)]
    by (metis b_e.distinct(729) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_2[of _ es "ves" "v1" "v2" "$Binop t op"]
    apply (simp add: is_const_def)
    apply (metis (no_types, lifting) e_type_const_conv_vs no_reduce_to_n2_binop no_reduce_to_n_binop seq_nonvalue1.hyps(1) seq_nonvalue1.hyps(2,3,4) seq_nonvalue1.hyps(7))
    done
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_2_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
qed auto

lemma no_reduce_to_n_relop:
  assumes "(s, vs, [$Relop t op]) \<Down>k{\<Gamma>} (s', vs', res)"
  shows False
  using assms no_reduce_to_n
  by blast

lemma no_reduce_to_n2_relop:
  assumes "(s, vs, [$C v, $Relop t op]) \<Down>k{\<Gamma>} (s', vs', res)"
  shows False
  using assms no_reduce_to_n2
  by blast

lemma reduce_to_n_relop:
  assumes "((s,vs,($$*ves)@[$C v1, $C v2, $Relop t op]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue (ves@[(app_relop op v1 v2)])"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v1, $C v2, $Relop t op])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "(es = [$Relop t op] \<and> ves = ves' @ [v1, v2])"
         | (2) "(es = [$C v2, $Relop t op] \<and> ves = ves'@[v1])"
         | (3) "(\<exists>ves''. es = ($$*ves'')@[$C v1, $C v2, $Relop t op] \<and> ves' = ves@ves'')"
    using consts_app_snoc_2[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n_relop const_value(1)
      by blast
  next
    case 2
    thus ?thesis
      using no_reduce_to_n2_relop const_value(1)
      by blast
  next
    case 3
    thus ?thesis
      by (metis append.assoc const_value.hyps(2) res_b.inject(1))
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_2_const_list[OF seq_value(7)]
    by (metis b_e.distinct(733) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_2[of _ es "ves" "v1" "v2" "$Relop t op"]
    by (metis (no_types, lifting) b_e.distinct(733) e.inject(1) e_type_const_conv_vs e_type_const_unwrap no_reduce_to_n_relop no_reduce_to_n2_relop seq_nonvalue1.hyps(1,2,3,4) seq_nonvalue1.hyps(7))
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_2_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
qed auto

lemma reduce_to_n_convert:
  assumes "((s,vs,($$*ves)@[$C v, $Cvtop t2 Convert t1 sx]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> types_agree t1 v \<and>
         (\<exists>v'. (res = RValue (ves@[v']) \<and> cvt t2 sx v = (Some v')) \<or> 
          (res = RTrap \<and> cvt t2 sx v = None))"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v, $Cvtop t2 Convert t1 sx])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "es = [$Cvtop t2 Convert t1 sx] \<and> ves = ves' @ [v]" | (2) "(\<exists>ves''. es = ($$* ves'') @ [$C v, $Cvtop t2 Convert t1 sx] \<and> ves' = ves @ ves'')"
    using consts_app_snoc_1[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n const_value(1)
      by blast
  next
    case 2
    then obtain ves'' where "es = ($$* ves'') @ [$C v, $Cvtop t2 Convert t1 sx]"
                            "ves'  = ves @ ves''"
      by blast
    thus ?thesis
      using const_value(2)
      by fastforce
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_value(7)]
    by (metis b_e.distinct(735) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_1[of _ es "ves" "v" "$Cvtop t2 Convert t1 sx"] e_type_const_conv_vs[of ves']
          no_reduce_to_n seq_nonvalue1
    apply (simp add: is_const_def)
    apply blast
    done
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
qed auto

lemma reduce_to_n_reinterpret:
  assumes "((s,vs,($$*ves)@[$C v, $Cvtop t2 Reinterpret t1 None]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "s = s' \<and> vs = vs' \<and> res = RValue (ves@[(wasm_deserialise (bits v) t2)]) \<and> types_agree t1 v"
  using assms
proof (induction "(s,vs,($$*ves)@[$C v, $Cvtop t2 Reinterpret t1 None])" k "\<Gamma>" "(s',vs',res)" arbitrary: s vs vs' s' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  consider (1) "es = [$Cvtop t2 Reinterpret t1 None] \<and> ves = ves' @ [v]" | (2) "(\<exists>ves''. es = ($$* ves'') @ [$C v, $Cvtop t2 Reinterpret t1 None] \<and> ves' = ves @ ves'')"
    using consts_app_snoc_1[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n const_value(1)
      by blast
  next
    case 2
    then obtain ves'' where "es = ($$* ves'') @ [$C v, $Cvtop t2 Reinterpret t1 None]"
                            "ves'  = ves @ ves''"
      by blast
    thus ?thesis
      using const_value(2)
      by auto
  qed
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_value(7)]
    by (metis b_e.distinct(735) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves' s vs es k \<Gamma> s' vs' res)
  show ?case
    using consts_app_snoc_1[of _ es "ves" "v" "$Cvtop t2 Reinterpret t1 None"] e_type_const_conv_vs[of ves']
          no_reduce_to_n seq_nonvalue1
    apply (simp add: is_const_def)
    apply blast
    done
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
qed auto

lemma no_reduce_to_n_grow_memory:
  assumes "(s, vs, [$Grow_memory]) \<Down>k{(ls, r, i)} (s', vs', res)"
  shows False
  using assms
  apply (induction "(s,vs,[$Grow_memory])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res k rule: reduce_to_n.induct)
  apply simp_all
  apply (metis append_eq_Cons_conv b_e.distinct(715) consts_cons(2) e.inject(1) e_type_const_unwrap)
  apply (metis Cons_eq_append_conv append.right_neutral append_is_Nil_conv consts_app_ex(2) is_const_list)
  apply (simp add: append_eq_Cons_conv)
  apply (metis Nil_is_append_conv append_eq_Cons_conv reduce_to_n_emp)
  done

lemma reduce_to_n_grow_memory:
  assumes "((s,vs,($$*ves)@[$C ConstInt32 c, $Grow_memory]) \<Down>k{(ls,r,i)} (s',vs',res))"
  shows "\<exists>n j m. (vs = vs' \<and> smem_ind s i = Some j \<and> ((mem s)!j) = m \<and> mem_size m = n) \<and> ((s = s' \<and> res = RValue (ves@[ConstInt32 int32_minus_one])) \<or> (s' = s \<lparr>s.mem := s.mem s [j := mem_grow (s.mem s ! j) (Wasm_Base_Defs.nat_of_int c)]\<rparr> \<and> res = RValue (ves@[ConstInt32 (int_of_nat n)])))"
  using assms
proof (induction "(s,vs,($$*ves)@[$C ConstInt32 c, $Grow_memory])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs vs' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es k vs' res ves ves')
  consider (1) "es = [$Grow_memory] \<and> ves = ves' @ [ConstInt32 c]" | (2) "(\<exists>ves''. es = ($$* ves'') @ [$C ConstInt32 c, $Grow_memory] \<and> ves' = ves @ ves'')"
    using consts_app_snoc_1[OF const_value(4)] is_const_def
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using no_reduce_to_n_grow_memory const_value(1)
      by blast
  next
    case 2
    then obtain ves'' where "es = ($$* ves'') @ [$C ConstInt32 c, $Grow_memory]"
                            "ves'  = ves @ ves''"
      by blast
    thus ?thesis
      using const_value(2)
      by auto
  qed
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_value(7)]
    by (meson b_e.distinct(715) e.inject(1) e_type_const_unwrap)
next
  case (seq_nonvalue1 ves s vs es k vs' res ves')
  show ?case
    using consts_app_snoc_1[of _ es "ves'" "ConstInt32 c" "$Grow_memory"] e_type_const_conv_vs[of ves]
          no_reduce_to_n_grow_memory seq_nonvalue1
    apply (simp add: is_const_def)
    apply blast
    done
next
  case (seq_nonvalue2 s vs es k vs' res es')
  have "\<not> const_list es"
    using seq_nonvalue2(1,3) reduce_to_consts e_type_const_conv_vs reduce_to_n_imp_reduce_to
    by metis
  thus ?case
    using consts_app_snoc_1_const_list[OF seq_nonvalue2(5)] seq_nonvalue2(4)
    by (simp add: is_const_def)
qed auto

lemma calln_imp: "((s,vs,($$*ves)@[$(Call j)]) \<Down>(Suc k){(ls,r,i)} (s',vs',res)) \<Longrightarrow> ((s,vs,($$*ves)@[(Callcl (sfunc s i j))]) \<Down>k{(ls,r,i)} (s',vs',res))"
proof (induction "(s,vs,($$*ves)@[$(Call j)])" "(Suc k)" "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es s' vs' res ves ves')
  consider (1) "($$* ves) = ($$* ves') @ [$Call j] \<and> es = []"
         | (2) "(\<exists>ves'a ves''.
                  ($$* ves) = ($$* ves'a) \<and>
                  es = ($$* ves'') @ [$Call j] \<and>
                  ves' = ves'a @ ves'')"
    using consts_app_snoc[OF const_value(4)]
    by fastforce
  thus ?case
  proof (cases)
    case 1
    thus ?thesis
      by (metis b_e.distinct(505) consts_cons_last(2) e.inject(1) e_type_const_unwrap)
  next
    case 2
    then obtain ves'a ves'' where ves''_def:"($$* ves) = ($$* ves'a)"
                                            "es = ($$* ves'') @ [$Call j]"
                                            "ves' = ves'a @ ves''"
      by blast
    thus ?thesis
      using const_value(2)[OF ves''_def(2)]  const_value.hyps(3) reduce_to_n.const_value
      by fastforce
  qed
next
  case (seq_value s vs es s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)] reduce_to_consts reduce_to_n_imp_reduce_to
    apply (cases "es = ($$* ves) @ [$Call j] \<and> es' = []")
    apply fastforce
    apply blast
    done
next
  case (seq_nonvalue1 ves s vs es s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_nonvalue1(7)]
    apply (auto simp add: reduce_to_n.seq_nonvalue1)
    done
next
  case (seq_nonvalue2 s vs es s' vs' res es')
  thus ?case
    using consts_app_snoc[OF seq_nonvalue2(5)] reduce_to_n_consts
    apply fastforce
    done
qed (fastforce intro: reduce_to_n.intros)+

lemma reduce_to_n_br_imp_length:
  assumes "(s,vs,($$* vcs) @ [$Br j]) \<Down>k{(ls,r,i)} (s',vs',res)"
  shows "length vcs \<ge> (ls!j) \<and> (\<exists>vcs'. res = RBreak j vcs')"
  using assms
proof (induction "(s,vs,($$* vcs) @ [$Br j])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res vcs rule: reduce_to_n.induct)
  case (br vcs' n j' s vs k)
  hence "j = j'" "vcs = vcs'"
    using inj_basic_econst
    by auto
  thus ?case
    using br
    by simp
next
  case (const_value s vs es k s' vs' res ves)
  have "(\<exists>ves' ves''. ($$* ves) = ($$* ves') \<and> es = ($$* ves'') @ [$Br j] \<and> vcs = ves' @ ves'')"
    using const_value consts_app_snoc[OF const_value(4)]
    by (metis b_e.simps(387) consts_cons_last(2) e.inject(1) e_type_const_unwrap)
  thus ?case
    using const_value(2)
    by (metis res_b.distinct(1))
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    by (metis consts_app_snoc is_const_list)
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  thus ?case
    by (metis consts_app_snoc length_append trans_le_add2)
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    by (metis (no_types, lifting) consts_app_snoc reduce_to_consts reduce_to_n_imp_reduce_to)
qed auto

lemma reduce_to_n_br:
  assumes "(s,vs,($$* vcsf) @ ($$* vcs) @ [$Br j]) \<Down>k{(ls,r,i)} (s',vs',res)"
          "length vcs = (ls!j)"
  shows "((s,vs,($$* vcs) @ [$Br j]) \<Down>k{(ls,r,i)} (s',vs',res)) \<and> s = s' \<and> vs = vs' \<and> (res = RBreak j vcs)"
  using assms
proof (induction "(s,vs,($$* vcsf) @ ($$* vcs) @ [$Br j])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res vcs vcsf rule: reduce_to_n.induct)
  case (br vcs' n j' s vs k)
  hence "vcs = vcs' \<and> j = j'"
    using inj_basic_econst
    apply simp
    apply (metis append_eq_append_conv append_eq_append_conv2 length_map map_injective)
    done
  thus ?case
    by (metis br(1,2) reduce_to_n.br)
next
  case (const_value s vs es k s' vs' res ves)
  then consider
      (1) "($$* ves) = ($$* vcsf @ vcs) @ [$Br j] \<and> es = []"
    | (2) ves' ves'' where "ves = ves' \<and> es = ($$* ves'') @ [$Br j] \<and> vcsf @ vcs = ves' @ ves''"
    using consts_app_snoc[of "($$* ves)" es "vcsf@vcs" "$Br j"] inj_basic_econst
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      by (metis b_e.distinct(365) consts_cons_last(2) e.inject(1) e_type_const_unwrap)
  next
    case 2
    show ?thesis
    proof (cases "length ves'' \<ge> ls ! j")
      case True
      then obtain ves''_1  where "ves'' = ves''_1@vcs"
        using const_value(5) 2
        by (metis (no_types, lifting) append_eq_append_conv append_eq_append_conv_if le_antisym length_append pl_pl_rels)
      hence 3:"es = ($$* ves''_1) @ ($$* vcs) @ [$Br j]"
        using 2
        by simp
      show ?thesis
        using const_value(2)[OF 3] const_value(5)
        by simp
    next
      case False
      thus ?thesis
        using const_value
        by (metis 2 reduce_to_n_br_imp_length)
    qed
  qed
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[of es es' "vcsf@vcs" "$Br j"]
    apply simp
    apply (metis is_const_list)
    done
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  then obtain ves' ves'' where ves'_def:"ves = ($$* ves') \<and> es = ($$* ves'') @ [$Br j] \<and> vcsf @ vcs = ves' @ ves''"
    using consts_app_snoc[of ves es "vcsf@vcs" "$Br j"]
    by fastforce
  show ?case
  proof (cases "length ves'' \<ge> ls ! j")
    case True
    then obtain ves''_1  where "ves'' = ves''_1@vcs"
      using seq_nonvalue1(8)
      by (metis (no_types, lifting) append_eq_append_conv append_eq_append_conv_if le_antisym length_append pl_pl_rels ves'_def)
    thus ?thesis
      using ves'_def seq_nonvalue1
      by (metis append_assoc map_append)
  next
    case False
    thus ?thesis
      using ves'_def seq_nonvalue1
      by (metis reduce_to_n_br_imp_length)
  qed

next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    using consts_app_snoc[of es es' "vcsf@vcs" "$Br j"]
    apply simp
    apply (metis reduce_to_n_consts)
    done
qed auto


lemma reduce_to_n_br:
  assumes "(s,vs,($$* vcs) @ [$Br j]) \<Down>k{(ls,r,i)} (s',vs',res)"
          "ls!j = n"
          "length vcs = n"
  shows "res = RBreak j vcs"
  using assms
proof (induction "(s,vs,($$* vcs) @ [$Br j])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res vcs rule: reduce_to_n.induct)
  case (br vcs n j s vs k)
  thus ?case
    using inj_basic_econst
    by auto
next
  case (const_value s vs es k s' vs' res ves)
  thus ?case
    using consts_app_snoc[OF const_value(4)]
    apply simp
    apply safe
    apply (metis b_e.simps(387) consts_cons_last(2) e.inject(1) e_type_const_unwrap)
    apply (metis le_add2 le_antisym length_append reduce_to_n_br_imp_length)
    done
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    apply simp
    apply (metis is_const_list)
    done
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_nonvalue1(7)]
    apply safe
    apply simp_all
    apply (metis add_le_same_cancel2 le_zero_eq length_0_conv reduce_to_n_br_imp_length)
    apply (metis add_le_same_cancel2 le_zero_eq length_0_conv reduce_to_n_br_imp_length)
    done
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    using consts_app_snoc[OF seq_nonvalue2(5)]
    apply safe
    apply simp_all
    apply (metis reduce_to_n_consts)
    apply (metis reduce_to_n_consts)
    done
qed auto

lemma calln: "((s,vs,($$*ves)@[$(Call j)]) \<Down>(Suc k){(ls,r,i)} (s',vs',res)) = ((s,vs,($$*ves)@[(Callcl (sfunc s i j))]) \<Down>k{(ls,r,i)} (s',vs',res))"
  using calln_imp reduce_to_n.call
  by (metis is_const_list)

lemma callcl_native_imp_local_length:
  assumes "(s,vs,($$* vcs) @ [Callcl cl]) \<Down>k{(ls,r,i)} (s',vs',res)"
          "cl = Func_native j (t1s _> t2s) ts es"
  shows "length vcs \<ge> length t1s"
  using assms
proof (induction "(s,vs,($$* vcs) @ [Callcl cl])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res vcs rule: reduce_to_n.induct)
  case (callcl_native cl j t1s t2s ts es ves vcs n m zs s vs k s' vs' res)
  thus ?case
    using inj_basic_econst
    by simp
next
  case (const_value s vs es k s' vs' res ves)
  thus ?case
    using consts_app_snoc[OF const_value(4)] consts_cons_last[of _ _ ves] is_const_def
    by fastforce
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    by (metis is_const_list)
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_nonvalue1(7)]
    by force
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    using consts_app_snoc[OF seq_nonvalue2(5)]
    by (metis reduce_to_n_consts)
qed auto

lemma callcl_native_imp_local1:
  assumes "(s,vs,($$* vcs) @ [Callcl cl]) \<Down>k{(ls,r,i)} (s',vs',res)"
          "cl = Func_native j (t1s _> t2s) ts es"
          "length vcs = n"
          "length t1s = n"
          "length t2s = m"
          "(n_zeros ts = zs)"
  shows "(s,vs,[Local m j (vcs@zs) [$(Block ([] _> t2s) es)]]) \<Down>k{(ls,r,i)} (s',vs',res)"
  using assms
proof (induction "(s,vs,($$* vcs) @ [Callcl cl])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res vcs rule: reduce_to_n.induct)
  case (callcl_native cl' j t1s t2s ts es ves' vcs n m zs s vs k s' vs' res)
  thus ?case
    using inj_basic_econst
    by auto
next
  case (const_value s vs es k s' vs' res ves)
  consider (1) "($$* ves) = ($$* vcs) @ [Callcl cl]" "es = []"
         | (2) "(\<exists>ves' ves''. ($$* ves) = ($$* ves') \<and> es = ($$* ves'') @ [Callcl cl] \<and> vcs = ves' @ ves'')"
    using consts_app_snoc[OF const_value(4)] inj_basic_econst
    by auto
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using consts_cons_last[OF 1(1)[symmetric]] is_const_def
      by simp
  next
    case 2
    then obtain ves' ves'' where ves'_def:"($$* ves) = $$* ves'"
                                           "es = ($$* ves'') @ [Callcl cl]"
                                           "vcs = ves' @ ves''"
      by blast
    show ?thesis
    proof (cases "length ves'' \<ge> length t1s")
      case True
      hence "ves'' = vcs"
        using ves'_def const_value(6,7)
        by auto
      thus ?thesis
        using const_value
              ves'_def inj_basic_econst
        by simp
    next
      case False
      thus ?thesis
        using callcl_native_imp_local_length const_value(1,5) ves'_def(2)
        by fastforce
    qed
  qed
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    apply simp
    apply (metis reduce_to_n_consts res_b.inject(1))
    done
next
  case (seq_nonvalue1 ves s vs es' k s' vs' res)
  show ?case
  proof -
    {
      fix ves' :: "v list" and ves'' :: "v list"
      assume a1: "ves = $$* ves'"
      assume a2: "(s, vs, ($$* ves'') @ [Callcl (Func_native j (t1s _> t2s) ts es)]) \<Down>k{(ls, r, i)} (s', vs', res)"
      assume a3: "length t1s = length (ves' @ ves'')"
      have "length t1s \<le> length ves''"
        using a2 by (simp add: callcl_native_imp_local_length)
      then have "ves'' = []"
        using a3 a1 by (simp add: local.seq_nonvalue1(5))
    }
    note a = this
    show ?case
      using consts_app_snoc[OF seq_nonvalue1(7)]
      apply simp
      apply safe
      apply (simp_all add: seq_nonvalue1.hyps(6))
      apply (metis a callcl_native_imp_local_length le_zero_eq length_0_conv self_append_conv2 seq_nonvalue1(2,3,8,9,10,11,12))
      done
  qed
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    using consts_app_snoc[OF seq_nonvalue2(5)] reduce_to_n_consts
    apply simp
    apply blast
    done
next
qed auto

lemma reduce_to_local_nonvalue:
  assumes "(s,vs,($$* vfs)@[Local m j vcs es]) \<Down>k{\<Gamma>} (s',vs',res)"
          "\<nexists>rvs. res = RValue rvs"
  shows "(s,vs,[Local m j vcs es]) \<Down>k{\<Gamma>} (s',vs',res)"
  using assms
proof (induction "(s,vs,($$* vfs)@[Local m j vcs es])" k \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res vfs rule: reduce_to_n.induct)
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    apply simp
    apply (metis reduce_to_n_consts res_b.inject(1))
    done
next
  case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
  thus ?case
    using consts_app_snoc
    by blast
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  thus ?case
    by (metis consts_app_snoc reduce_to_consts reduce_to_n_imp_reduce_to)
next
  case (local_trap s lls es k n j s' lls' vs \<Gamma>)
  thus ?case
    using reduce_to_n.local_trap
    by auto
qed auto

lemma local_imp_body:
  assumes "(s,vs,($$*vfs)@[Local m j lvs les]) \<Down>k{(ls,r,i)} (s',vs',res)"
  shows "\<exists>lvs' lres. ((s,lvs,les) \<Down>k{([],Some m,j)} (s',lvs',lres)) \<and> vs = vs' \<and>
         ((lres = RTrap \<and> res = RTrap) \<or> (\<exists>rvs. ((lres = RValue rvs \<or> lres = RReturn rvs) \<and> res = RValue (vfs@rvs))))"
  using assms
proof (induction "(s,vs,($$*vfs)@[Local m j lvs les])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res les vfs rule: reduce_to_n.induct)
  case (const_value s vs es k s' vs' res ves)
  thus ?case
    using consts_app_snoc[OF const_value(4)]
    apply simp
    apply safe
    apply (metis consts_cons_last(2) e.simps(12) e_type_const_unwrap)
    apply (metis (no_types, lifting) append.assoc inj_basic_econst map_injective)
    done
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  consider (1) "es = ($$* vfs) @ [Local m j lvs les]" "es' = []"
         | (2) "(\<exists>ves' ves''. es = ($$* ves') \<and> es' = ($$* ves'') @ [Local m j lvs les] \<and> vfs = ves' @ ves'')"
    using consts_app_snoc[OF seq_value(7)]
    by blast
  thus ?case
  proof cases
    case 1
    thus ?thesis
      by (metis append.right_neutral reduce_to_n_consts seq_value.hyps(2,3))
  next
    case 2
    then obtain ves' ves'' where
     "es = $$* ves'"
     "es' = ($$* ves'') @ [Local m j lvs les] \<and> vfs = ves' @ ves''"
      by blast
    thus ?thesis
      using seq_value
      by (metis (no_types, lifting) reduce_to_n_consts res_b.inject(1))
  qed
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  thus ?case
    by (metis consts_app_snoc)
next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    using consts_app_snoc[OF seq_nonvalue2(5)]
    by (metis reduce_to_n_consts)
qed auto

lemma callcl_native_imp_local:
  assumes "(s,vs,($$* vfs) @ ($$* vcs) @ [Callcl cl]) \<Down>k{(ls,r,i)} (s',vs',res)"
          "cl = Func_native j (t1s _> t2s) ts es"
          "length vcs = n"
          "length t1s = n"
          "length t2s = m"
          "(n_zeros ts = zs)"
  shows "(s,vs,($$* vfs)@[Local m j (vcs@zs) [$(Block ([] _> t2s) es)]]) \<Down>k{(ls,r,i)} (s',vs',res)"
  using assms
proof (induction "(s,vs,($$* vfs) @ ($$* vcs) @ [Callcl cl])" k "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res vcs vfs rule: reduce_to_n.induct)
  case (callcl_native cl j t1s t2s ts es ves vcs' n m zs s vs k s' vs' res)
   thus ?case
   proof -
     {
       assume a1: "($$* vcs') = ($$* vfs) @ ($$* vcs) \<and> j = j \<and> t1s = t1s \<and> t2s = t2s \<and> ts = ts \<and> es = es"
       assume "ves = ($$* vfs) @ ($$* vcs)"
       assume a2: "length vcs = n"
       assume a3: "length vcs' = n"
       assume a4: "(s, vs, [Local m j (vcs' @ zs) [$Block ([] _> t2s) es]]) \<Down>k{(ls, r, i)} (s', vs', res)"
       have "($$* vfs) = []"
         using a3 a2 a1 by (metis (no_types) append_eq_append_conv length_map self_append_conv2)
       then have "(s, vs, ($$* vfs) @ [Local m j (vcs @ zs) [$Block ([] _> t2s) es]]) \<Down>k{(ls, r, i)} (s', vs', res)"
         using a4 a1 by (metis (no_types) reduce_to_n_consts reduce_to_n_consts1 res_b.inject(1) self_append_conv2)
     }
     thus ?thesis
       using callcl_native
       by auto
   qed
next
  case (const_value s vs es' k s' vs' res ves vcs)
  consider (1) "($$* ves) = ($$*vfs @ vcs) @ [Callcl cl]" "es' = []"
         | (2) "(\<exists>ves' ves''. ($$* ves) = ($$* ves') \<and> es' = ($$* ves'') @ [Callcl cl] \<and> vfs @ vcs = ves' @ ves'')"
    using consts_app_snoc[of "$$*ves" es' "vfs@vcs" "Callcl cl"] inj_basic_econst const_value(4)
    by auto
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using consts_cons_last[OF 1(1)[symmetric]] is_const_def
      by simp
  next
    case 2
    then obtain ves' ves'' where ves'_def:"($$* ves) = $$* ves'"
                                           "es' = ($$* ves'') @ [Callcl cl]"
                                           "vfs @ vcs = ves' @ ves''"
      by blast
    thus ?thesis
    proof (cases "length ves'' \<ge> length t1s")
      case True
      then obtain ves_l ves_l' where ves_l_def:"ves'' = ves_l @ ves_l'"
                                     "length ves_l' = length t1s"
        by (metis (full_types) append_take_drop_id diff_diff_cancel length_drop)
      hence 0:"ves_l' = vcs"
        using ves'_def const_value(6)
        by (metis append.assoc append_eq_append_conv const_value.prems(3))
      hence 1:"(s, vs, ($$* ves_l) @ [Local m j (vcs @ zs) [$Block ([] _> t2s) es]]) \<Down>k{(ls, r,i)} (s', vs', RValue res)"
        by (simp add: const_value.hyps(2) const_value.prems(1) const_value.prems(2) const_value.prems(3) const_value.prems(4) const_value.prems(5) ves'_def(2) ves_l_def(1))
      thus ?thesis
        using reduce_to_n.const_value[OF 1] ves_l_def ves'_def 0 inj_basic_econst 
              const_value.hyps(3)
        by auto
    next
      case False
      thus ?thesis
        using callcl_native_imp_local_length const_value(1,5) ves'_def(2)
        by fastforce
    qed
  qed
next
  case (seq_value s vs es k s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[of es es' "vfs@vcs" "Callcl cl"]
    apply simp
    apply (metis reduce_to_n_consts res_b.inject(1))
    done
next
  case (seq_nonvalue1 ves s vs es k s' vs' res)
  consider (1) "ves = ($$* vfs @ vcs) @ [Callcl cl] \<and> es = []"
         | (2) "(\<exists>ves' ves''.
                ves = ($$* ves') \<and>
                es = ($$* ves'') @ [Callcl cl] \<and>
                vfs @ vcs = ves' @ ves'')"
    using consts_app_snoc[of ves es "vfs@vcs" "Callcl cl"] seq_nonvalue1(7)
    by fastforce
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using seq_nonvalue1(6)
      by blast
  next
    case 2
    then obtain ves' ves'' where ves'_def:"ves = ($$* ves')"
                                          "es = ($$* ves'') @ [Callcl cl]"
                                          "vfs @ vcs = ves' @ ves''"
      by blast
    show ?thesis
    proof (cases "length ves'' \<ge> n")
      case True
      then obtain ves''_1 ves''_2 where ves''_is:"ves'' = ves''_1 @ ves''_2"
                                                 "length ves''_2 = n"
        by (metis append_take_drop_id diff_diff_cancel length_drop)
      hence "vcs = ves''_2 \<and> vfs = ves' @ ves''_1"
        using seq_nonvalue1(9)
        by (metis append_assoc append_eq_append_conv ves'_def(3))
      thus ?thesis
        using ves''_is ves'_def  seq_nonvalue1.hyps(1)
              seq_nonvalue1(3)[OF _ seq_nonvalue1(8,9,10,11,12), of ves''_1]
              reduce_to_n.seq_nonvalue1[OF _ _ seq_nonvalue1(4) , of "$$* (ves')"]
        apply (cases ves')
        apply simp_all
        done
    next
      case False
      thus ?thesis
        using callcl_native_imp_local_length seq_nonvalue1(2,10,8) ves'_def(2)
        by blast
    qed
  qed
  

next
  case (seq_nonvalue2 s vs es k s' vs' res es')
  thus ?case
    using consts_app_snoc[of es es' "vfs@vcs" "Callcl cl"]
    apply simp
    apply (metis reduce_to_n_consts)
    done
next
qed auto

lemma callcl_native_equiv_local:
  assumes "cl = Func_native j (t1s _> t2s) ts es"
          "length vcs = n"
          "length t1s = n"
          "length t2s = m"
          "(n_zeros ts = zs)"
  shows "((s,vs,($$* vcs) @ [Callcl cl]) \<Down>k{(ls,r,i)} (s',vs',res)) = ((s,vs,[Local m j (vcs@zs) [$(Block ([] _> t2s) es)]]) \<Down>k{(ls,r,i)} (s',vs',res))"
  using callcl_native_imp_local1[OF _ assms] reduce_to_n.callcl_native[OF assms(1) _ assms(2,3,4,5)]
  by blast

lemma local_context:
  assumes "((s,vs,[Local n i vls es]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "((s,vs,[Local n i vls es]) \<Down>k{\<Gamma>'} (s',vs',res))"
  using assms
proof (induction "(s,vs,[Local n i vls es])" k \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res rule: reduce_to_n.induct)
  case (const_value s vs es' k \<Gamma> s' vs' res ves)
  thus ?case
    using consts_app_snoc[of "($$* ves)" "es" "[]" "Local n i vls es"]
          consts_cons_last[of "[]" "Local n i vls es" ves]
    apply (simp add: is_const_def)
    apply (metis (no_types, lifting) Cons_eq_append_conv Nil_is_append_conv append_self_conv inj_basic_econst map_append map_injective)
    done
next
  case (local_value k lls' res \<Gamma>)
  thus ?case
    using reduce_to_n.local_value
    by blast
next
  case (seq_value s vs es' k \<Gamma> s'' vs'' res'' es'' s' vs' res)
  consider (1) "es' = [Local n i vls es]" "es'' = []" | (2) "es' = []" "es'' = [Local n i vls es]"
    using seq_value(7)
    unfolding append_eq_Cons_conv
    by fastforce
  thus ?case
    apply (cases)
    apply (metis append_Nil2 reduce_to_consts reduce_to_n_imp_reduce_to seq_value.hyps(2) seq_value.hyps(3))
    apply (metis append.right_neutral consts_app_ex(2) is_const_list seq_value.hyps(5))
    done
next
  case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
  thus ?case
    by (meson append_eq_Cons_conv append_is_Nil_conv)
    
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  thus ?case
    by (metis Cons_eq_append_conv Nil_is_append_conv reduce_to_n_emp)
next
  case (local_trap k lls' \<Gamma>)
  thus ?case
    using reduce_to_n.local_trap
    by blast
next
  case (local_return k lls' rvs \<Gamma>)
  thus ?case
    using reduce_to_n.local_return
    by blast
qed auto

lemma callcl_context:
  assumes "((s,vs,($$*ves)@[(Callcl cl)]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "((s,vs,($$*ves)@[(Callcl cl)]) \<Down>k{\<Gamma>'} (s',vs',res))"
  using assms
proof (induction "(s,vs,($$*ves)@[(Callcl cl)])" k \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res ves rule: reduce_to_n.induct)
  case (callcl_native cl j t1s t2s ts es ves' vcs n m zs s vs k ls r i s' vs' res)
  show ?case
    using local_context[OF callcl_native(7), of \<Gamma>'] reduce_to_n.callcl_native[OF callcl_native(1,2,3,4,5,6)]
    apply (cases \<Gamma>')
    apply (auto simp add: callcl_native.hyps(9))
    done
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs k ls r i)
  show ?case
    using reduce_to_n.callcl_host_Some[OF callcl_host_Some(1,2,3,4,5,6)]
    apply (cases \<Gamma>')
    apply (auto simp add: callcl_host_Some.hyps(7))
    done
next
  case (callcl_host_None cl t1s t2s f ves vcs n m s vs k ls r i)
  thus ?case
    using reduce_to_n.callcl_host_None[OF callcl_host_None(1,2,3,4,5)]
    apply (cases \<Gamma>')
    apply (auto simp add: callcl_host_None.hyps(6))
    done
next
  case (const_value s vs es k \<Gamma> s' vs' res ves ves')
  thus ?case
    using consts_app_snoc[OF const_value(4)]
    by (metis (no_types, lifting) const_list_cons_last(2) e.distinct(3) e_type_const_unwrap is_const_list reduce_to_n.const_value)
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    by (metis (no_types, lifting) reduce_to_consts reduce_to_n_imp_reduce_to res_b.inject(1))
next
  case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
  thus ?case
    by (metis consts_app_snoc reduce_to_n.seq_nonvalue1)
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  thus ?case
    by (metis consts_app_snoc reduce_to_consts reduce_to_n_imp_reduce_to)
qed auto

lemma calln_context: "((s,vs,($$*ves)@[$(Call j)]) \<Down>k{(ls,r,i)} (s',vs',res)) = ((s,vs,($$*ves)@[$(Call j)]) \<Down>k{(ls',r',i)} (s',vs',res))"
  apply (cases k)
  apply(metis call0)
  apply (metis callcl_context calln)
  done

lemma reduce_to_length_globs:
  assumes "(s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)"
  shows "length (s.globs s) = length (s.globs s')"
  using assms
proof (induction "(s,vs,es)" "k" "\<Gamma>" "(s',vs',res)" arbitrary: s s' es res vs vs' rule: reduce_to_n.induct)
  case (set_global s i j v s' vs k ls r)
  thus ?case
    by (metis length_list_update s.ext_inject s.surjective s.update_convs(4) supdate_glob_def supdate_glob_s_def)
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs k ls r i)
  show ?case
    using host_apply_preserve_store[OF callcl_host_Some(6)] list_all2_lengthD
    unfolding store_extension.simps
    by force
qed auto

lemma reduce_to_funcs:
  assumes "(s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)"
  shows "(s.funcs s) = (s.funcs s')"
  using assms
proof (induction "(s,vs,es)" "k" "\<Gamma>" "(s',vs',res)" arbitrary: s s' es res vs vs' rule: reduce_to_n.induct)
  case (set_global s i j v s' vs k ls r)
  thus ?case
    by (metis s.ext_inject s.surjective s.update_convs(4) supdate_glob_def supdate_glob_s_def)
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs k ls r i)
  show ?case
    using host_apply_preserve_store[OF callcl_host_Some(6)] list_all2_lengthD
    unfolding store_extension.simps
    by force
qed auto

lemma local_value_trap:
  assumes "((s,vs,[Local n i vls es]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "\<exists>vrs. res = RValue vrs \<or> res = RTrap"
  using assms
proof (induction "(s,vs,[Local n i vls es])" k \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res rule: reduce_to_n.induct)
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  consider (1) "es = []" | (2) "es' = []"
    using seq_value(7)
    by (metis Cons_eq_append_conv Nil_is_append_conv)
  thus ?case
    apply cases
    apply (metis append_self_conv2 local.seq_value(1) map_append reduce_to_n_emp res_b.inject(1) seq_value.hyps(4,7))
    apply (metis reduce_to_consts reduce_to_n_imp_reduce_to self_append_conv seq_value.hyps(3))
    done
next
  case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
  thus ?case
    by (meson append_eq_Cons_conv append_is_Nil_conv)
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  thus ?case
    by (metis append_eq_Cons_conv append_is_Nil_conv reduce_to_n_emp)
qed auto

lemma callcl_value_trap:
  assumes "((s,vs,($$*ves)@[(Callcl cl)]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "\<exists>vrs. res = RValue vrs \<or> res = RTrap"
  using assms
proof (induction "(s,vs,($$*ves)@[(Callcl cl)])" k \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res ves rule: reduce_to_n.induct)
  case (callcl_native cl j t1s t2s ts es ves vcs n m zs s vs k ls r i s' vs' res)
  thus ?case
    using local_value_trap
    by blast
next
  case (seq_value s vs es k \<Gamma> s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(7)]
    apply simp
    apply (metis reduce_to_consts reduce_to_n_imp_reduce_to res_b.inject(1))
    done
next
  case (seq_nonvalue1 ves s vs es k \<Gamma> s' vs' res)
  thus ?case
    using consts_app_snoc
    by blast
next
  case (seq_nonvalue2 s vs es k \<Gamma> s' vs' res es')
  thus ?case
    by (metis consts_app_snoc reduce_to_consts reduce_to_n_imp_reduce_to)
qed auto

lemma call_value_trap:
  assumes "((s,vs,($$*ves)@[$(Call j)]) \<Down>k{\<Gamma>} (s',vs',res))"
  shows "\<exists>vrs. res = RValue vrs \<or> res = RTrap"
proof (cases k)
  case 0
  thus ?thesis
    using call0 assms
    by metis
next
  case (Suc k')
  thus ?thesis
    using assms calln callcl_value_trap
    apply (cases \<Gamma>)
    apply simp
    done
qed

lemma reduce_to_apps:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "($$*ves') @ [e] = es@es'"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
proof -
  consider (1) "es = es@es'" | (2) "\<exists>ves. es = $$* ves"
    using consts_app_snoc[of es es' ves' e] assms(2)
    by fastforce
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using assms(1)
      by (metis reduce_to_n_consts1 self_append_conv)
  next
    case 2
    thus ?thesis
      using reduce_to_n_consts1 assms(1)
      by blast
  qed
qed

lemma reduce_to_app0:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "[e] = es@es'"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
  using assms(2) reduce_to_apps[OF assms(1), of "[]"]
  by auto

lemma reduce_to_app1:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "[$C v, e] = es@es'"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
  using assms(2) reduce_to_apps[OF assms(1), of "[v]"]
  by fastforce

lemma reduce_to_app2:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "[$C v, $C v', e] = es@es'"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
  using assms(2) reduce_to_apps[OF assms(1), of "[v,v']"]
  by fastforce

lemma reduce_to_app3:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "[$C v, $C v', $C v'', e] = es@es'"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
  using assms(2) reduce_to_apps[OF assms(1), of "[v,v',v'']"]
  by fastforce

lemma reduce_to_apps_const_list:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "const_list ves'"
          "(ves') @ [e] = es@es'"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
proof -
  consider (1) "es = es@es'" | (2) "\<exists>ves. es = $$* ves"
    using consts_app_snoc[of es es' _ e]  e_type_const_conv_vs[OF assms(2)]
    by (metis assms(3))
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using assms(1)
      by (metis reduce_to_n_consts1 self_append_conv)
  next
    case 2
    thus ?thesis
      using reduce_to_n_consts1 assms(1)
      by blast
  qed
qed

lemma reduce_to_apps_const_list_v:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "const_list ves'"
          "(ves') @ [$C v, e] = es@es'"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
proof -
  obtain ves where "($$* ves) = (ves') @ [$C v]"
  proof -
    assume a1: "\<And>ves. ($$* ves) = ves' @ [$C v] \<Longrightarrow> thesis"
    obtain vvs :: "v list" where
      "\<forall>vs. ves' @ ($$* vs) = $$* vvs @ vs"
      using e_type_const_conv_vs[OF assms(2)] by moura
    then show ?thesis
      using a1 by (metis (no_types) list.simps(8) list.simps(9))
  qed
  then consider (1) "es' = []" | (2) "\<exists>ves. es = $$* ves"
    using consts_app_snoc[of es es' ves e] assms(3)
    by fastforce
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using assms(1)
      by (metis reduce_to_n_consts1 self_append_conv)
  next
    case 2
    thus ?thesis
      using reduce_to_n_consts1 assms(1)
      by blast
  qed
qed

lemma reduce_to_app_disj:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
          "[e] = es@es' \<or>
           [$C v, e] = es@es' \<or>
           [$C v, $C v', e] = es@es' \<or>
           [$C v, $C v', $C v'', e] = es@es' \<or>
           ($$*ves') @ [e] = es@es' \<or>
           (const_list ves'' \<and> (ves'') @ [e] = es@es') \<or>
           (const_list ves''' \<and> (ves''') @ [$C v''', e] = es@es')"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
  using assms
  apply safe
  using reduce_to_app0 apply (blast+)[2]
  using reduce_to_app1 apply (blast+)[2]
  using reduce_to_app2 apply (blast+)[2]
  using reduce_to_app3 apply (blast+)[2]
  using reduce_to_apps apply (blast+)[2]
  using reduce_to_apps_const_list apply (blast+)[2]
  using reduce_to_apps_const_list_v apply (blast+)[2]
  done

lemma reduce_to_app:
  assumes "(s,vs,es@es') \<Down>k{\<Gamma>} (s',vs',res)"
  shows "(\<exists>s'' vs'' rvs. ((s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue rvs)) \<and> ((s'',vs'',($$*rvs)@es') \<Down>k{\<Gamma>} (s',vs',res))) \<or>
         (((s,vs,es) \<Down>k{\<Gamma>} (s',vs',res)) \<and> (\<nexists>rvs. res = RValue rvs))"
  using assms assms
proof (induction "(s,vs,es@es')" "k" "\<Gamma>" "(s',vs',res)" arbitrary: s vs es es' s' vs' res rule: reduce_to_n.induct)
  case (emp s vs k \<Gamma>)
  thus ?case
    by fastforce
next
  case (if_false n ves s vs tf e2s k \<Gamma> s' vs' res e1s)
  thus ?case
    using reduce_to_apps_const_list_v
    by auto
next
  case (if_true n ves s vs tf e1s k \<Gamma> s' vs' res e2s)
  thus ?case
    using reduce_to_apps_const_list_v
    by auto
next
  case (tee_local v s vs i k \<Gamma> s' vs' res)
  thus ?case
    using e_type_const_unwrap[of v] reduce_to_app1
    by fast
next
  case (const_value s vs es'' k \<Gamma> s' vs' res ves es)
  consider (1) "(\<exists>ves' ves''.
                  es = ($$* ves') \<and>
                  es' = ($$* ves'') @ es'' \<and>
                  ves = ves' @ ves'')"
    | (2) "(\<exists>es_1 es_2.
              es = ($$* ves) @ es_1 \<and>
              es' = es_2 \<and>
              es'' = es_1 @ es_2)"
    using consts_app[OF const_value(4)[symmetric]]
    by blast
  thus ?case
  proof (cases)
    case 1
    thus ?thesis
      using reduce_to_n_consts1 const_value
      by blast
  next
    case 2
    then obtain es_1 es_2 where es_1_def:"es = ($$* ves) @ es_1"
                                          "es' = es_2"
                                          "es'' = es_1 @ es_2"
      by blast
    obtain s'' vs'' res' where s''_def:"((s, vs, es_1) \<Down>k{\<Gamma>} (s'', vs'', RValue res'))"
                               "(s'', vs'', ($$* res') @ es_2) \<Down>k{\<Gamma>} (s', vs', RValue res)"
      using const_value(1) const_value(2)[OF es_1_def(3)] es_1_def(3)
      by blast
    hence "((s'', vs'', ($$* res') @  es_2) \<Down>k{\<Gamma>} (s', vs', RValue res))"
      using s''_def
      by blast
    hence "((s'', vs'', ($$* ves) @ ($$* res') @  es_2) \<Down>k{\<Gamma>} (s', vs', RValue (ves@res)))"
      by (simp add: const_value.hyps(3) reduce_to_n.const_value)
    moreover
    have "(s, vs, es) \<Down>k{\<Gamma>} (s'', vs'', RValue (ves@res'))"
      using s''_def(1) es_1_def(1)
      by (simp add: const_value.hyps(3) reduce_to_n.const_value)
    ultimately
    show ?thesis
      using es_1_def(2)
      by fastforce
  qed
next
  case (seq_value s vs es'' k \<Gamma> s'' vs'' res'' es''' s' vs' res es es')
  consider (1) "\<exists>us. (es'' = es @ us \<and> us @ es''' = es')" | (2) "\<exists>us. (es'' @ us = es \<and> es''' = us @ es')"
    using seq_value(7) append_eq_append_conv2[of es'' es''' es es']
    by blast
  thus ?case
  proof (cases)
    case 1
    then obtain us where us_def:"es'' = es @ us"
                                "us @ es''' = es'"
      by blast
    consider (1) "(\<exists>s''a vs''a rvs.
                    ((s, vs, es) \<Down>k{\<Gamma>} (s''a, vs''a, RValue rvs)) \<and>
                    ((s''a, vs''a, ($$* rvs) @ us) \<Down>k{\<Gamma>} (s'', vs'', RValue res'')))"
      | (2) "((s, vs, es) \<Down>k{\<Gamma>} (s'', vs'', RValue res''))"
            "(\<nexists>rvs. RValue res'' = RValue rvs)"
      using seq_value(2)[OF us_def(1)] seq_value.hyps(1) us_def(1)
      by blast
    thus ?thesis
    proof cases
      case 1
      then obtain s''a vs''a rvs where s''a_def:
       "((s, vs, es) \<Down>k{\<Gamma>} (s''a, vs''a, RValue rvs))"
       "((s''a, vs''a, ($$* rvs) @ us) \<Down>k{\<Gamma>} (s'', vs'', RValue res''))"
        by blast
      have "(s''a, vs''a, (($$* rvs) @ us) @ es''') \<Down>k{\<Gamma>} (s', vs', res)"
        using reduce_to_n.seq_value[OF s''a_def(2) seq_value(3)]
        by (metis e_type_const_conv_vs reduce_to_consts reduce_to_n_imp_reduce_to res_b.inject(1) s''a_def(2) seq_value.hyps(3,6))
      thus ?thesis
        using s''a_def(1) us_def(2)
        by auto
    next
      case 2
      thus ?thesis
        by blast
    qed
  next
    case 2
    then obtain us where us_def:"es'' @ us = es"
                                "es''' = us @ es'"
      by blast
    consider (1) "\<exists>s''a vs''a rvs. (((s'', vs'', ($$* res'') @ us) \<Down>k{\<Gamma>} (s''a, vs''a,  RValue rvs)) \<and>
           ((s''a, vs''a, ($$* rvs) @ es') \<Down>k{\<Gamma>} (s', vs', res)))"
      | (2) "((s'', vs'', ($$* res'') @ us) \<Down>k{\<Gamma>} (s', vs', res)) \<and> (\<nexists>rvs. res = RValue rvs)"
      using seq_value(4)[of "($$* res'') @ us" "es'"] seq_value.hyps(3) us_def(2)
      by auto
    thus ?thesis
      using reduce_to_n.seq_value seq_value.hyps(1) us_def(1)
      apply cases
      apply (metis append.assoc append_Nil2 seq_value.hyps(3) seq_value.hyps(5) us_def(2))
      apply (metis append_Nil2 self_append_conv2 seq_value.hyps(3) seq_value.hyps(5) us_def(2))
      done
  qed
next
  case (seq_nonvalue1 ves s vs es'' k \<Gamma> s' vs' res)
  consider (1) "(\<exists>us. ves = es @ us \<and> us @ es'' = es')"
         | (2) "(\<exists>us. ves @ us = es \<and> es'' = us @ es')"
    using append_eq_append_conv2[of ves es'' es es'] seq_nonvalue1(7)
    by blast
  thus ?case
  proof cases
    case 1
    thus ?thesis
      by (metis (no_types, lifting) consts_app_ex(1) e_type_const_conv_vs reduce_to_n_consts1 seq_nonvalue1.hyps(1) seq_nonvalue1.prems)
  next
    case 2
    then obtain us where us_def:"ves @ us = es" "es'' = us @ es'"
      by blast
    consider
      (1) s'' vs'' rvs where "(((s, vs, us) \<Down>k{\<Gamma>} (s'', vs'', RValue rvs)) \<and> ((s'', vs'', ($$* rvs) @ es') \<Down>k{\<Gamma>} (s', vs', res)))"
    | (2) "(((s, vs, us) \<Down>k{\<Gamma>} (s', vs', res)) \<and> (\<nexists>rvs. res = RValue rvs))"
      using seq_nonvalue1(3)[OF us_def(2)] seq_nonvalue1(2) us_def(2)
      by fastforce
    thus ?thesis
    proof (cases)
      case 1
      obtain vcs where ves_is:"ves = $$* vcs"
        using e_type_const_conv_vs seq_nonvalue1.hyps(1)
        by blast
      hence "((s, vs, ves@us) \<Down>k{\<Gamma>} (s'', vs'', RValue (vcs@rvs)))"
        using "1" reduce_to_n.const_value seq_nonvalue1.hyps(5)
        by auto
      moreover
      have "((s'', vs'', ($$* (vcs@rvs)) @ es') \<Down>k{\<Gamma>} (s', vs', res))"
        using 1 reduce_to_n.seq_nonvalue1[OF _ _ seq_nonvalue1(4), of ves] ves_is
        by (metis append_assoc map_append reduce_to_n_emp seq_nonvalue1.hyps(1,4,5))
      ultimately
      show ?thesis
        using us_def(1)
        by blast
    next
      case 2
      thus ?thesis
        by (metis reduce_to_n.seq_nonvalue1 reduce_to_n_emp seq_nonvalue1.hyps(1,5) us_def(1))
    qed
  qed
next
  case (seq_nonvalue2 s vs es'' k \<Gamma> s' vs' res es''')
  thus ?case
    using append_eq_append_conv2[of es'' es''' es es']
    apply simp
    apply safe
    apply (metis append_assoc reduce_to_n.seq_nonvalue2)
    apply (meson reduce_to_n.seq_nonvalue2)
    apply (metis append.right_neutral reduce_to_n.seq_nonvalue2)
    done
next
qed (insert reduce_to_app_disj, (fast+))
(* terminal method long-running *)

end
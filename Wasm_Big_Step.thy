theory Wasm_Big_Step imports "WebAssembly/Wasm_Properties" begin

datatype res_b =
  RValue "v list" 
| RBreak nat "v list"
| RReturn "v list"
| RTrap

inductive reduce_to :: "[(s \<times> v list \<times> e list), (nat list \<times> nat option \<times> inst), (s \<times> v list \<times> res_b)] \<Rightarrow> bool" ("_ \<Down>{_} _" 60) where
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
| return:"\<lbrakk>length vs = r\<rbrakk>  \<Longrightarrow> (s,vs,($$*vcs) @ [$Return]) \<Down>{(ls,Some r,i)} (s',vs',RReturn vcs)"
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
| const_value:"\<lbrakk>(s,vs,es) \<Down>{\<Gamma>} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,($$*ves)@es) \<Down>{\<Gamma>} (s',vs',RValue (ves@res))"
| label_value:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RValue res)"
| local_value:"\<lbrakk>(s,lls,es) \<Down>{([],Some n,j)} (s',lls',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RValue res)"
  \<comment> \<open>\<open>seq congruence\<close>\<close>
| seq_value:"\<lbrakk>(s,vs,es) \<Down>{\<Gamma>} (s'',vs'',RValue res''); (s'',vs'',($$* res'') @ es') \<Down>{\<Gamma>} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,es @ es') \<Down>{\<Gamma>} (s',vs',RValue res)"
| seq_nonvalue:"\<lbrakk>const_list ves; (s,vs,es) \<Down>{\<Gamma>} (s',vs',res); \<nexists>rvs. res = RValue rvs\<rbrakk> \<Longrightarrow> (s,vs,ves @ es @ es') \<Down>{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>trap congruence\<close>\<close>
| label_trap:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RTrap)"
| local_trap:"\<lbrakk>(s,lls,es) \<Down>{([],Some n,j)} (s',lls',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RTrap)"
  \<comment> \<open>\<open>break congruence\<close>\<close>
| label_break_suc:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RBreak (Suc bn) bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RBreak bn bvs)"
| label_break_nil:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RBreak 0 bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RValue bvs)"
  \<comment> \<open>\<open>return congruence\<close>\<close>
| label_return:"\<lbrakk>(s,vs,es) \<Down>{(n#ls,r,i)} (s',vs',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>{(ls,r,i)} (s',vs',RReturn rvs)"
| local_return:"\<lbrakk>(s,lls,es) \<Down>{([],Some n,j)} (s',lls',RReturn rvs)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>{\<Gamma>} (s',vs,RValue rvs)"

inductive reduce_to_n :: "[(s \<times> v list \<times> e list), nat, (nat list \<times> nat option \<times> inst), (s \<times> v list \<times> res_b)] \<Rightarrow> bool" ("_ \<Down>_{_} _" 60) where
  \<comment> \<open>\<open>constant values\<close>\<close>
  const:"(s,vs,[$C v]) \<Down>k{\<Gamma>} (s,vs,RValue [v])"
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
| loop:"\<lbrakk>const_list ves; length ves = n; length t1s = n; length t2s = m; (s,vs,[Label n [] (ves @ ($* es))]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves @ [$(Loop (t1s _> t2s) es)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>if\<close>\<close>
| if_false:"\<lbrakk>int_eq n 0; const_list ves; (s,vs,ves@[$(Block tf e2s)]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>k{\<Gamma>} (s',vs',res)"
| if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Block tf e1s)]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(If tf e1s e2s)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br\<close>\<close>
| br:"\<lbrakk>length vcs = n; j < length ls; ls!j = n\<rbrakk> \<Longrightarrow> (s,vs,(($$*vcs) @ [$(Br j)])) \<Down>k{(ls,r,i)} (s,vs,RBreak j vcs)"
  \<comment> \<open>\<open>br_if\<close>\<close>
| br_if_false:"int_eq n 0 \<Longrightarrow> (s,vs,[$C (ConstInt32 n), $(Br_if j)]) \<Down>k{\<Gamma>} (s,vs,RValue [])"
| br_if_true:"\<lbrakk>int_ne n 0; const_list ves; (s,vs,ves@[$(Br j)]) \<Down>k{\<Gamma>} (s',vs',res) \<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 n), $(Br_if j)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>br_table\<close>\<close>
| br_table:"\<lbrakk>length js > (nat_of_int c); const_list ves; (s,vs,ves@[$(Br (js!(nat_of_int c)))]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table js j)]) \<Down>k{\<Gamma>} (s',vs',res)"
| br_table_length:"\<lbrakk>length js \<le> (nat_of_int c); const_list ves; (s,vs,ves@[$(Br j)]) \<Down>k{\<Gamma>} (s',vs',res)\<rbrakk> \<Longrightarrow> (s,vs,ves@[$C (ConstInt32 c), $(Br_table js j)]) \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>return\<close>\<close>
| return:"\<lbrakk>length vs = r\<rbrakk>  \<Longrightarrow> (s,vs,($$*vcs) @ [$Return]) \<Down>k{(ls,Some r,i)} (s',vs',RReturn vcs)"
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
| const_value:"\<lbrakk>(s,vs,es) \<Down>k{\<Gamma>} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,($$*ves)@es) \<Down>k{\<Gamma>} (s',vs',RValue (ves@res))"
| label_value:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RValue res)"
| local_value:"\<lbrakk>(s,lls,es) \<Down>k{([],Some n,j)} (s',lls',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>k{\<Gamma>} (s',vs,RValue res)"
  \<comment> \<open>\<open>seq congruence\<close>\<close>
| seq_value:"\<lbrakk>(s,vs,es) \<Down>k{\<Gamma>} (s'',vs'',RValue res''); (s'',vs'',($$* res'') @ es') \<Down>k{\<Gamma>} (s',vs',RValue res)\<rbrakk> \<Longrightarrow> (s,vs,es @ es') \<Down>k{\<Gamma>} (s',vs',RValue res)"
| seq_nonvalue:"\<lbrakk>const_list ves; (s,vs,es) \<Down>k{\<Gamma>} (s',vs',res); \<nexists>rvs. res = RValue rvs\<rbrakk> \<Longrightarrow> (s,vs,ves @ es @ es') \<Down>k{\<Gamma>} (s',vs',res)"
  \<comment> \<open>\<open>trap congruence\<close>\<close>
| label_trap:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RTrap)"
| local_trap:"\<lbrakk>(s,lls,es) \<Down>k{([],Some n,j)} (s',lls',RTrap)\<rbrakk> \<Longrightarrow> (s,vs,[Local n j lls es]) \<Down>k{\<Gamma>} (s',vs,RTrap)"
  \<comment> \<open>\<open>break congruence\<close>\<close>
| label_break_suc:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RBreak (Suc bn) bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RBreak bn bvs)"
| label_break_nil:"\<lbrakk>(s,vs,es) \<Down>k{(n#ls,r,i)} (s',vs',RBreak 0 bvs)\<rbrakk> \<Longrightarrow> (s,vs,[Label n les es]) \<Down>k{(ls,r,i)} (s',vs',RValue bvs)"
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
qed (fastforce intro: reduce_to_n.intros)+

lemma reduce_to_n_imp_reduce_to:
  assumes "(c1 \<Down>k{\<Gamma>} c2)"
  shows"(c1 \<Down>{\<Gamma>} c2)"
  using assms
  apply (induction rule: reduce_to_n.induct)
                      apply (fastforce intro: reduce_to.intros)+
  done

lemma reduce_to_iff_reduce_to_n:
  shows "(c1 \<Down>{\<Gamma>} c2) = (\<exists>k. (c1 \<Down>k{\<Gamma>} c2))"
  using reduce_to_imp_reduce_to_n reduce_to_n_imp_reduce_to
  by blast

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
  case (seq_nonvalue ves s vs es \<Gamma> s' vs' es')
  thus ?case
    using consts_app_ex
    by meson
qed auto

lemma call0: "((s,vs,($$*ves)@[$(Call j)]) \<Down>0{\<Gamma>} (s',vs',res)) \<Longrightarrow> False"
proof (induction "(s,vs,($$*ves)@[$(Call j)])" "0::nat" \<Gamma> "(s',vs',res)" arbitrary: s vs s' vs' res ves rule: reduce_to_n.induct)
  case (const_value s vs es \<Gamma> s' vs' res ves ves')
  consider (1) "es = []" | (2) "\<exists>ves'. es = ($$* ves') @ [$Call j]"
    using consts_cons_last consts_app_ex const_value(3)
    by (metis append_butlast_last_id butlast_append butlast_snoc last_appendR last_snoc)
  thus ?case
    using const_value
    apply (cases)
    apply (metis append_Nil2 b_e.distinct(505) const_list_cons_last(2) e.inject(1) e_type_const_unwrap is_const_list)
    apply blast
    done
next
  case (seq_value s vs es \<Gamma> s'' vs'' res'' es' s' vs' res)
  consider (1) "es' = []" | (2) "\<exists>ves'. es' = ($$* ves') @ [$Call j]"
    using consts_cons_last consts_app_ex seq_value(5)
    by (metis append_butlast_last_id butlast_append butlast_snoc last_appendR last_snoc)
  thus ?case
    using seq_value
    apply (cases)
    apply fastforce
    apply (metis append_assoc map_append)
    done
next
  case (seq_nonvalue ves s vs es \<Gamma> s' vs' res es' ves')
  consider (1) "ves = ($$* ves') @ [$Call j] \<and> es = [] \<and> es' = []"
         | (2) "(\<exists>ves'a ves''.
                  ves = ($$* ves'a) \<and>
                  es = ($$* ves'') @ [$Call j] \<and> es' = [] \<and>
                  ves' = ves'a @ ves'')"
         | (3) "(\<exists>ves'a ves'' ves'''.
                  ves = ($$* ves'a) \<and>
                  es = ($$* ves'') \<and>
                  es' = ($$* ves''') @ [$Call j] \<and>
                  ves' = ves'a @ ves'' @ ves''')"
    using consts_app_snoc3[OF seq_nonvalue(5)]
    by fastforce
  thus ?case
  proof (cases)
    case 1
    thus ?thesis
      using seq_nonvalue(1) const_list_cons_last(2) e_type_const_unwrap
      by auto
  next
    case 2
    thus ?thesis
      using seq_nonvalue(3)
      by blast
  next
    case 3
    thus ?thesis
      using seq_nonvalue(2,4) reduce_to_consts reduce_to_n_imp_reduce_to
      by blast
  qed
qed (fastforce intro: reduce_to_n.intros)+

lemma calln_imp: "((s,vs,($$*ves)@[$(Call j)]) \<Down>(Suc k){(ls,r,i)} (s',vs',res)) \<Longrightarrow> ((s,vs,($$*ves)@[(Callcl (sfunc s i j))]) \<Down>k{(ls,r,i)} (s',vs',res))"
proof (induction "(s,vs,($$*ves)@[$(Call j)])" "(Suc k)" "(ls,r,i)" "(s',vs',res)" arbitrary: s vs s' vs' res ves k rule: reduce_to_n.induct)
  case (const_value s vs es s' vs' res ves ves')
  consider (1) "($$* ves) = ($$* ves') @ [$Call j] \<and> es = []"
         | (2) "(\<exists>ves'a ves''.
                  ($$* ves) = ($$* ves'a) \<and>
                  es = ($$* ves'') @ [$Call j] \<and>
                  ves' = ves'a @ ves'')"
    using consts_app_snoc[OF const_value(3)]
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
      using const_value(2)[OF ves''_def(2)] reduce_to.const_value
      by (metis (no_types, lifting) append_assoc map_append reduce_to_n.const_value)
  qed
next
  case (seq_value s vs es s'' vs'' res'' es' s' vs' res)
  thus ?case
    using consts_app_snoc[OF seq_value(5)] reduce_to_consts reduce_to_n_imp_reduce_to
    apply (cases "es = ($$* ves) @ [$Call j] \<and> es' = []")
    apply fastforce
    apply blast
    done
next
  case (seq_nonvalue ves s vs es s' vs' res es' ves')
  consider (1) "ves = ($$* ves') @ [$Call j] \<and> es = [] \<and> es' = []"
         | (2) "(\<exists>ves'a ves''.
                  ves = ($$* ves'a) \<and>
                  es = ($$* ves'') @ [$Call j] \<and> es' = [] \<and>
                  ves' = ves'a @ ves'')"
         | (3) "(\<exists>ves'a ves'' ves'''.
                  ves = ($$* ves'a) \<and>
                  es = ($$* ves'') \<and>
                  es' = ($$* ves''') @ [$Call j] \<and>
                  ves' = ves'a @ ves'' @ ves''')"
    using consts_app_snoc3[OF seq_nonvalue(5)]
    by fastforce
  thus ?case
  proof (cases)
    case 1
    thus ?thesis
      using seq_nonvalue(1) const_list_cons_last(2) e_type_const_unwrap
      by auto
  next
    case 2
    then obtain ves'a ves'' where ves''_def:"ves = ($$* ves'a)"
                                            "es = ($$* ves'') @ [$Call j]"
                                            "ves' = ves'a @ ves''"
      by blast
    thus ?thesis
      using seq_nonvalue(1,4) reduce_to_n.seq_nonvalue[OF _ seq_nonvalue(3)[OF ves''_def(2)]]
      by auto
  next
    case 3
    thus ?thesis
      using seq_nonvalue(2,4) reduce_to_consts reduce_to_n_imp_reduce_to
      by blast
  qed
qed (fastforce intro: reduce_to_n.intros)+

lemma calln: "((s,vs,($$*ves)@[$(Call j)]) \<Down>(Suc k){(ls,r,i)} (s',vs',res)) = ((s,vs,($$*ves)@[(Callcl (sfunc s i j))]) \<Down>k{(ls,r,i)} (s',vs',res))"
  using calln_imp reduce_to_n.call
  by (metis is_const_list)
end
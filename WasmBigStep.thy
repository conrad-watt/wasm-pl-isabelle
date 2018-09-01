theory WasmBigStep imports "WebAssembly/Wasm" begin

datatype res_b =
  Value "v list" 
| Break nat "v list"
| Trap

inductive reduce_to :: "[(s \<times> v list \<times> e list), nat list, nat, (s \<times> v list \<times> res_b)] \<Rightarrow> bool" ("_ \<Down>{_,_} _" 60) where
"(s,vs,()) \<Down>{ls,i} (s,vs,res)"

end
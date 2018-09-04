theory Wasm_Inference_Rules imports Wasm_Assertions_Shallow begin

(* separating conjuction *)
definition sep_conj :: "'a heap_ass \<Rightarrow> 'a heap_ass \<Rightarrow> 'a heap_ass" (infixr "\<^emph>" 60) where
  "ha' \<^emph> ha'' \<equiv> \<lambda>h st. \<exists>h' h''. heap_disj h' h'' \<and> ha' h' st \<and> ha'' h'' st \<and> heap_merge h' h'' = h"

end
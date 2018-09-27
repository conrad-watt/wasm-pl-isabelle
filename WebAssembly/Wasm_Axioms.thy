section {* Host Properties *}

theory Wasm_Axioms imports Wasm begin

lemma old_mem_size_def:
  shows "mem_size m = length (Rep_mem m) div Ki64"
  unfolding mem_size_def mem_length_def
  by simp

(* these were originally axioms, but memory now has a concrete representation in the model *)
lemma mem_grow_size:
  assumes "mem_grow m n = m'"
  shows "(mem_size m + n) = mem_size m'"
  using assms Abs_mem_inverse
  unfolding mem_grow_def old_mem_size_def mem_append_def bytes_replicate_def
  by (auto simp add: Ki64_def)

lemma mem_grow_length:
  assumes "mem_grow m n = m'"
  shows "(mem_length m + (n * Ki64)) = mem_length m'"
  using assms Abs_mem_inverse
        bytes_replicate_def mem_append.rep_eq mem_length.rep_eq
  unfolding mem_grow_def old_mem_size_def mem_append_def bytes_replicate_def
  by auto

lemma mem_grow_byte_at_m:
  assumes "k < mem_length m"
  shows "byte_at (mem_grow m n) k = byte_at m k"
  using assms
  unfolding byte_at.rep_eq mem_length.rep_eq mem_grow_def mem_append.rep_eq
  by (simp add: nth_append)

lemma mem_grow_byte_at_m_n:
  assumes "k \<ge> mem_length m"
          "k < mem_length (mem_grow m n)"
  shows "byte_at (mem_grow m n) k = (0::byte)"
  using assms
  unfolding byte_at.rep_eq mem_length.rep_eq mem_grow_def mem_append.rep_eq bytes_replicate_def
  by (simp add: nth_append)

lemma load_size:
  "(load m n off l = None) = (mem_length m < (off + n + l))"
  unfolding load_def
  by (cases "n + off + l \<le> mem_length m") auto

lemma load_packed_size:
  "(load_packed sx m n off lp l = None) = (mem_length m < (off + n + lp))"
  using load_size
  unfolding load_packed_def
  by (cases "n + off + l \<le> mem_length m") auto  

lemma store_size1:
  "(store m n off v l = None) = (mem_length m < (off + n + l))"
  unfolding store_def
  by (cases "n + off + l \<le> mem_length m") auto

lemma store_size:
  assumes "(store m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms Abs_mem_inverse mem_length.rep_eq
  unfolding store_def write_bytes_def bytes_takefill_def
  by (cases "n + off + l \<le> mem_length m") (auto simp add: old_mem_size_def)

lemma store_length:
  assumes "(store m n off v l = Some m')"
  shows "mem_length m = mem_length m'"
  using assms Abs_mem_inverse mem_length.rep_eq
  unfolding store_def write_bytes_def bytes_takefill_def
  by (cases "n + off + l \<le> mem_length m") auto

lemma store_packed_size1:
  "(store_packed m n off v l = None) = (mem_length m < (off + n + l))"
  using store_size1
  unfolding store_packed_def
  by simp

lemma store_packed_size:
  assumes "(store_packed m n off v l = Some m')"
  shows "mem_size m = mem_size m'"
  using assms store_size
  unfolding store_packed_def
  by simp

axiomatization where
  wasm_deserialise_type:"typeof (wasm_deserialise bs t) = t"

axiomatization where
    host_apply_preserve_store:"host_apply s (t1s _> t2s) f vs hs = Some (s', vs') \<Longrightarrow> store_extension s s'"
and host_apply_respect_type:"list_all2 types_agree t1s vs \<Longrightarrow> host_apply s (t1s _> t2s) f vs hs = Some (s', vs') \<Longrightarrow> list_all2 types_agree t2s vs'"
end
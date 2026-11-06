theory OCX_c30_135
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2160: "oc_sub oc_b30 2160"
  by (oc_eval oc_c30_2160)

lemma oc_c30_2161: "oc_sub oc_b30 2161"
  by (oc_eval oc_c30_2161)

lemma oc_c30_2162: "oc_sub oc_b30 2162"
  by (oc_eval oc_c30_2162)

lemma oc_c30_2163: "oc_sub oc_b30 2163"
  by (oc_eval oc_c30_2163)

lemma oc_c30_2164: "oc_sub oc_b30 2164"
  by (oc_eval oc_c30_2164)

lemma oc_c30_2165: "oc_sub oc_b30 2165"
  by (oc_eval oc_c30_2165)

lemma oc_c30_2166: "oc_sub oc_b30 2166"
  by (oc_eval oc_c30_2166)

lemma oc_c30_2167: "oc_sub oc_b30 2167"
  by (oc_eval oc_c30_2167)

lemma oc_c30_2168: "oc_sub oc_b30 2168"
  by (oc_eval oc_c30_2168)

lemma oc_c30_2169: "oc_sub oc_b30 2169"
  by (oc_eval oc_c30_2169)

lemma oc_c30_2170: "oc_sub oc_b30 2170"
  by (oc_eval oc_c30_2170)

lemma oc_c30_2171: "oc_sub oc_b30 2171"
  by (oc_eval oc_c30_2171)

lemma oc_c30_2172: "oc_sub oc_b30 2172"
  by (oc_eval oc_c30_2172)

lemma oc_c30_2173: "oc_sub oc_b30 2173"
  by (oc_eval oc_c30_2173)

lemma oc_c30_2174: "oc_sub oc_b30 2174"
  by (oc_eval oc_c30_2174)

lemma oc_c30_2175: "oc_sub oc_b30 2175"
  by (oc_eval oc_c30_2175)

lemma upt_c30_135: "[2160..<2176] = [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]"
  by (simp add: upt_rec)

lemma sec_c30_135: "\<forall>j\<in>{16 * 135..<16 * 135 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 135..<16 * 135 + 16}"
  then have "j \<in> set [2160..<2176]" unfolding set_upt by simp
  then have "j \<in> set [2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175]" unfolding upt_c30_135 .
  then show "oc_sub oc_b30 j" using oc_c30_2160 oc_c30_2161 oc_c30_2162 oc_c30_2163 oc_c30_2164 oc_c30_2165 oc_c30_2166 oc_c30_2167 oc_c30_2168 oc_c30_2169 oc_c30_2170 oc_c30_2171 oc_c30_2172 oc_c30_2173 oc_c30_2174 oc_c30_2175
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

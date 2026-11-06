theory OCX_c30_138
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2208: "oc_sub oc_b30 2208"
  by (oc_eval oc_c30_2208)

lemma oc_c30_2209: "oc_sub oc_b30 2209"
  by (oc_eval oc_c30_2209)

lemma oc_c30_2210: "oc_sub oc_b30 2210"
  by (oc_eval oc_c30_2210)

lemma oc_c30_2211: "oc_sub oc_b30 2211"
  by (oc_eval oc_c30_2211)

lemma oc_c30_2212: "oc_sub oc_b30 2212"
  by (oc_eval oc_c30_2212)

lemma oc_c30_2213: "oc_sub oc_b30 2213"
  by (oc_eval oc_c30_2213)

lemma oc_c30_2214: "oc_sub oc_b30 2214"
  by (oc_eval oc_c30_2214)

lemma oc_c30_2215: "oc_sub oc_b30 2215"
  by (oc_eval oc_c30_2215)

lemma oc_c30_2216: "oc_sub oc_b30 2216"
  by (oc_eval oc_c30_2216)

lemma oc_c30_2217: "oc_sub oc_b30 2217"
  by (oc_eval oc_c30_2217)

lemma oc_c30_2218: "oc_sub oc_b30 2218"
  by (oc_eval oc_c30_2218)

lemma oc_c30_2219: "oc_sub oc_b30 2219"
  by (oc_eval oc_c30_2219)

lemma oc_c30_2220: "oc_sub oc_b30 2220"
  by (oc_eval oc_c30_2220)

lemma oc_c30_2221: "oc_sub oc_b30 2221"
  by (oc_eval oc_c30_2221)

lemma oc_c30_2222: "oc_sub oc_b30 2222"
  by (oc_eval oc_c30_2222)

lemma oc_c30_2223: "oc_sub oc_b30 2223"
  by (oc_eval oc_c30_2223)

lemma upt_c30_138: "[2208..<2224] = [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]"
  by (simp add: upt_rec)

lemma sec_c30_138: "\<forall>j\<in>{16 * 138..<16 * 138 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 138..<16 * 138 + 16}"
  then have "j \<in> set [2208..<2224]" unfolding set_upt by simp
  then have "j \<in> set [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]" unfolding upt_c30_138 .
  then show "oc_sub oc_b30 j" using oc_c30_2208 oc_c30_2209 oc_c30_2210 oc_c30_2211 oc_c30_2212 oc_c30_2213 oc_c30_2214 oc_c30_2215 oc_c30_2216 oc_c30_2217 oc_c30_2218 oc_c30_2219 oc_c30_2220 oc_c30_2221 oc_c30_2222 oc_c30_2223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

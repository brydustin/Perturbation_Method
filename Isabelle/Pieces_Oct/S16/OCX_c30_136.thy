theory OCX_c30_136
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2176: "oc_sub oc_b30 2176"
  by (oc_eval oc_c30_2176)

lemma oc_c30_2177: "oc_sub oc_b30 2177"
  by (oc_eval oc_c30_2177)

lemma oc_c30_2178: "oc_sub oc_b30 2178"
  by (oc_eval oc_c30_2178)

lemma oc_c30_2179: "oc_sub oc_b30 2179"
  by (oc_eval oc_c30_2179)

lemma oc_c30_2180: "oc_sub oc_b30 2180"
  by (oc_eval oc_c30_2180)

lemma oc_c30_2181: "oc_sub oc_b30 2181"
  by (oc_eval oc_c30_2181)

lemma oc_c30_2182: "oc_sub oc_b30 2182"
  by (oc_eval oc_c30_2182)

lemma oc_c30_2183: "oc_sub oc_b30 2183"
  by (oc_eval oc_c30_2183)

lemma oc_c30_2184: "oc_sub oc_b30 2184"
  by (oc_eval oc_c30_2184)

lemma oc_c30_2185: "oc_sub oc_b30 2185"
  by (oc_eval oc_c30_2185)

lemma oc_c30_2186: "oc_sub oc_b30 2186"
  by (oc_eval oc_c30_2186)

lemma oc_c30_2187: "oc_sub oc_b30 2187"
  by (oc_eval oc_c30_2187)

lemma oc_c30_2188: "oc_sub oc_b30 2188"
  by (oc_eval oc_c30_2188)

lemma oc_c30_2189: "oc_sub oc_b30 2189"
  by (oc_eval oc_c30_2189)

lemma oc_c30_2190: "oc_sub oc_b30 2190"
  by (oc_eval oc_c30_2190)

lemma oc_c30_2191: "oc_sub oc_b30 2191"
  by (oc_eval oc_c30_2191)

lemma upt_c30_136: "[2176..<2192] = [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]"
  by (simp add: upt_rec)

lemma sec_c30_136: "\<forall>j\<in>{16 * 136..<16 * 136 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 136..<16 * 136 + 16}"
  then have "j \<in> set [2176..<2192]" unfolding set_upt by simp
  then have "j \<in> set [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]" unfolding upt_c30_136 .
  then show "oc_sub oc_b30 j" using oc_c30_2176 oc_c30_2177 oc_c30_2178 oc_c30_2179 oc_c30_2180 oc_c30_2181 oc_c30_2182 oc_c30_2183 oc_c30_2184 oc_c30_2185 oc_c30_2186 oc_c30_2187 oc_c30_2188 oc_c30_2189 oc_c30_2190 oc_c30_2191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

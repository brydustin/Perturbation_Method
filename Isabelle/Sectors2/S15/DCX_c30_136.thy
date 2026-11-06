theory DCX_c30_136
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2176: "dc_sub dc_b30 2176"
  by (dc_eval dc_c30_2176)

lemma dc_c30_2177: "dc_sub dc_b30 2177"
  by (dc_eval dc_c30_2177)

lemma dc_c30_2178: "dc_sub dc_b30 2178"
  by (dc_eval dc_c30_2178)

lemma dc_c30_2179: "dc_sub dc_b30 2179"
  by (dc_eval dc_c30_2179)

lemma dc_c30_2180: "dc_sub dc_b30 2180"
  by (dc_eval dc_c30_2180)

lemma dc_c30_2181: "dc_sub dc_b30 2181"
  by (dc_eval dc_c30_2181)

lemma dc_c30_2182: "dc_sub dc_b30 2182"
  by (dc_eval dc_c30_2182)

lemma dc_c30_2183: "dc_sub dc_b30 2183"
  by (dc_eval dc_c30_2183)

lemma dc_c30_2184: "dc_sub dc_b30 2184"
  by (dc_eval dc_c30_2184)

lemma dc_c30_2185: "dc_sub dc_b30 2185"
  by (dc_eval dc_c30_2185)

lemma dc_c30_2186: "dc_sub dc_b30 2186"
  by (dc_eval dc_c30_2186)

lemma dc_c30_2187: "dc_sub dc_b30 2187"
  by (dc_eval dc_c30_2187)

lemma dc_c30_2188: "dc_sub dc_b30 2188"
  by (dc_eval dc_c30_2188)

lemma dc_c30_2189: "dc_sub dc_b30 2189"
  by (dc_eval dc_c30_2189)

lemma dc_c30_2190: "dc_sub dc_b30 2190"
  by (dc_eval dc_c30_2190)

lemma dc_c30_2191: "dc_sub dc_b30 2191"
  by (dc_eval dc_c30_2191)

lemma upt_c30_136: "[2176..<2192] = [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]"
  by (simp add: upt_rec)

lemma sec_c30_136: "\<forall>j\<in>{16 * 136..<16 * 136 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 136..<16 * 136 + 16}"
  then have "j \<in> set [2176..<2192]" unfolding set_upt by simp
  then have "j \<in> set [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]" unfolding upt_c30_136 .
  then show "dc_sub dc_b30 j" using dc_c30_2176 dc_c30_2177 dc_c30_2178 dc_c30_2179 dc_c30_2180 dc_c30_2181 dc_c30_2182 dc_c30_2183 dc_c30_2184 dc_c30_2185 dc_c30_2186 dc_c30_2187 dc_c30_2188 dc_c30_2189 dc_c30_2190 dc_c30_2191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory OCX_nc_136
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2176: "oc_sub None 2176"
  by (oc_eval oc_nc_2176)

lemma oc_nc_2177: "oc_sub None 2177"
  by (oc_eval oc_nc_2177)

lemma oc_nc_2178: "oc_sub None 2178"
  by (oc_eval oc_nc_2178)

lemma oc_nc_2179: "oc_sub None 2179"
  by (oc_eval oc_nc_2179)

lemma oc_nc_2180: "oc_sub None 2180"
  by (oc_eval oc_nc_2180)

lemma oc_nc_2181: "oc_sub None 2181"
  by (oc_eval oc_nc_2181)

lemma oc_nc_2182: "oc_sub None 2182"
  by (oc_eval oc_nc_2182)

lemma oc_nc_2183: "oc_sub None 2183"
  by (oc_eval oc_nc_2183)

lemma oc_nc_2184: "oc_sub None 2184"
  by (oc_eval oc_nc_2184)

lemma oc_nc_2185: "oc_sub None 2185"
  by (oc_eval oc_nc_2185)

lemma oc_nc_2186: "oc_sub None 2186"
  by (oc_eval oc_nc_2186)

lemma oc_nc_2187: "oc_sub None 2187"
  by (oc_eval oc_nc_2187)

lemma oc_nc_2188: "oc_sub None 2188"
  by (oc_eval oc_nc_2188)

lemma oc_nc_2189: "oc_sub None 2189"
  by (oc_eval oc_nc_2189)

lemma oc_nc_2190: "oc_sub None 2190"
  by (oc_eval oc_nc_2190)

lemma oc_nc_2191: "oc_sub None 2191"
  by (oc_eval oc_nc_2191)

lemma upt_nc_136: "[2176..<2192] = [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]"
  by (simp add: upt_rec)

lemma sec_nc_136: "\<forall>j\<in>{16 * 136..<16 * 136 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 136..<16 * 136 + 16}"
  then have "j \<in> set [2176..<2192]" unfolding set_upt by simp
  then have "j \<in> set [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]" unfolding upt_nc_136 .
  then show "oc_sub None j" using oc_nc_2176 oc_nc_2177 oc_nc_2178 oc_nc_2179 oc_nc_2180 oc_nc_2181 oc_nc_2182 oc_nc_2183 oc_nc_2184 oc_nc_2185 oc_nc_2186 oc_nc_2187 oc_nc_2188 oc_nc_2189 oc_nc_2190 oc_nc_2191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

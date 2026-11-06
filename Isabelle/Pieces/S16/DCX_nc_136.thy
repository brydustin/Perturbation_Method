theory DCX_nc_136
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2176: "dc_sub None 2176"
  by (dc_eval dc_nc_2176)

lemma dc_nc_2177: "dc_sub None 2177"
  by (dc_eval dc_nc_2177)

lemma dc_nc_2178: "dc_sub None 2178"
  by (dc_eval dc_nc_2178)

lemma dc_nc_2179: "dc_sub None 2179"
  by (dc_eval dc_nc_2179)

lemma dc_nc_2180: "dc_sub None 2180"
  by (dc_eval dc_nc_2180)

lemma dc_nc_2181: "dc_sub None 2181"
  by (dc_eval dc_nc_2181)

lemma dc_nc_2182: "dc_sub None 2182"
  by (dc_eval dc_nc_2182)

lemma dc_nc_2183: "dc_sub None 2183"
  by (dc_eval dc_nc_2183)

lemma dc_nc_2184: "dc_sub None 2184"
  by (dc_eval dc_nc_2184)

lemma dc_nc_2185: "dc_sub None 2185"
  by (dc_eval dc_nc_2185)

lemma dc_nc_2186: "dc_sub None 2186"
  by (dc_eval dc_nc_2186)

lemma dc_nc_2187: "dc_sub None 2187"
  by (dc_eval dc_nc_2187)

lemma dc_nc_2188: "dc_sub None 2188"
  by (dc_eval dc_nc_2188)

lemma dc_nc_2189: "dc_sub None 2189"
  by (dc_eval dc_nc_2189)

lemma dc_nc_2190: "dc_sub None 2190"
  by (dc_eval dc_nc_2190)

lemma dc_nc_2191: "dc_sub None 2191"
  by (dc_eval dc_nc_2191)

lemma upt_nc_136: "[2176..<2192] = [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]"
  by (simp add: upt_rec)

lemma sec_nc_136: "\<forall>j\<in>{16 * 136..<16 * 136 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 136..<16 * 136 + 16}"
  then have "j \<in> set [2176..<2192]" unfolding set_upt by simp
  then have "j \<in> set [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]" unfolding upt_nc_136 .
  then show "dc_sub None j" using dc_nc_2176 dc_nc_2177 dc_nc_2178 dc_nc_2179 dc_nc_2180 dc_nc_2181 dc_nc_2182 dc_nc_2183 dc_nc_2184 dc_nc_2185 dc_nc_2186 dc_nc_2187 dc_nc_2188 dc_nc_2189 dc_nc_2190 dc_nc_2191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory GDCX_nc_136
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2176: "gdc_sub None 2176"
  by (gdc_eval gdc_nc_2176)

lemma gdc_nc_2177: "gdc_sub None 2177"
  by (gdc_eval gdc_nc_2177)

lemma gdc_nc_2178: "gdc_sub None 2178"
  by (gdc_eval gdc_nc_2178)

lemma gdc_nc_2179: "gdc_sub None 2179"
  by (gdc_eval gdc_nc_2179)

lemma gdc_nc_2180: "gdc_sub None 2180"
  by (gdc_eval gdc_nc_2180)

lemma gdc_nc_2181: "gdc_sub None 2181"
  by (gdc_eval gdc_nc_2181)

lemma gdc_nc_2182: "gdc_sub None 2182"
  by (gdc_eval gdc_nc_2182)

lemma gdc_nc_2183: "gdc_sub None 2183"
  by (gdc_eval gdc_nc_2183)

lemma gdc_nc_2184: "gdc_sub None 2184"
  by (gdc_eval gdc_nc_2184)

lemma gdc_nc_2185: "gdc_sub None 2185"
  by (gdc_eval gdc_nc_2185)

lemma gdc_nc_2186: "gdc_sub None 2186"
  by (gdc_eval gdc_nc_2186)

lemma gdc_nc_2187: "gdc_sub None 2187"
  by (gdc_eval gdc_nc_2187)

lemma gdc_nc_2188: "gdc_sub None 2188"
  by (gdc_eval gdc_nc_2188)

lemma gdc_nc_2189: "gdc_sub None 2189"
  by (gdc_eval gdc_nc_2189)

lemma gdc_nc_2190: "gdc_sub None 2190"
  by (gdc_eval gdc_nc_2190)

lemma gdc_nc_2191: "gdc_sub None 2191"
  by (gdc_eval gdc_nc_2191)

lemma gupt_nc_136: "[2176..<2192] = [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]"
  by (simp add: upt_rec)

lemma gsec_nc_136: "\<forall>j\<in>{16 * 136..<16 * 136 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 136..<16 * 136 + 16}"
  then have "j \<in> set [2176..<2192]" unfolding set_upt by simp
  then have "j \<in> set [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]" unfolding gupt_nc_136 .
  then show "gdc_sub None j" using gdc_nc_2176 gdc_nc_2177 gdc_nc_2178 gdc_nc_2179 gdc_nc_2180 gdc_nc_2181 gdc_nc_2182 gdc_nc_2183 gdc_nc_2184 gdc_nc_2185 gdc_nc_2186 gdc_nc_2187 gdc_nc_2188 gdc_nc_2189 gdc_nc_2190 gdc_nc_2191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

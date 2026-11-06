theory GOCX_nc_136
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2176: "goc_sub None 2176"
  by (goc_eval goc_nc_2176)

lemma goc_nc_2177: "goc_sub None 2177"
  by (goc_eval goc_nc_2177)

lemma goc_nc_2178: "goc_sub None 2178"
  by (goc_eval goc_nc_2178)

lemma goc_nc_2179: "goc_sub None 2179"
  by (goc_eval goc_nc_2179)

lemma goc_nc_2180: "goc_sub None 2180"
  by (goc_eval goc_nc_2180)

lemma goc_nc_2181: "goc_sub None 2181"
  by (goc_eval goc_nc_2181)

lemma goc_nc_2182: "goc_sub None 2182"
  by (goc_eval goc_nc_2182)

lemma goc_nc_2183: "goc_sub None 2183"
  by (goc_eval goc_nc_2183)

lemma goc_nc_2184: "goc_sub None 2184"
  by (goc_eval goc_nc_2184)

lemma goc_nc_2185: "goc_sub None 2185"
  by (goc_eval goc_nc_2185)

lemma goc_nc_2186: "goc_sub None 2186"
  by (goc_eval goc_nc_2186)

lemma goc_nc_2187: "goc_sub None 2187"
  by (goc_eval goc_nc_2187)

lemma goc_nc_2188: "goc_sub None 2188"
  by (goc_eval goc_nc_2188)

lemma goc_nc_2189: "goc_sub None 2189"
  by (goc_eval goc_nc_2189)

lemma goc_nc_2190: "goc_sub None 2190"
  by (goc_eval goc_nc_2190)

lemma goc_nc_2191: "goc_sub None 2191"
  by (goc_eval goc_nc_2191)

lemma gupt_nc_136: "[2176..<2192] = [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]"
  by (simp add: upt_rec)

lemma gsec_nc_136: "\<forall>j\<in>{16 * 136..<16 * 136 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 136..<16 * 136 + 16}"
  then have "j \<in> set [2176..<2192]" unfolding set_upt by simp
  then have "j \<in> set [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191]" unfolding gupt_nc_136 .
  then show "goc_sub None j" using goc_nc_2176 goc_nc_2177 goc_nc_2178 goc_nc_2179 goc_nc_2180 goc_nc_2181 goc_nc_2182 goc_nc_2183 goc_nc_2184 goc_nc_2185 goc_nc_2186 goc_nc_2187 goc_nc_2188 goc_nc_2189 goc_nc_2190 goc_nc_2191
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

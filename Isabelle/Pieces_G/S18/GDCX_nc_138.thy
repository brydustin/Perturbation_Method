theory GDCX_nc_138
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2208: "gdc_sub None 2208"
  by (gdc_eval gdc_nc_2208)

lemma gdc_nc_2209: "gdc_sub None 2209"
  by (gdc_eval gdc_nc_2209)

lemma gdc_nc_2210: "gdc_sub None 2210"
  by (gdc_eval gdc_nc_2210)

lemma gdc_nc_2211: "gdc_sub None 2211"
  by (gdc_eval gdc_nc_2211)

lemma gdc_nc_2212: "gdc_sub None 2212"
  by (gdc_eval gdc_nc_2212)

lemma gdc_nc_2213: "gdc_sub None 2213"
  by (gdc_eval gdc_nc_2213)

lemma gdc_nc_2214: "gdc_sub None 2214"
  by (gdc_eval gdc_nc_2214)

lemma gdc_nc_2215: "gdc_sub None 2215"
  by (gdc_eval gdc_nc_2215)

lemma gdc_nc_2216: "gdc_sub None 2216"
  by (gdc_eval gdc_nc_2216)

lemma gdc_nc_2217: "gdc_sub None 2217"
  by (gdc_eval gdc_nc_2217)

lemma gdc_nc_2218: "gdc_sub None 2218"
  by (gdc_eval gdc_nc_2218)

lemma gdc_nc_2219: "gdc_sub None 2219"
  by (gdc_eval gdc_nc_2219)

lemma gdc_nc_2220: "gdc_sub None 2220"
  by (gdc_eval gdc_nc_2220)

lemma gdc_nc_2221: "gdc_sub None 2221"
  by (gdc_eval gdc_nc_2221)

lemma gdc_nc_2222: "gdc_sub None 2222"
  by (gdc_eval gdc_nc_2222)

lemma gdc_nc_2223: "gdc_sub None 2223"
  by (gdc_eval gdc_nc_2223)

lemma gupt_nc_138: "[2208..<2224] = [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]"
  by (simp add: upt_rec)

lemma gsec_nc_138: "\<forall>j\<in>{16 * 138..<16 * 138 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 138..<16 * 138 + 16}"
  then have "j \<in> set [2208..<2224]" unfolding set_upt by simp
  then have "j \<in> set [2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223]" unfolding gupt_nc_138 .
  then show "gdc_sub None j" using gdc_nc_2208 gdc_nc_2209 gdc_nc_2210 gdc_nc_2211 gdc_nc_2212 gdc_nc_2213 gdc_nc_2214 gdc_nc_2215 gdc_nc_2216 gdc_nc_2217 gdc_nc_2218 gdc_nc_2219 gdc_nc_2220 gdc_nc_2221 gdc_nc_2222 gdc_nc_2223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

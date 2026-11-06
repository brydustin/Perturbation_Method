theory GDCX_nc_140
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2240: "gdc_sub None 2240"
  by (gdc_eval gdc_nc_2240)

lemma gdc_nc_2241: "gdc_sub None 2241"
  by (gdc_eval gdc_nc_2241)

lemma gdc_nc_2242: "gdc_sub None 2242"
  by (gdc_eval gdc_nc_2242)

lemma gdc_nc_2243: "gdc_sub None 2243"
  by (gdc_eval gdc_nc_2243)

lemma gdc_nc_2244: "gdc_sub None 2244"
  by (gdc_eval gdc_nc_2244)

lemma gdc_nc_2245: "gdc_sub None 2245"
  by (gdc_eval gdc_nc_2245)

lemma gdc_nc_2246: "gdc_sub None 2246"
  by (gdc_eval gdc_nc_2246)

lemma gdc_nc_2247: "gdc_sub None 2247"
  by (gdc_eval gdc_nc_2247)

lemma gdc_nc_2248: "gdc_sub None 2248"
  by (gdc_eval gdc_nc_2248)

lemma gdc_nc_2249: "gdc_sub None 2249"
  by (gdc_eval gdc_nc_2249)

lemma gdc_nc_2250: "gdc_sub None 2250"
  by (gdc_eval gdc_nc_2250)

lemma gdc_nc_2251: "gdc_sub None 2251"
  by (gdc_eval gdc_nc_2251)

lemma gdc_nc_2252: "gdc_sub None 2252"
  by (gdc_eval gdc_nc_2252)

lemma gdc_nc_2253: "gdc_sub None 2253"
  by (gdc_eval gdc_nc_2253)

lemma gdc_nc_2254: "gdc_sub None 2254"
  by (gdc_eval gdc_nc_2254)

lemma gdc_nc_2255: "gdc_sub None 2255"
  by (gdc_eval gdc_nc_2255)

lemma gupt_nc_140: "[2240..<2256] = [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]"
  by (simp add: upt_rec)

lemma gsec_nc_140: "\<forall>j\<in>{16 * 140..<16 * 140 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 140..<16 * 140 + 16}"
  then have "j \<in> set [2240..<2256]" unfolding set_upt by simp
  then have "j \<in> set [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]" unfolding gupt_nc_140 .
  then show "gdc_sub None j" using gdc_nc_2240 gdc_nc_2241 gdc_nc_2242 gdc_nc_2243 gdc_nc_2244 gdc_nc_2245 gdc_nc_2246 gdc_nc_2247 gdc_nc_2248 gdc_nc_2249 gdc_nc_2250 gdc_nc_2251 gdc_nc_2252 gdc_nc_2253 gdc_nc_2254 gdc_nc_2255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

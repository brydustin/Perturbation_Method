theory GDCX_nc_145
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2320: "gdc_sub None 2320"
  by (gdc_eval gdc_nc_2320)

lemma gdc_nc_2321: "gdc_sub None 2321"
  by (gdc_eval gdc_nc_2321)

lemma gdc_nc_2322: "gdc_sub None 2322"
  by (gdc_eval gdc_nc_2322)

lemma gdc_nc_2323: "gdc_sub None 2323"
  by (gdc_eval gdc_nc_2323)

lemma gdc_nc_2324: "gdc_sub None 2324"
  by (gdc_eval gdc_nc_2324)

lemma gdc_nc_2325: "gdc_sub None 2325"
  by (gdc_eval gdc_nc_2325)

lemma gdc_nc_2326: "gdc_sub None 2326"
  by (gdc_eval gdc_nc_2326)

lemma gdc_nc_2327: "gdc_sub None 2327"
  by (gdc_eval gdc_nc_2327)

lemma gdc_nc_2328: "gdc_sub None 2328"
  by (gdc_eval gdc_nc_2328)

lemma gdc_nc_2329: "gdc_sub None 2329"
  by (gdc_eval gdc_nc_2329)

lemma gdc_nc_2330: "gdc_sub None 2330"
  by (gdc_eval gdc_nc_2330)

lemma gdc_nc_2331: "gdc_sub None 2331"
  by (gdc_eval gdc_nc_2331)

lemma gdc_nc_2332: "gdc_sub None 2332"
  by (gdc_eval gdc_nc_2332)

lemma gdc_nc_2333: "gdc_sub None 2333"
  by (gdc_eval gdc_nc_2333)

lemma gdc_nc_2334: "gdc_sub None 2334"
  by (gdc_eval gdc_nc_2334)

lemma gdc_nc_2335: "gdc_sub None 2335"
  by (gdc_eval gdc_nc_2335)

lemma gupt_nc_145: "[2320..<2336] = [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]"
  by (simp add: upt_rec)

lemma gsec_nc_145: "\<forall>j\<in>{16 * 145..<16 * 145 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 145..<16 * 145 + 16}"
  then have "j \<in> set [2320..<2336]" unfolding set_upt by simp
  then have "j \<in> set [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]" unfolding gupt_nc_145 .
  then show "gdc_sub None j" using gdc_nc_2320 gdc_nc_2321 gdc_nc_2322 gdc_nc_2323 gdc_nc_2324 gdc_nc_2325 gdc_nc_2326 gdc_nc_2327 gdc_nc_2328 gdc_nc_2329 gdc_nc_2330 gdc_nc_2331 gdc_nc_2332 gdc_nc_2333 gdc_nc_2334 gdc_nc_2335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

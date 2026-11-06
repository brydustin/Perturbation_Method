theory DCX_nc_145
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2320: "dc_sub None 2320"
  by (dc_eval dc_nc_2320)

lemma dc_nc_2321: "dc_sub None 2321"
  by (dc_eval dc_nc_2321)

lemma dc_nc_2322: "dc_sub None 2322"
  by (dc_eval dc_nc_2322)

lemma dc_nc_2323: "dc_sub None 2323"
  by (dc_eval dc_nc_2323)

lemma dc_nc_2324: "dc_sub None 2324"
  by (dc_eval dc_nc_2324)

lemma dc_nc_2325: "dc_sub None 2325"
  by (dc_eval dc_nc_2325)

lemma dc_nc_2326: "dc_sub None 2326"
  by (dc_eval dc_nc_2326)

lemma dc_nc_2327: "dc_sub None 2327"
  by (dc_eval dc_nc_2327)

lemma dc_nc_2328: "dc_sub None 2328"
  by (dc_eval dc_nc_2328)

lemma dc_nc_2329: "dc_sub None 2329"
  by (dc_eval dc_nc_2329)

lemma dc_nc_2330: "dc_sub None 2330"
  by (dc_eval dc_nc_2330)

lemma dc_nc_2331: "dc_sub None 2331"
  by (dc_eval dc_nc_2331)

lemma dc_nc_2332: "dc_sub None 2332"
  by (dc_eval dc_nc_2332)

lemma dc_nc_2333: "dc_sub None 2333"
  by (dc_eval dc_nc_2333)

lemma dc_nc_2334: "dc_sub None 2334"
  by (dc_eval dc_nc_2334)

lemma dc_nc_2335: "dc_sub None 2335"
  by (dc_eval dc_nc_2335)

lemma upt_nc_145: "[2320..<2336] = [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]"
  by (simp add: upt_rec)

lemma sec_nc_145: "\<forall>j\<in>{16 * 145..<16 * 145 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 145..<16 * 145 + 16}"
  then have "j \<in> set [2320..<2336]" unfolding set_upt by simp
  then have "j \<in> set [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]" unfolding upt_nc_145 .
  then show "dc_sub None j" using dc_nc_2320 dc_nc_2321 dc_nc_2322 dc_nc_2323 dc_nc_2324 dc_nc_2325 dc_nc_2326 dc_nc_2327 dc_nc_2328 dc_nc_2329 dc_nc_2330 dc_nc_2331 dc_nc_2332 dc_nc_2333 dc_nc_2334 dc_nc_2335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

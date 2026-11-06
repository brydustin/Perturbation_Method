theory DCX_c30_145
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_2320: "dc_sub dc_b30 2320"
  by (dc_eval dc_c30_2320)

lemma dc_c30_2321: "dc_sub dc_b30 2321"
  by (dc_eval dc_c30_2321)

lemma dc_c30_2322: "dc_sub dc_b30 2322"
  by (dc_eval dc_c30_2322)

lemma dc_c30_2323: "dc_sub dc_b30 2323"
  by (dc_eval dc_c30_2323)

lemma dc_c30_2324: "dc_sub dc_b30 2324"
  by (dc_eval dc_c30_2324)

lemma dc_c30_2325: "dc_sub dc_b30 2325"
  by (dc_eval dc_c30_2325)

lemma dc_c30_2326: "dc_sub dc_b30 2326"
  by (dc_eval dc_c30_2326)

lemma dc_c30_2327: "dc_sub dc_b30 2327"
  by (dc_eval dc_c30_2327)

lemma dc_c30_2328: "dc_sub dc_b30 2328"
  by (dc_eval dc_c30_2328)

lemma dc_c30_2329: "dc_sub dc_b30 2329"
  by (dc_eval dc_c30_2329)

lemma dc_c30_2330: "dc_sub dc_b30 2330"
  by (dc_eval dc_c30_2330)

lemma dc_c30_2331: "dc_sub dc_b30 2331"
  by (dc_eval dc_c30_2331)

lemma dc_c30_2332: "dc_sub dc_b30 2332"
  by (dc_eval dc_c30_2332)

lemma dc_c30_2333: "dc_sub dc_b30 2333"
  by (dc_eval dc_c30_2333)

lemma dc_c30_2334: "dc_sub dc_b30 2334"
  by (dc_eval dc_c30_2334)

lemma dc_c30_2335: "dc_sub dc_b30 2335"
  by (dc_eval dc_c30_2335)

lemma upt_c30_145: "[2320..<2336] = [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]"
  by (simp add: upt_rec)

lemma sec_c30_145: "\<forall>j\<in>{16 * 145..<16 * 145 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 145..<16 * 145 + 16}"
  then have "j \<in> set [2320..<2336]" unfolding set_upt by simp
  then have "j \<in> set [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]" unfolding upt_c30_145 .
  then show "dc_sub dc_b30 j" using dc_c30_2320 dc_c30_2321 dc_c30_2322 dc_c30_2323 dc_c30_2324 dc_c30_2325 dc_c30_2326 dc_c30_2327 dc_c30_2328 dc_c30_2329 dc_c30_2330 dc_c30_2331 dc_c30_2332 dc_c30_2333 dc_c30_2334 dc_c30_2335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

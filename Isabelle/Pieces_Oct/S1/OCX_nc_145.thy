theory OCX_nc_145
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2320: "oc_sub None 2320"
  by (oc_eval oc_nc_2320)

lemma oc_nc_2321: "oc_sub None 2321"
  by (oc_eval oc_nc_2321)

lemma oc_nc_2322: "oc_sub None 2322"
  by (oc_eval oc_nc_2322)

lemma oc_nc_2323: "oc_sub None 2323"
  by (oc_eval oc_nc_2323)

lemma oc_nc_2324: "oc_sub None 2324"
  by (oc_eval oc_nc_2324)

lemma oc_nc_2325: "oc_sub None 2325"
  by (oc_eval oc_nc_2325)

lemma oc_nc_2326: "oc_sub None 2326"
  by (oc_eval oc_nc_2326)

lemma oc_nc_2327: "oc_sub None 2327"
  by (oc_eval oc_nc_2327)

lemma oc_nc_2328: "oc_sub None 2328"
  by (oc_eval oc_nc_2328)

lemma oc_nc_2329: "oc_sub None 2329"
  by (oc_eval oc_nc_2329)

lemma oc_nc_2330: "oc_sub None 2330"
  by (oc_eval oc_nc_2330)

lemma oc_nc_2331: "oc_sub None 2331"
  by (oc_eval oc_nc_2331)

lemma oc_nc_2332: "oc_sub None 2332"
  by (oc_eval oc_nc_2332)

lemma oc_nc_2333: "oc_sub None 2333"
  by (oc_eval oc_nc_2333)

lemma oc_nc_2334: "oc_sub None 2334"
  by (oc_eval oc_nc_2334)

lemma oc_nc_2335: "oc_sub None 2335"
  by (oc_eval oc_nc_2335)

lemma upt_nc_145: "[2320..<2336] = [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]"
  by (simp add: upt_rec)

lemma sec_nc_145: "\<forall>j\<in>{16 * 145..<16 * 145 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 145..<16 * 145 + 16}"
  then have "j \<in> set [2320..<2336]" unfolding set_upt by simp
  then have "j \<in> set [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]" unfolding upt_nc_145 .
  then show "oc_sub None j" using oc_nc_2320 oc_nc_2321 oc_nc_2322 oc_nc_2323 oc_nc_2324 oc_nc_2325 oc_nc_2326 oc_nc_2327 oc_nc_2328 oc_nc_2329 oc_nc_2330 oc_nc_2331 oc_nc_2332 oc_nc_2333 oc_nc_2334 oc_nc_2335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory GOCX_nc_145
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2320: "goc_sub None 2320"
  by (goc_eval goc_nc_2320)

lemma goc_nc_2321: "goc_sub None 2321"
  by (goc_eval goc_nc_2321)

lemma goc_nc_2322: "goc_sub None 2322"
  by (goc_eval goc_nc_2322)

lemma goc_nc_2323: "goc_sub None 2323"
  by (goc_eval goc_nc_2323)

lemma goc_nc_2324: "goc_sub None 2324"
  by (goc_eval goc_nc_2324)

lemma goc_nc_2325: "goc_sub None 2325"
  by (goc_eval goc_nc_2325)

lemma goc_nc_2326: "goc_sub None 2326"
  by (goc_eval goc_nc_2326)

lemma goc_nc_2327: "goc_sub None 2327"
  by (goc_eval goc_nc_2327)

lemma goc_nc_2328: "goc_sub None 2328"
  by (goc_eval goc_nc_2328)

lemma goc_nc_2329: "goc_sub None 2329"
  by (goc_eval goc_nc_2329)

lemma goc_nc_2330: "goc_sub None 2330"
  by (goc_eval goc_nc_2330)

lemma goc_nc_2331: "goc_sub None 2331"
  by (goc_eval goc_nc_2331)

lemma goc_nc_2332: "goc_sub None 2332"
  by (goc_eval goc_nc_2332)

lemma goc_nc_2333: "goc_sub None 2333"
  by (goc_eval goc_nc_2333)

lemma goc_nc_2334: "goc_sub None 2334"
  by (goc_eval goc_nc_2334)

lemma goc_nc_2335: "goc_sub None 2335"
  by (goc_eval goc_nc_2335)

lemma gupt_nc_145: "[2320..<2336] = [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]"
  by (simp add: upt_rec)

lemma gsec_nc_145: "\<forall>j\<in>{16 * 145..<16 * 145 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 145..<16 * 145 + 16}"
  then have "j \<in> set [2320..<2336]" unfolding set_upt by simp
  then have "j \<in> set [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]" unfolding gupt_nc_145 .
  then show "goc_sub None j" using goc_nc_2320 goc_nc_2321 goc_nc_2322 goc_nc_2323 goc_nc_2324 goc_nc_2325 goc_nc_2326 goc_nc_2327 goc_nc_2328 goc_nc_2329 goc_nc_2330 goc_nc_2331 goc_nc_2332 goc_nc_2333 goc_nc_2334 goc_nc_2335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

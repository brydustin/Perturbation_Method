theory OCX_c30_145
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_2320: "oc_sub oc_b30 2320"
  by (oc_eval oc_c30_2320)

lemma oc_c30_2321: "oc_sub oc_b30 2321"
  by (oc_eval oc_c30_2321)

lemma oc_c30_2322: "oc_sub oc_b30 2322"
  by (oc_eval oc_c30_2322)

lemma oc_c30_2323: "oc_sub oc_b30 2323"
  by (oc_eval oc_c30_2323)

lemma oc_c30_2324: "oc_sub oc_b30 2324"
  by (oc_eval oc_c30_2324)

lemma oc_c30_2325: "oc_sub oc_b30 2325"
  by (oc_eval oc_c30_2325)

lemma oc_c30_2326: "oc_sub oc_b30 2326"
  by (oc_eval oc_c30_2326)

lemma oc_c30_2327: "oc_sub oc_b30 2327"
  by (oc_eval oc_c30_2327)

lemma oc_c30_2328: "oc_sub oc_b30 2328"
  by (oc_eval oc_c30_2328)

lemma oc_c30_2329: "oc_sub oc_b30 2329"
  by (oc_eval oc_c30_2329)

lemma oc_c30_2330: "oc_sub oc_b30 2330"
  by (oc_eval oc_c30_2330)

lemma oc_c30_2331: "oc_sub oc_b30 2331"
  by (oc_eval oc_c30_2331)

lemma oc_c30_2332: "oc_sub oc_b30 2332"
  by (oc_eval oc_c30_2332)

lemma oc_c30_2333: "oc_sub oc_b30 2333"
  by (oc_eval oc_c30_2333)

lemma oc_c30_2334: "oc_sub oc_b30 2334"
  by (oc_eval oc_c30_2334)

lemma oc_c30_2335: "oc_sub oc_b30 2335"
  by (oc_eval oc_c30_2335)

lemma upt_c30_145: "[2320..<2336] = [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]"
  by (simp add: upt_rec)

lemma sec_c30_145: "\<forall>j\<in>{16 * 145..<16 * 145 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 145..<16 * 145 + 16}"
  then have "j \<in> set [2320..<2336]" unfolding set_upt by simp
  then have "j \<in> set [2320, 2321, 2322, 2323, 2324, 2325, 2326, 2327, 2328, 2329, 2330, 2331, 2332, 2333, 2334, 2335]" unfolding upt_c30_145 .
  then show "oc_sub oc_b30 j" using oc_c30_2320 oc_c30_2321 oc_c30_2322 oc_c30_2323 oc_c30_2324 oc_c30_2325 oc_c30_2326 oc_c30_2327 oc_c30_2328 oc_c30_2329 oc_c30_2330 oc_c30_2331 oc_c30_2332 oc_c30_2333 oc_c30_2334 oc_c30_2335
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

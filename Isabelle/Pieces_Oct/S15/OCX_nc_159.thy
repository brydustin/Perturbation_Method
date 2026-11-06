theory OCX_nc_159
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2544: "oc_sub None 2544"
  by (oc_eval oc_nc_2544)

lemma oc_nc_2545: "oc_sub None 2545"
  by (oc_eval oc_nc_2545)

lemma oc_nc_2546: "oc_sub None 2546"
  by (oc_eval oc_nc_2546)

lemma oc_nc_2547: "oc_sub None 2547"
  by (oc_eval oc_nc_2547)

lemma oc_nc_2548: "oc_sub None 2548"
  by (oc_eval oc_nc_2548)

lemma oc_nc_2549: "oc_sub None 2549"
  by (oc_eval oc_nc_2549)

lemma oc_nc_2550: "oc_sub None 2550"
  by (oc_eval oc_nc_2550)

lemma oc_nc_2551: "oc_sub None 2551"
  by (oc_eval oc_nc_2551)

lemma oc_nc_2552: "oc_sub None 2552"
  by (oc_eval oc_nc_2552)

lemma oc_nc_2553: "oc_sub None 2553"
  by (oc_eval oc_nc_2553)

lemma oc_nc_2554: "oc_sub None 2554"
  by (oc_eval oc_nc_2554)

lemma oc_nc_2555: "oc_sub None 2555"
  by (oc_eval oc_nc_2555)

lemma oc_nc_2556: "oc_sub None 2556"
  by (oc_eval oc_nc_2556)

lemma oc_nc_2557: "oc_sub None 2557"
  by (oc_eval oc_nc_2557)

lemma oc_nc_2558: "oc_sub None 2558"
  by (oc_eval oc_nc_2558)

lemma oc_nc_2559: "oc_sub None 2559"
  by (oc_eval oc_nc_2559)

lemma upt_nc_159: "[2544..<2560] = [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]"
  by (simp add: upt_rec)

lemma sec_nc_159: "\<forall>j\<in>{16 * 159..<16 * 159 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 159..<16 * 159 + 16}"
  then have "j \<in> set [2544..<2560]" unfolding set_upt by simp
  then have "j \<in> set [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]" unfolding upt_nc_159 .
  then show "oc_sub None j" using oc_nc_2544 oc_nc_2545 oc_nc_2546 oc_nc_2547 oc_nc_2548 oc_nc_2549 oc_nc_2550 oc_nc_2551 oc_nc_2552 oc_nc_2553 oc_nc_2554 oc_nc_2555 oc_nc_2556 oc_nc_2557 oc_nc_2558 oc_nc_2559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

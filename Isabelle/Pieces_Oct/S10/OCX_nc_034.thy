theory OCX_nc_034
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0544: "oc_sub None 544"
  by (oc_eval oc_nc_0544)

lemma oc_nc_0545: "oc_sub None 545"
  by (oc_eval oc_nc_0545)

lemma oc_nc_0546: "oc_sub None 546"
  by (oc_eval oc_nc_0546)

lemma oc_nc_0547: "oc_sub None 547"
  by (oc_eval oc_nc_0547)

lemma oc_nc_0548: "oc_sub None 548"
  by (oc_eval oc_nc_0548)

lemma oc_nc_0549: "oc_sub None 549"
  by (oc_eval oc_nc_0549)

lemma oc_nc_0550: "oc_sub None 550"
  by (oc_eval oc_nc_0550)

lemma oc_nc_0551: "oc_sub None 551"
  by (oc_eval oc_nc_0551)

lemma oc_nc_0552: "oc_sub None 552"
  by (oc_eval oc_nc_0552)

lemma oc_nc_0553: "oc_sub None 553"
  by (oc_eval oc_nc_0553)

lemma oc_nc_0554: "oc_sub None 554"
  by (oc_eval oc_nc_0554)

lemma oc_nc_0555: "oc_sub None 555"
  by (oc_eval oc_nc_0555)

lemma oc_nc_0556: "oc_sub None 556"
  by (oc_eval oc_nc_0556)

lemma oc_nc_0557: "oc_sub None 557"
  by (oc_eval oc_nc_0557)

lemma oc_nc_0558: "oc_sub None 558"
  by (oc_eval oc_nc_0558)

lemma oc_nc_0559: "oc_sub None 559"
  by (oc_eval oc_nc_0559)

lemma upt_nc_034: "[544..<560] = [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]"
  by (simp add: upt_rec)

lemma sec_nc_034: "\<forall>j\<in>{16 * 34..<16 * 34 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 34..<16 * 34 + 16}"
  then have "j \<in> set [544..<560]" unfolding set_upt by simp
  then have "j \<in> set [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]" unfolding upt_nc_034 .
  then show "oc_sub None j" using oc_nc_0544 oc_nc_0545 oc_nc_0546 oc_nc_0547 oc_nc_0548 oc_nc_0549 oc_nc_0550 oc_nc_0551 oc_nc_0552 oc_nc_0553 oc_nc_0554 oc_nc_0555 oc_nc_0556 oc_nc_0557 oc_nc_0558 oc_nc_0559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

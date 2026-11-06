theory OCX_c30_034
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0544: "oc_sub oc_b30 544"
  by (oc_eval oc_c30_0544)

lemma oc_c30_0545: "oc_sub oc_b30 545"
  by (oc_eval oc_c30_0545)

lemma oc_c30_0546: "oc_sub oc_b30 546"
  by (oc_eval oc_c30_0546)

lemma oc_c30_0547: "oc_sub oc_b30 547"
  by (oc_eval oc_c30_0547)

lemma oc_c30_0548: "oc_sub oc_b30 548"
  by (oc_eval oc_c30_0548)

lemma oc_c30_0549: "oc_sub oc_b30 549"
  by (oc_eval oc_c30_0549)

lemma oc_c30_0550: "oc_sub oc_b30 550"
  by (oc_eval oc_c30_0550)

lemma oc_c30_0551: "oc_sub oc_b30 551"
  by (oc_eval oc_c30_0551)

lemma oc_c30_0552: "oc_sub oc_b30 552"
  by (oc_eval oc_c30_0552)

lemma oc_c30_0553: "oc_sub oc_b30 553"
  by (oc_eval oc_c30_0553)

lemma oc_c30_0554: "oc_sub oc_b30 554"
  by (oc_eval oc_c30_0554)

lemma oc_c30_0555: "oc_sub oc_b30 555"
  by (oc_eval oc_c30_0555)

lemma oc_c30_0556: "oc_sub oc_b30 556"
  by (oc_eval oc_c30_0556)

lemma oc_c30_0557: "oc_sub oc_b30 557"
  by (oc_eval oc_c30_0557)

lemma oc_c30_0558: "oc_sub oc_b30 558"
  by (oc_eval oc_c30_0558)

lemma oc_c30_0559: "oc_sub oc_b30 559"
  by (oc_eval oc_c30_0559)

lemma upt_c30_034: "[544..<560] = [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]"
  by (simp add: upt_rec)

lemma sec_c30_034: "\<forall>j\<in>{16 * 34..<16 * 34 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 34..<16 * 34 + 16}"
  then have "j \<in> set [544..<560]" unfolding set_upt by simp
  then have "j \<in> set [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]" unfolding upt_c30_034 .
  then show "oc_sub oc_b30 j" using oc_c30_0544 oc_c30_0545 oc_c30_0546 oc_c30_0547 oc_c30_0548 oc_c30_0549 oc_c30_0550 oc_c30_0551 oc_c30_0552 oc_c30_0553 oc_c30_0554 oc_c30_0555 oc_c30_0556 oc_c30_0557 oc_c30_0558 oc_c30_0559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory DCX_c30_034
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0544: "dc_sub dc_b30 544"
  by (dc_eval dc_c30_0544)

lemma dc_c30_0545: "dc_sub dc_b30 545"
  by (dc_eval dc_c30_0545)

lemma dc_c30_0546: "dc_sub dc_b30 546"
  by (dc_eval dc_c30_0546)

lemma dc_c30_0547: "dc_sub dc_b30 547"
  by (dc_eval dc_c30_0547)

lemma dc_c30_0548: "dc_sub dc_b30 548"
  by (dc_eval dc_c30_0548)

lemma dc_c30_0549: "dc_sub dc_b30 549"
  by (dc_eval dc_c30_0549)

lemma dc_c30_0550: "dc_sub dc_b30 550"
  by (dc_eval dc_c30_0550)

lemma dc_c30_0551: "dc_sub dc_b30 551"
  by (dc_eval dc_c30_0551)

lemma dc_c30_0552: "dc_sub dc_b30 552"
  by (dc_eval dc_c30_0552)

lemma dc_c30_0553: "dc_sub dc_b30 553"
  by (dc_eval dc_c30_0553)

lemma dc_c30_0554: "dc_sub dc_b30 554"
  by (dc_eval dc_c30_0554)

lemma dc_c30_0555: "dc_sub dc_b30 555"
  by (dc_eval dc_c30_0555)

lemma dc_c30_0556: "dc_sub dc_b30 556"
  by (dc_eval dc_c30_0556)

lemma dc_c30_0557: "dc_sub dc_b30 557"
  by (dc_eval dc_c30_0557)

lemma dc_c30_0558: "dc_sub dc_b30 558"
  by (dc_eval dc_c30_0558)

lemma dc_c30_0559: "dc_sub dc_b30 559"
  by (dc_eval dc_c30_0559)

lemma upt_c30_034: "[544..<560] = [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]"
  by (simp add: upt_rec)

lemma sec_c30_034: "\<forall>j\<in>{16 * 34..<16 * 34 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 34..<16 * 34 + 16}"
  then have "j \<in> set [544..<560]" unfolding set_upt by simp
  then have "j \<in> set [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]" unfolding upt_c30_034 .
  then show "dc_sub dc_b30 j" using dc_c30_0544 dc_c30_0545 dc_c30_0546 dc_c30_0547 dc_c30_0548 dc_c30_0549 dc_c30_0550 dc_c30_0551 dc_c30_0552 dc_c30_0553 dc_c30_0554 dc_c30_0555 dc_c30_0556 dc_c30_0557 dc_c30_0558 dc_c30_0559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

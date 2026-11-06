theory DCX_nc_034
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0544: "dc_sub None 544"
  by (dc_eval dc_nc_0544)

lemma dc_nc_0545: "dc_sub None 545"
  by (dc_eval dc_nc_0545)

lemma dc_nc_0546: "dc_sub None 546"
  by (dc_eval dc_nc_0546)

lemma dc_nc_0547: "dc_sub None 547"
  by (dc_eval dc_nc_0547)

lemma dc_nc_0548: "dc_sub None 548"
  by (dc_eval dc_nc_0548)

lemma dc_nc_0549: "dc_sub None 549"
  by (dc_eval dc_nc_0549)

lemma dc_nc_0550: "dc_sub None 550"
  by (dc_eval dc_nc_0550)

lemma dc_nc_0551: "dc_sub None 551"
  by (dc_eval dc_nc_0551)

lemma dc_nc_0552: "dc_sub None 552"
  by (dc_eval dc_nc_0552)

lemma dc_nc_0553: "dc_sub None 553"
  by (dc_eval dc_nc_0553)

lemma dc_nc_0554: "dc_sub None 554"
  by (dc_eval dc_nc_0554)

lemma dc_nc_0555: "dc_sub None 555"
  by (dc_eval dc_nc_0555)

lemma dc_nc_0556: "dc_sub None 556"
  by (dc_eval dc_nc_0556)

lemma dc_nc_0557: "dc_sub None 557"
  by (dc_eval dc_nc_0557)

lemma dc_nc_0558: "dc_sub None 558"
  by (dc_eval dc_nc_0558)

lemma dc_nc_0559: "dc_sub None 559"
  by (dc_eval dc_nc_0559)

lemma upt_nc_034: "[544..<560] = [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]"
  by (simp add: upt_rec)

lemma sec_nc_034: "\<forall>j\<in>{16 * 34..<16 * 34 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 34..<16 * 34 + 16}"
  then have "j \<in> set [544..<560]" unfolding set_upt by simp
  then have "j \<in> set [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]" unfolding upt_nc_034 .
  then show "dc_sub None j" using dc_nc_0544 dc_nc_0545 dc_nc_0546 dc_nc_0547 dc_nc_0548 dc_nc_0549 dc_nc_0550 dc_nc_0551 dc_nc_0552 dc_nc_0553 dc_nc_0554 dc_nc_0555 dc_nc_0556 dc_nc_0557 dc_nc_0558 dc_nc_0559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

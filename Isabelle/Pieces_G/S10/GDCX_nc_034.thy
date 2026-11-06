theory GDCX_nc_034
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0544: "gdc_sub None 544"
  by (gdc_eval gdc_nc_0544)

lemma gdc_nc_0545: "gdc_sub None 545"
  by (gdc_eval gdc_nc_0545)

lemma gdc_nc_0546: "gdc_sub None 546"
  by (gdc_eval gdc_nc_0546)

lemma gdc_nc_0547: "gdc_sub None 547"
  by (gdc_eval gdc_nc_0547)

lemma gdc_nc_0548: "gdc_sub None 548"
  by (gdc_eval gdc_nc_0548)

lemma gdc_nc_0549: "gdc_sub None 549"
  by (gdc_eval gdc_nc_0549)

lemma gdc_nc_0550: "gdc_sub None 550"
  by (gdc_eval gdc_nc_0550)

lemma gdc_nc_0551: "gdc_sub None 551"
  by (gdc_eval gdc_nc_0551)

lemma gdc_nc_0552: "gdc_sub None 552"
  by (gdc_eval gdc_nc_0552)

lemma gdc_nc_0553: "gdc_sub None 553"
  by (gdc_eval gdc_nc_0553)

lemma gdc_nc_0554: "gdc_sub None 554"
  by (gdc_eval gdc_nc_0554)

lemma gdc_nc_0555: "gdc_sub None 555"
  by (gdc_eval gdc_nc_0555)

lemma gdc_nc_0556: "gdc_sub None 556"
  by (gdc_eval gdc_nc_0556)

lemma gdc_nc_0557: "gdc_sub None 557"
  by (gdc_eval gdc_nc_0557)

lemma gdc_nc_0558: "gdc_sub None 558"
  by (gdc_eval gdc_nc_0558)

lemma gdc_nc_0559: "gdc_sub None 559"
  by (gdc_eval gdc_nc_0559)

lemma gupt_nc_034: "[544..<560] = [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]"
  by (simp add: upt_rec)

lemma gsec_nc_034: "\<forall>j\<in>{16 * 34..<16 * 34 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 34..<16 * 34 + 16}"
  then have "j \<in> set [544..<560]" unfolding set_upt by simp
  then have "j \<in> set [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]" unfolding gupt_nc_034 .
  then show "gdc_sub None j" using gdc_nc_0544 gdc_nc_0545 gdc_nc_0546 gdc_nc_0547 gdc_nc_0548 gdc_nc_0549 gdc_nc_0550 gdc_nc_0551 gdc_nc_0552 gdc_nc_0553 gdc_nc_0554 gdc_nc_0555 gdc_nc_0556 gdc_nc_0557 gdc_nc_0558 gdc_nc_0559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

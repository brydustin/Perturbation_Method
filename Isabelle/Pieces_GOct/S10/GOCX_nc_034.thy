theory GOCX_nc_034
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0544: "goc_sub None 544"
  by (goc_eval goc_nc_0544)

lemma goc_nc_0545: "goc_sub None 545"
  by (goc_eval goc_nc_0545)

lemma goc_nc_0546: "goc_sub None 546"
  by (goc_eval goc_nc_0546)

lemma goc_nc_0547: "goc_sub None 547"
  by (goc_eval goc_nc_0547)

lemma goc_nc_0548: "goc_sub None 548"
  by (goc_eval goc_nc_0548)

lemma goc_nc_0549: "goc_sub None 549"
  by (goc_eval goc_nc_0549)

lemma goc_nc_0550: "goc_sub None 550"
  by (goc_eval goc_nc_0550)

lemma goc_nc_0551: "goc_sub None 551"
  by (goc_eval goc_nc_0551)

lemma goc_nc_0552: "goc_sub None 552"
  by (goc_eval goc_nc_0552)

lemma goc_nc_0553: "goc_sub None 553"
  by (goc_eval goc_nc_0553)

lemma goc_nc_0554: "goc_sub None 554"
  by (goc_eval goc_nc_0554)

lemma goc_nc_0555: "goc_sub None 555"
  by (goc_eval goc_nc_0555)

lemma goc_nc_0556: "goc_sub None 556"
  by (goc_eval goc_nc_0556)

lemma goc_nc_0557: "goc_sub None 557"
  by (goc_eval goc_nc_0557)

lemma goc_nc_0558: "goc_sub None 558"
  by (goc_eval goc_nc_0558)

lemma goc_nc_0559: "goc_sub None 559"
  by (goc_eval goc_nc_0559)

lemma gupt_nc_034: "[544..<560] = [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]"
  by (simp add: upt_rec)

lemma gsec_nc_034: "\<forall>j\<in>{16 * 34..<16 * 34 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 34..<16 * 34 + 16}"
  then have "j \<in> set [544..<560]" unfolding set_upt by simp
  then have "j \<in> set [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559]" unfolding gupt_nc_034 .
  then show "goc_sub None j" using goc_nc_0544 goc_nc_0545 goc_nc_0546 goc_nc_0547 goc_nc_0548 goc_nc_0549 goc_nc_0550 goc_nc_0551 goc_nc_0552 goc_nc_0553 goc_nc_0554 goc_nc_0555 goc_nc_0556 goc_nc_0557 goc_nc_0558 goc_nc_0559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

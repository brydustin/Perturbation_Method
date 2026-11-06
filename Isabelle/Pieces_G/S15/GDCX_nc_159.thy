theory GDCX_nc_159
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2544: "gdc_sub None 2544"
  by (gdc_eval gdc_nc_2544)

lemma gdc_nc_2545: "gdc_sub None 2545"
  by (gdc_eval gdc_nc_2545)

lemma gdc_nc_2546: "gdc_sub None 2546"
  by (gdc_eval gdc_nc_2546)

lemma gdc_nc_2547: "gdc_sub None 2547"
  by (gdc_eval gdc_nc_2547)

lemma gdc_nc_2548: "gdc_sub None 2548"
  by (gdc_eval gdc_nc_2548)

lemma gdc_nc_2549: "gdc_sub None 2549"
  by (gdc_eval gdc_nc_2549)

lemma gdc_nc_2550: "gdc_sub None 2550"
  by (gdc_eval gdc_nc_2550)

lemma gdc_nc_2551: "gdc_sub None 2551"
  by (gdc_eval gdc_nc_2551)

lemma gdc_nc_2552: "gdc_sub None 2552"
  by (gdc_eval gdc_nc_2552)

lemma gdc_nc_2553: "gdc_sub None 2553"
  by (gdc_eval gdc_nc_2553)

lemma gdc_nc_2554: "gdc_sub None 2554"
  by (gdc_eval gdc_nc_2554)

lemma gdc_nc_2555: "gdc_sub None 2555"
  by (gdc_eval gdc_nc_2555)

lemma gdc_nc_2556: "gdc_sub None 2556"
  by (gdc_eval gdc_nc_2556)

lemma gdc_nc_2557: "gdc_sub None 2557"
  by (gdc_eval gdc_nc_2557)

lemma gdc_nc_2558: "gdc_sub None 2558"
  by (gdc_eval gdc_nc_2558)

lemma gdc_nc_2559: "gdc_sub None 2559"
  by (gdc_eval gdc_nc_2559)

lemma gupt_nc_159: "[2544..<2560] = [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]"
  by (simp add: upt_rec)

lemma gsec_nc_159: "\<forall>j\<in>{16 * 159..<16 * 159 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 159..<16 * 159 + 16}"
  then have "j \<in> set [2544..<2560]" unfolding set_upt by simp
  then have "j \<in> set [2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559]" unfolding gupt_nc_159 .
  then show "gdc_sub None j" using gdc_nc_2544 gdc_nc_2545 gdc_nc_2546 gdc_nc_2547 gdc_nc_2548 gdc_nc_2549 gdc_nc_2550 gdc_nc_2551 gdc_nc_2552 gdc_nc_2553 gdc_nc_2554 gdc_nc_2555 gdc_nc_2556 gdc_nc_2557 gdc_nc_2558 gdc_nc_2559
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory GDCX_nc_019
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0304: "gdc_sub None 304"
  by (gdc_eval gdc_nc_0304)

lemma gdc_nc_0305: "gdc_sub None 305"
  by (gdc_eval gdc_nc_0305)

lemma gdc_nc_0306: "gdc_sub None 306"
  by (gdc_eval gdc_nc_0306)

lemma gdc_nc_0307: "gdc_sub None 307"
  by (gdc_eval gdc_nc_0307)

lemma gdc_nc_0308: "gdc_sub None 308"
  by (gdc_eval gdc_nc_0308)

lemma gdc_nc_0309: "gdc_sub None 309"
  by (gdc_eval gdc_nc_0309)

lemma gdc_nc_0310: "gdc_sub None 310"
  by (gdc_eval gdc_nc_0310)

lemma gdc_nc_0311: "gdc_sub None 311"
  by (gdc_eval gdc_nc_0311)

lemma gdc_nc_0312: "gdc_sub None 312"
  by (gdc_eval gdc_nc_0312)

lemma gdc_nc_0313: "gdc_sub None 313"
  by (gdc_eval gdc_nc_0313)

lemma gdc_nc_0314: "gdc_sub None 314"
  by (gdc_eval gdc_nc_0314)

lemma gdc_nc_0315: "gdc_sub None 315"
  by (gdc_eval gdc_nc_0315)

lemma gdc_nc_0316: "gdc_sub None 316"
  by (gdc_eval gdc_nc_0316)

lemma gdc_nc_0317: "gdc_sub None 317"
  by (gdc_eval gdc_nc_0317)

lemma gdc_nc_0318: "gdc_sub None 318"
  by (gdc_eval gdc_nc_0318)

lemma gdc_nc_0319: "gdc_sub None 319"
  by (gdc_eval gdc_nc_0319)

lemma gupt_nc_019: "[304..<320] = [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]"
  by (simp add: upt_rec)

lemma gsec_nc_019: "\<forall>j\<in>{16 * 19..<16 * 19 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 19..<16 * 19 + 16}"
  then have "j \<in> set [304..<320]" unfolding set_upt by simp
  then have "j \<in> set [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]" unfolding gupt_nc_019 .
  then show "gdc_sub None j" using gdc_nc_0304 gdc_nc_0305 gdc_nc_0306 gdc_nc_0307 gdc_nc_0308 gdc_nc_0309 gdc_nc_0310 gdc_nc_0311 gdc_nc_0312 gdc_nc_0313 gdc_nc_0314 gdc_nc_0315 gdc_nc_0316 gdc_nc_0317 gdc_nc_0318 gdc_nc_0319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

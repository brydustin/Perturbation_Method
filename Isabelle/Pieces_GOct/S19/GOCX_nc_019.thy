theory GOCX_nc_019
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0304: "goc_sub None 304"
  by (goc_eval goc_nc_0304)

lemma goc_nc_0305: "goc_sub None 305"
  by (goc_eval goc_nc_0305)

lemma goc_nc_0306: "goc_sub None 306"
  by (goc_eval goc_nc_0306)

lemma goc_nc_0307: "goc_sub None 307"
  by (goc_eval goc_nc_0307)

lemma goc_nc_0308: "goc_sub None 308"
  by (goc_eval goc_nc_0308)

lemma goc_nc_0309: "goc_sub None 309"
  by (goc_eval goc_nc_0309)

lemma goc_nc_0310: "goc_sub None 310"
  by (goc_eval goc_nc_0310)

lemma goc_nc_0311: "goc_sub None 311"
  by (goc_eval goc_nc_0311)

lemma goc_nc_0312: "goc_sub None 312"
  by (goc_eval goc_nc_0312)

lemma goc_nc_0313: "goc_sub None 313"
  by (goc_eval goc_nc_0313)

lemma goc_nc_0314: "goc_sub None 314"
  by (goc_eval goc_nc_0314)

lemma goc_nc_0315: "goc_sub None 315"
  by (goc_eval goc_nc_0315)

lemma goc_nc_0316: "goc_sub None 316"
  by (goc_eval goc_nc_0316)

lemma goc_nc_0317: "goc_sub None 317"
  by (goc_eval goc_nc_0317)

lemma goc_nc_0318: "goc_sub None 318"
  by (goc_eval goc_nc_0318)

lemma goc_nc_0319: "goc_sub None 319"
  by (goc_eval goc_nc_0319)

lemma gupt_nc_019: "[304..<320] = [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]"
  by (simp add: upt_rec)

lemma gsec_nc_019: "\<forall>j\<in>{16 * 19..<16 * 19 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 19..<16 * 19 + 16}"
  then have "j \<in> set [304..<320]" unfolding set_upt by simp
  then have "j \<in> set [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]" unfolding gupt_nc_019 .
  then show "goc_sub None j" using goc_nc_0304 goc_nc_0305 goc_nc_0306 goc_nc_0307 goc_nc_0308 goc_nc_0309 goc_nc_0310 goc_nc_0311 goc_nc_0312 goc_nc_0313 goc_nc_0314 goc_nc_0315 goc_nc_0316 goc_nc_0317 goc_nc_0318 goc_nc_0319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

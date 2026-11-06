theory OCX_nc_019
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0304: "oc_sub None 304"
  by (oc_eval oc_nc_0304)

lemma oc_nc_0305: "oc_sub None 305"
  by (oc_eval oc_nc_0305)

lemma oc_nc_0306: "oc_sub None 306"
  by (oc_eval oc_nc_0306)

lemma oc_nc_0307: "oc_sub None 307"
  by (oc_eval oc_nc_0307)

lemma oc_nc_0308: "oc_sub None 308"
  by (oc_eval oc_nc_0308)

lemma oc_nc_0309: "oc_sub None 309"
  by (oc_eval oc_nc_0309)

lemma oc_nc_0310: "oc_sub None 310"
  by (oc_eval oc_nc_0310)

lemma oc_nc_0311: "oc_sub None 311"
  by (oc_eval oc_nc_0311)

lemma oc_nc_0312: "oc_sub None 312"
  by (oc_eval oc_nc_0312)

lemma oc_nc_0313: "oc_sub None 313"
  by (oc_eval oc_nc_0313)

lemma oc_nc_0314: "oc_sub None 314"
  by (oc_eval oc_nc_0314)

lemma oc_nc_0315: "oc_sub None 315"
  by (oc_eval oc_nc_0315)

lemma oc_nc_0316: "oc_sub None 316"
  by (oc_eval oc_nc_0316)

lemma oc_nc_0317: "oc_sub None 317"
  by (oc_eval oc_nc_0317)

lemma oc_nc_0318: "oc_sub None 318"
  by (oc_eval oc_nc_0318)

lemma oc_nc_0319: "oc_sub None 319"
  by (oc_eval oc_nc_0319)

lemma upt_nc_019: "[304..<320] = [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]"
  by (simp add: upt_rec)

lemma sec_nc_019: "\<forall>j\<in>{16 * 19..<16 * 19 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 19..<16 * 19 + 16}"
  then have "j \<in> set [304..<320]" unfolding set_upt by simp
  then have "j \<in> set [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]" unfolding upt_nc_019 .
  then show "oc_sub None j" using oc_nc_0304 oc_nc_0305 oc_nc_0306 oc_nc_0307 oc_nc_0308 oc_nc_0309 oc_nc_0310 oc_nc_0311 oc_nc_0312 oc_nc_0313 oc_nc_0314 oc_nc_0315 oc_nc_0316 oc_nc_0317 oc_nc_0318 oc_nc_0319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

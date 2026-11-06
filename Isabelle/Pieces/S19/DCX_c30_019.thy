theory DCX_c30_019
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0304: "dc_sub dc_b30 304"
  by (dc_eval dc_c30_0304)

lemma dc_c30_0305: "dc_sub dc_b30 305"
  by (dc_eval dc_c30_0305)

lemma dc_c30_0306: "dc_sub dc_b30 306"
  by (dc_eval dc_c30_0306)

lemma dc_c30_0307: "dc_sub dc_b30 307"
  by (dc_eval dc_c30_0307)

lemma dc_c30_0308: "dc_sub dc_b30 308"
  by (dc_eval dc_c30_0308)

lemma dc_c30_0309: "dc_sub dc_b30 309"
  by (dc_eval dc_c30_0309)

lemma dc_c30_0310: "dc_sub dc_b30 310"
  by (dc_eval dc_c30_0310)

lemma dc_c30_0311: "dc_sub dc_b30 311"
  by (dc_eval dc_c30_0311)

lemma dc_c30_0312: "dc_sub dc_b30 312"
  by (dc_eval dc_c30_0312)

lemma dc_c30_0313: "dc_sub dc_b30 313"
  by (dc_eval dc_c30_0313)

lemma dc_c30_0314: "dc_sub dc_b30 314"
  by (dc_eval dc_c30_0314)

lemma dc_c30_0315: "dc_sub dc_b30 315"
  by (dc_eval dc_c30_0315)

lemma dc_c30_0316: "dc_sub dc_b30 316"
  by (dc_eval dc_c30_0316)

lemma dc_c30_0317: "dc_sub dc_b30 317"
  by (dc_eval dc_c30_0317)

lemma dc_c30_0318: "dc_sub dc_b30 318"
  by (dc_eval dc_c30_0318)

lemma dc_c30_0319: "dc_sub dc_b30 319"
  by (dc_eval dc_c30_0319)

lemma upt_c30_019: "[304..<320] = [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]"
  by (simp add: upt_rec)

lemma sec_c30_019: "\<forall>j\<in>{16 * 19..<16 * 19 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 19..<16 * 19 + 16}"
  then have "j \<in> set [304..<320]" unfolding set_upt by simp
  then have "j \<in> set [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]" unfolding upt_c30_019 .
  then show "dc_sub dc_b30 j" using dc_c30_0304 dc_c30_0305 dc_c30_0306 dc_c30_0307 dc_c30_0308 dc_c30_0309 dc_c30_0310 dc_c30_0311 dc_c30_0312 dc_c30_0313 dc_c30_0314 dc_c30_0315 dc_c30_0316 dc_c30_0317 dc_c30_0318 dc_c30_0319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

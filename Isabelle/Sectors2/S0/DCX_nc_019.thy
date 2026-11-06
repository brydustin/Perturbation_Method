theory DCX_nc_019
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0304: "dc_sub None 304"
  by (dc_eval dc_nc_0304)

lemma dc_nc_0305: "dc_sub None 305"
  by (dc_eval dc_nc_0305)

lemma dc_nc_0306: "dc_sub None 306"
  by (dc_eval dc_nc_0306)

lemma dc_nc_0307: "dc_sub None 307"
  by (dc_eval dc_nc_0307)

lemma dc_nc_0308: "dc_sub None 308"
  by (dc_eval dc_nc_0308)

lemma dc_nc_0309: "dc_sub None 309"
  by (dc_eval dc_nc_0309)

lemma dc_nc_0310: "dc_sub None 310"
  by (dc_eval dc_nc_0310)

lemma dc_nc_0311: "dc_sub None 311"
  by (dc_eval dc_nc_0311)

lemma dc_nc_0312: "dc_sub None 312"
  by (dc_eval dc_nc_0312)

lemma dc_nc_0313: "dc_sub None 313"
  by (dc_eval dc_nc_0313)

lemma dc_nc_0314: "dc_sub None 314"
  by (dc_eval dc_nc_0314)

lemma dc_nc_0315: "dc_sub None 315"
  by (dc_eval dc_nc_0315)

lemma dc_nc_0316: "dc_sub None 316"
  by (dc_eval dc_nc_0316)

lemma dc_nc_0317: "dc_sub None 317"
  by (dc_eval dc_nc_0317)

lemma dc_nc_0318: "dc_sub None 318"
  by (dc_eval dc_nc_0318)

lemma dc_nc_0319: "dc_sub None 319"
  by (dc_eval dc_nc_0319)

lemma upt_nc_019: "[304..<320] = [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]"
  by (simp add: upt_rec)

lemma sec_nc_019: "\<forall>j\<in>{16 * 19..<16 * 19 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 19..<16 * 19 + 16}"
  then have "j \<in> set [304..<320]" unfolding set_upt by simp
  then have "j \<in> set [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319]" unfolding upt_nc_019 .
  then show "dc_sub None j" using dc_nc_0304 dc_nc_0305 dc_nc_0306 dc_nc_0307 dc_nc_0308 dc_nc_0309 dc_nc_0310 dc_nc_0311 dc_nc_0312 dc_nc_0313 dc_nc_0314 dc_nc_0315 dc_nc_0316 dc_nc_0317 dc_nc_0318 dc_nc_0319
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

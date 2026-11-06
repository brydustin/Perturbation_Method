theory DCX_c30_004
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0064: "dc_sub dc_b30 64"
  by (dc_eval dc_c30_0064)

lemma dc_c30_0065: "dc_sub dc_b30 65"
  by (dc_eval dc_c30_0065)

lemma dc_c30_0066: "dc_sub dc_b30 66"
  by (dc_eval dc_c30_0066)

lemma dc_c30_0067: "dc_sub dc_b30 67"
  by (dc_eval dc_c30_0067)

lemma dc_c30_0068: "dc_sub dc_b30 68"
  by (dc_eval dc_c30_0068)

lemma dc_c30_0069: "dc_sub dc_b30 69"
  by (dc_eval dc_c30_0069)

lemma dc_c30_0070: "dc_sub dc_b30 70"
  by (dc_eval dc_c30_0070)

lemma dc_c30_0071: "dc_sub dc_b30 71"
  by (dc_eval dc_c30_0071)

lemma dc_c30_0072: "dc_sub dc_b30 72"
  by (dc_eval dc_c30_0072)

lemma dc_c30_0073: "dc_sub dc_b30 73"
  by (dc_eval dc_c30_0073)

lemma dc_c30_0074: "dc_sub dc_b30 74"
  by (dc_eval dc_c30_0074)

lemma dc_c30_0075: "dc_sub dc_b30 75"
  by (dc_eval dc_c30_0075)

lemma dc_c30_0076: "dc_sub dc_b30 76"
  by (dc_eval dc_c30_0076)

lemma dc_c30_0077: "dc_sub dc_b30 77"
  by (dc_eval dc_c30_0077)

lemma dc_c30_0078: "dc_sub dc_b30 78"
  by (dc_eval dc_c30_0078)

lemma dc_c30_0079: "dc_sub dc_b30 79"
  by (dc_eval dc_c30_0079)

lemma upt_c30_004: "[64..<80] = [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]"
  by (simp add: upt_rec)

lemma sec_c30_004: "\<forall>j\<in>{16 * 4..<16 * 4 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 4..<16 * 4 + 16}"
  then have "j \<in> set [64..<80]" unfolding set_upt by simp
  then have "j \<in> set [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]" unfolding upt_c30_004 .
  then show "dc_sub dc_b30 j" using dc_c30_0064 dc_c30_0065 dc_c30_0066 dc_c30_0067 dc_c30_0068 dc_c30_0069 dc_c30_0070 dc_c30_0071 dc_c30_0072 dc_c30_0073 dc_c30_0074 dc_c30_0075 dc_c30_0076 dc_c30_0077 dc_c30_0078 dc_c30_0079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

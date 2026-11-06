theory DCX_nc_004
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0064: "dc_sub None 64"
  by (dc_eval dc_nc_0064)

lemma dc_nc_0065: "dc_sub None 65"
  by (dc_eval dc_nc_0065)

lemma dc_nc_0066: "dc_sub None 66"
  by (dc_eval dc_nc_0066)

lemma dc_nc_0067: "dc_sub None 67"
  by (dc_eval dc_nc_0067)

lemma dc_nc_0068: "dc_sub None 68"
  by (dc_eval dc_nc_0068)

lemma dc_nc_0069: "dc_sub None 69"
  by (dc_eval dc_nc_0069)

lemma dc_nc_0070: "dc_sub None 70"
  by (dc_eval dc_nc_0070)

lemma dc_nc_0071: "dc_sub None 71"
  by (dc_eval dc_nc_0071)

lemma dc_nc_0072: "dc_sub None 72"
  by (dc_eval dc_nc_0072)

lemma dc_nc_0073: "dc_sub None 73"
  by (dc_eval dc_nc_0073)

lemma dc_nc_0074: "dc_sub None 74"
  by (dc_eval dc_nc_0074)

lemma dc_nc_0075: "dc_sub None 75"
  by (dc_eval dc_nc_0075)

lemma dc_nc_0076: "dc_sub None 76"
  by (dc_eval dc_nc_0076)

lemma dc_nc_0077: "dc_sub None 77"
  by (dc_eval dc_nc_0077)

lemma dc_nc_0078: "dc_sub None 78"
  by (dc_eval dc_nc_0078)

lemma dc_nc_0079: "dc_sub None 79"
  by (dc_eval dc_nc_0079)

lemma upt_nc_004: "[64..<80] = [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]"
  by (simp add: upt_rec)

lemma sec_nc_004: "\<forall>j\<in>{16 * 4..<16 * 4 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 4..<16 * 4 + 16}"
  then have "j \<in> set [64..<80]" unfolding set_upt by simp
  then have "j \<in> set [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]" unfolding upt_nc_004 .
  then show "dc_sub None j" using dc_nc_0064 dc_nc_0065 dc_nc_0066 dc_nc_0067 dc_nc_0068 dc_nc_0069 dc_nc_0070 dc_nc_0071 dc_nc_0072 dc_nc_0073 dc_nc_0074 dc_nc_0075 dc_nc_0076 dc_nc_0077 dc_nc_0078 dc_nc_0079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

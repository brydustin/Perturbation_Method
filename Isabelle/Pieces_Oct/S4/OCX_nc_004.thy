theory OCX_nc_004
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0064: "oc_sub None 64"
  by (oc_eval oc_nc_0064)

lemma oc_nc_0065: "oc_sub None 65"
  by (oc_eval oc_nc_0065)

lemma oc_nc_0066: "oc_sub None 66"
  by (oc_eval oc_nc_0066)

lemma oc_nc_0067: "oc_sub None 67"
  by (oc_eval oc_nc_0067)

lemma oc_nc_0068: "oc_sub None 68"
  by (oc_eval oc_nc_0068)

lemma oc_nc_0069: "oc_sub None 69"
  by (oc_eval oc_nc_0069)

lemma oc_nc_0070: "oc_sub None 70"
  by (oc_eval oc_nc_0070)

lemma oc_nc_0071: "oc_sub None 71"
  by (oc_eval oc_nc_0071)

lemma oc_nc_0072: "oc_sub None 72"
  by (oc_eval oc_nc_0072)

lemma oc_nc_0073: "oc_sub None 73"
  by (oc_eval oc_nc_0073)

lemma oc_nc_0074: "oc_sub None 74"
  by (oc_eval oc_nc_0074)

lemma oc_nc_0075: "oc_sub None 75"
  by (oc_eval oc_nc_0075)

lemma oc_nc_0076: "oc_sub None 76"
  by (oc_eval oc_nc_0076)

lemma oc_nc_0077: "oc_sub None 77"
  by (oc_eval oc_nc_0077)

lemma oc_nc_0078: "oc_sub None 78"
  by (oc_eval oc_nc_0078)

lemma oc_nc_0079: "oc_sub None 79"
  by (oc_eval oc_nc_0079)

lemma upt_nc_004: "[64..<80] = [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]"
  by (simp add: upt_rec)

lemma sec_nc_004: "\<forall>j\<in>{16 * 4..<16 * 4 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 4..<16 * 4 + 16}"
  then have "j \<in> set [64..<80]" unfolding set_upt by simp
  then have "j \<in> set [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]" unfolding upt_nc_004 .
  then show "oc_sub None j" using oc_nc_0064 oc_nc_0065 oc_nc_0066 oc_nc_0067 oc_nc_0068 oc_nc_0069 oc_nc_0070 oc_nc_0071 oc_nc_0072 oc_nc_0073 oc_nc_0074 oc_nc_0075 oc_nc_0076 oc_nc_0077 oc_nc_0078 oc_nc_0079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

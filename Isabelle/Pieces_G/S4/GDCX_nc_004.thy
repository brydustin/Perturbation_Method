theory GDCX_nc_004
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0064: "gdc_sub None 64"
  by (gdc_eval gdc_nc_0064)

lemma gdc_nc_0065: "gdc_sub None 65"
  by (gdc_eval gdc_nc_0065)

lemma gdc_nc_0066: "gdc_sub None 66"
  by (gdc_eval gdc_nc_0066)

lemma gdc_nc_0067: "gdc_sub None 67"
  by (gdc_eval gdc_nc_0067)

lemma gdc_nc_0068: "gdc_sub None 68"
  by (gdc_eval gdc_nc_0068)

lemma gdc_nc_0069: "gdc_sub None 69"
  by (gdc_eval gdc_nc_0069)

lemma gdc_nc_0070: "gdc_sub None 70"
  by (gdc_eval gdc_nc_0070)

lemma gdc_nc_0071: "gdc_sub None 71"
  by (gdc_eval gdc_nc_0071)

lemma gdc_nc_0072: "gdc_sub None 72"
  by (gdc_eval gdc_nc_0072)

lemma gdc_nc_0073: "gdc_sub None 73"
  by (gdc_eval gdc_nc_0073)

lemma gdc_nc_0074: "gdc_sub None 74"
  by (gdc_eval gdc_nc_0074)

lemma gdc_nc_0075: "gdc_sub None 75"
  by (gdc_eval gdc_nc_0075)

lemma gdc_nc_0076: "gdc_sub None 76"
  by (gdc_eval gdc_nc_0076)

lemma gdc_nc_0077: "gdc_sub None 77"
  by (gdc_eval gdc_nc_0077)

lemma gdc_nc_0078: "gdc_sub None 78"
  by (gdc_eval gdc_nc_0078)

lemma gdc_nc_0079: "gdc_sub None 79"
  by (gdc_eval gdc_nc_0079)

lemma gupt_nc_004: "[64..<80] = [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]"
  by (simp add: upt_rec)

lemma gsec_nc_004: "\<forall>j\<in>{16 * 4..<16 * 4 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 4..<16 * 4 + 16}"
  then have "j \<in> set [64..<80]" unfolding set_upt by simp
  then have "j \<in> set [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]" unfolding gupt_nc_004 .
  then show "gdc_sub None j" using gdc_nc_0064 gdc_nc_0065 gdc_nc_0066 gdc_nc_0067 gdc_nc_0068 gdc_nc_0069 gdc_nc_0070 gdc_nc_0071 gdc_nc_0072 gdc_nc_0073 gdc_nc_0074 gdc_nc_0075 gdc_nc_0076 gdc_nc_0077 gdc_nc_0078 gdc_nc_0079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

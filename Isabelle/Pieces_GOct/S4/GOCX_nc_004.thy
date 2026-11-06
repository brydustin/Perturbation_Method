theory GOCX_nc_004
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0064: "goc_sub None 64"
  by (goc_eval goc_nc_0064)

lemma goc_nc_0065: "goc_sub None 65"
  by (goc_eval goc_nc_0065)

lemma goc_nc_0066: "goc_sub None 66"
  by (goc_eval goc_nc_0066)

lemma goc_nc_0067: "goc_sub None 67"
  by (goc_eval goc_nc_0067)

lemma goc_nc_0068: "goc_sub None 68"
  by (goc_eval goc_nc_0068)

lemma goc_nc_0069: "goc_sub None 69"
  by (goc_eval goc_nc_0069)

lemma goc_nc_0070: "goc_sub None 70"
  by (goc_eval goc_nc_0070)

lemma goc_nc_0071: "goc_sub None 71"
  by (goc_eval goc_nc_0071)

lemma goc_nc_0072: "goc_sub None 72"
  by (goc_eval goc_nc_0072)

lemma goc_nc_0073: "goc_sub None 73"
  by (goc_eval goc_nc_0073)

lemma goc_nc_0074: "goc_sub None 74"
  by (goc_eval goc_nc_0074)

lemma goc_nc_0075: "goc_sub None 75"
  by (goc_eval goc_nc_0075)

lemma goc_nc_0076: "goc_sub None 76"
  by (goc_eval goc_nc_0076)

lemma goc_nc_0077: "goc_sub None 77"
  by (goc_eval goc_nc_0077)

lemma goc_nc_0078: "goc_sub None 78"
  by (goc_eval goc_nc_0078)

lemma goc_nc_0079: "goc_sub None 79"
  by (goc_eval goc_nc_0079)

lemma gupt_nc_004: "[64..<80] = [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]"
  by (simp add: upt_rec)

lemma gsec_nc_004: "\<forall>j\<in>{16 * 4..<16 * 4 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 4..<16 * 4 + 16}"
  then have "j \<in> set [64..<80]" unfolding set_upt by simp
  then have "j \<in> set [64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]" unfolding gupt_nc_004 .
  then show "goc_sub None j" using goc_nc_0064 goc_nc_0065 goc_nc_0066 goc_nc_0067 goc_nc_0068 goc_nc_0069 goc_nc_0070 goc_nc_0071 goc_nc_0072 goc_nc_0073 goc_nc_0074 goc_nc_0075 goc_nc_0076 goc_nc_0077 goc_nc_0078 goc_nc_0079
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

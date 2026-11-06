theory GDCX_nc_008
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0128: "gdc_sub None 128"
  by (gdc_eval gdc_nc_0128)

lemma gdc_nc_0129: "gdc_sub None 129"
  by (gdc_eval gdc_nc_0129)

lemma gdc_nc_0130: "gdc_sub None 130"
  by (gdc_eval gdc_nc_0130)

lemma gdc_nc_0131: "gdc_sub None 131"
  by (gdc_eval gdc_nc_0131)

lemma gdc_nc_0132: "gdc_sub None 132"
  by (gdc_eval gdc_nc_0132)

lemma gdc_nc_0133: "gdc_sub None 133"
  by (gdc_eval gdc_nc_0133)

lemma gdc_nc_0134: "gdc_sub None 134"
  by (gdc_eval gdc_nc_0134)

lemma gdc_nc_0135: "gdc_sub None 135"
  by (gdc_eval gdc_nc_0135)

lemma gdc_nc_0136: "gdc_sub None 136"
  by (gdc_eval gdc_nc_0136)

lemma gdc_nc_0137: "gdc_sub None 137"
  by (gdc_eval gdc_nc_0137)

lemma gdc_nc_0138: "gdc_sub None 138"
  by (gdc_eval gdc_nc_0138)

lemma gdc_nc_0139: "gdc_sub None 139"
  by (gdc_eval gdc_nc_0139)

lemma gdc_nc_0140: "gdc_sub None 140"
  by (gdc_eval gdc_nc_0140)

lemma gdc_nc_0141: "gdc_sub None 141"
  by (gdc_eval gdc_nc_0141)

lemma gdc_nc_0142: "gdc_sub None 142"
  by (gdc_eval gdc_nc_0142)

lemma gdc_nc_0143: "gdc_sub None 143"
  by (gdc_eval gdc_nc_0143)

lemma gupt_nc_008: "[128..<144] = [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]"
  by (simp add: upt_rec)

lemma gsec_nc_008: "\<forall>j\<in>{16 * 8..<16 * 8 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 8..<16 * 8 + 16}"
  then have "j \<in> set [128..<144]" unfolding set_upt by simp
  then have "j \<in> set [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]" unfolding gupt_nc_008 .
  then show "gdc_sub None j" using gdc_nc_0128 gdc_nc_0129 gdc_nc_0130 gdc_nc_0131 gdc_nc_0132 gdc_nc_0133 gdc_nc_0134 gdc_nc_0135 gdc_nc_0136 gdc_nc_0137 gdc_nc_0138 gdc_nc_0139 gdc_nc_0140 gdc_nc_0141 gdc_nc_0142 gdc_nc_0143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

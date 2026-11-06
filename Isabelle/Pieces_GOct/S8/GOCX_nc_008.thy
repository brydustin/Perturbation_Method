theory GOCX_nc_008
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0128: "goc_sub None 128"
  by (goc_eval goc_nc_0128)

lemma goc_nc_0129: "goc_sub None 129"
  by (goc_eval goc_nc_0129)

lemma goc_nc_0130: "goc_sub None 130"
  by (goc_eval goc_nc_0130)

lemma goc_nc_0131: "goc_sub None 131"
  by (goc_eval goc_nc_0131)

lemma goc_nc_0132: "goc_sub None 132"
  by (goc_eval goc_nc_0132)

lemma goc_nc_0133: "goc_sub None 133"
  by (goc_eval goc_nc_0133)

lemma goc_nc_0134: "goc_sub None 134"
  by (goc_eval goc_nc_0134)

lemma goc_nc_0135: "goc_sub None 135"
  by (goc_eval goc_nc_0135)

lemma goc_nc_0136: "goc_sub None 136"
  by (goc_eval goc_nc_0136)

lemma goc_nc_0137: "goc_sub None 137"
  by (goc_eval goc_nc_0137)

lemma goc_nc_0138: "goc_sub None 138"
  by (goc_eval goc_nc_0138)

lemma goc_nc_0139: "goc_sub None 139"
  by (goc_eval goc_nc_0139)

lemma goc_nc_0140: "goc_sub None 140"
  by (goc_eval goc_nc_0140)

lemma goc_nc_0141: "goc_sub None 141"
  by (goc_eval goc_nc_0141)

lemma goc_nc_0142: "goc_sub None 142"
  by (goc_eval goc_nc_0142)

lemma goc_nc_0143: "goc_sub None 143"
  by (goc_eval goc_nc_0143)

lemma gupt_nc_008: "[128..<144] = [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]"
  by (simp add: upt_rec)

lemma gsec_nc_008: "\<forall>j\<in>{16 * 8..<16 * 8 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 8..<16 * 8 + 16}"
  then have "j \<in> set [128..<144]" unfolding set_upt by simp
  then have "j \<in> set [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]" unfolding gupt_nc_008 .
  then show "goc_sub None j" using goc_nc_0128 goc_nc_0129 goc_nc_0130 goc_nc_0131 goc_nc_0132 goc_nc_0133 goc_nc_0134 goc_nc_0135 goc_nc_0136 goc_nc_0137 goc_nc_0138 goc_nc_0139 goc_nc_0140 goc_nc_0141 goc_nc_0142 goc_nc_0143
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

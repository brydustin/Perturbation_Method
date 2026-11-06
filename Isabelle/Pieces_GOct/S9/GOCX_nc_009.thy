theory GOCX_nc_009
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0144: "goc_sub None 144"
  by (goc_eval goc_nc_0144)

lemma goc_nc_0145: "goc_sub None 145"
  by (goc_eval goc_nc_0145)

lemma goc_nc_0146: "goc_sub None 146"
  by (goc_eval goc_nc_0146)

lemma goc_nc_0147: "goc_sub None 147"
  by (goc_eval goc_nc_0147)

lemma goc_nc_0148: "goc_sub None 148"
  by (goc_eval goc_nc_0148)

lemma goc_nc_0149: "goc_sub None 149"
  by (goc_eval goc_nc_0149)

lemma goc_nc_0150: "goc_sub None 150"
  by (goc_eval goc_nc_0150)

lemma goc_nc_0151: "goc_sub None 151"
  by (goc_eval goc_nc_0151)

lemma goc_nc_0152: "goc_sub None 152"
  by (goc_eval goc_nc_0152)

lemma goc_nc_0153: "goc_sub None 153"
  by (goc_eval goc_nc_0153)

lemma goc_nc_0154: "goc_sub None 154"
  by (goc_eval goc_nc_0154)

lemma goc_nc_0155: "goc_sub None 155"
  by (goc_eval goc_nc_0155)

lemma goc_nc_0156: "goc_sub None 156"
  by (goc_eval goc_nc_0156)

lemma goc_nc_0157: "goc_sub None 157"
  by (goc_eval goc_nc_0157)

lemma goc_nc_0158: "goc_sub None 158"
  by (goc_eval goc_nc_0158)

lemma goc_nc_0159: "goc_sub None 159"
  by (goc_eval goc_nc_0159)

lemma gupt_nc_009: "[144..<160] = [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]"
  by (simp add: upt_rec)

lemma gsec_nc_009: "\<forall>j\<in>{16 * 9..<16 * 9 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 9..<16 * 9 + 16}"
  then have "j \<in> set [144..<160]" unfolding set_upt by simp
  then have "j \<in> set [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]" unfolding gupt_nc_009 .
  then show "goc_sub None j" using goc_nc_0144 goc_nc_0145 goc_nc_0146 goc_nc_0147 goc_nc_0148 goc_nc_0149 goc_nc_0150 goc_nc_0151 goc_nc_0152 goc_nc_0153 goc_nc_0154 goc_nc_0155 goc_nc_0156 goc_nc_0157 goc_nc_0158 goc_nc_0159
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

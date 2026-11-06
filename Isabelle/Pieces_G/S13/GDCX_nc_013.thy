theory GDCX_nc_013
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0208: "gdc_sub None 208"
  by (gdc_eval gdc_nc_0208)

lemma gdc_nc_0209: "gdc_sub None 209"
  by (gdc_eval gdc_nc_0209)

lemma gdc_nc_0210: "gdc_sub None 210"
  by (gdc_eval gdc_nc_0210)

lemma gdc_nc_0211: "gdc_sub None 211"
  by (gdc_eval gdc_nc_0211)

lemma gdc_nc_0212: "gdc_sub None 212"
  by (gdc_eval gdc_nc_0212)

lemma gdc_nc_0213: "gdc_sub None 213"
  by (gdc_eval gdc_nc_0213)

lemma gdc_nc_0214: "gdc_sub None 214"
  by (gdc_eval gdc_nc_0214)

lemma gdc_nc_0215: "gdc_sub None 215"
  by (gdc_eval gdc_nc_0215)

lemma gdc_nc_0216: "gdc_sub None 216"
  by (gdc_eval gdc_nc_0216)

lemma gdc_nc_0217: "gdc_sub None 217"
  by (gdc_eval gdc_nc_0217)

lemma gdc_nc_0218: "gdc_sub None 218"
  by (gdc_eval gdc_nc_0218)

lemma gdc_nc_0219: "gdc_sub None 219"
  by (gdc_eval gdc_nc_0219)

lemma gdc_nc_0220: "gdc_sub None 220"
  by (gdc_eval gdc_nc_0220)

lemma gdc_nc_0221: "gdc_sub None 221"
  by (gdc_eval gdc_nc_0221)

lemma gdc_nc_0222: "gdc_sub None 222"
  by (gdc_eval gdc_nc_0222)

lemma gdc_nc_0223: "gdc_sub None 223"
  by (gdc_eval gdc_nc_0223)

lemma gupt_nc_013: "[208..<224] = [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]"
  by (simp add: upt_rec)

lemma gsec_nc_013: "\<forall>j\<in>{16 * 13..<16 * 13 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 13..<16 * 13 + 16}"
  then have "j \<in> set [208..<224]" unfolding set_upt by simp
  then have "j \<in> set [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]" unfolding gupt_nc_013 .
  then show "gdc_sub None j" using gdc_nc_0208 gdc_nc_0209 gdc_nc_0210 gdc_nc_0211 gdc_nc_0212 gdc_nc_0213 gdc_nc_0214 gdc_nc_0215 gdc_nc_0216 gdc_nc_0217 gdc_nc_0218 gdc_nc_0219 gdc_nc_0220 gdc_nc_0221 gdc_nc_0222 gdc_nc_0223
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

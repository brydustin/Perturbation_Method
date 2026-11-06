theory GDCX_nc_015
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0240: "gdc_sub None 240"
  by (gdc_eval gdc_nc_0240)

lemma gdc_nc_0241: "gdc_sub None 241"
  by (gdc_eval gdc_nc_0241)

lemma gdc_nc_0242: "gdc_sub None 242"
  by (gdc_eval gdc_nc_0242)

lemma gdc_nc_0243: "gdc_sub None 243"
  by (gdc_eval gdc_nc_0243)

lemma gdc_nc_0244: "gdc_sub None 244"
  by (gdc_eval gdc_nc_0244)

lemma gdc_nc_0245: "gdc_sub None 245"
  by (gdc_eval gdc_nc_0245)

lemma gdc_nc_0246: "gdc_sub None 246"
  by (gdc_eval gdc_nc_0246)

lemma gdc_nc_0247: "gdc_sub None 247"
  by (gdc_eval gdc_nc_0247)

lemma gdc_nc_0248: "gdc_sub None 248"
  by (gdc_eval gdc_nc_0248)

lemma gdc_nc_0249: "gdc_sub None 249"
  by (gdc_eval gdc_nc_0249)

lemma gdc_nc_0250: "gdc_sub None 250"
  by (gdc_eval gdc_nc_0250)

lemma gdc_nc_0251: "gdc_sub None 251"
  by (gdc_eval gdc_nc_0251)

lemma gdc_nc_0252: "gdc_sub None 252"
  by (gdc_eval gdc_nc_0252)

lemma gdc_nc_0253: "gdc_sub None 253"
  by (gdc_eval gdc_nc_0253)

lemma gdc_nc_0254: "gdc_sub None 254"
  by (gdc_eval gdc_nc_0254)

lemma gdc_nc_0255: "gdc_sub None 255"
  by (gdc_eval gdc_nc_0255)

lemma gupt_nc_015: "[240..<256] = [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]"
  by (simp add: upt_rec)

lemma gsec_nc_015: "\<forall>j\<in>{16 * 15..<16 * 15 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 15..<16 * 15 + 16}"
  then have "j \<in> set [240..<256]" unfolding set_upt by simp
  then have "j \<in> set [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]" unfolding gupt_nc_015 .
  then show "gdc_sub None j" using gdc_nc_0240 gdc_nc_0241 gdc_nc_0242 gdc_nc_0243 gdc_nc_0244 gdc_nc_0245 gdc_nc_0246 gdc_nc_0247 gdc_nc_0248 gdc_nc_0249 gdc_nc_0250 gdc_nc_0251 gdc_nc_0252 gdc_nc_0253 gdc_nc_0254 gdc_nc_0255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

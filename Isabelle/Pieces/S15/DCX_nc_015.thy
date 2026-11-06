theory DCX_nc_015
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0240: "dc_sub None 240"
  by (dc_eval dc_nc_0240)

lemma dc_nc_0241: "dc_sub None 241"
  by (dc_eval dc_nc_0241)

lemma dc_nc_0242: "dc_sub None 242"
  by (dc_eval dc_nc_0242)

lemma dc_nc_0243: "dc_sub None 243"
  by (dc_eval dc_nc_0243)

lemma dc_nc_0244: "dc_sub None 244"
  by (dc_eval dc_nc_0244)

lemma dc_nc_0245: "dc_sub None 245"
  by (dc_eval dc_nc_0245)

lemma dc_nc_0246: "dc_sub None 246"
  by (dc_eval dc_nc_0246)

lemma dc_nc_0247: "dc_sub None 247"
  by (dc_eval dc_nc_0247)

lemma dc_nc_0248: "dc_sub None 248"
  by (dc_eval dc_nc_0248)

lemma dc_nc_0249: "dc_sub None 249"
  by (dc_eval dc_nc_0249)

lemma dc_nc_0250: "dc_sub None 250"
  by (dc_eval dc_nc_0250)

lemma dc_nc_0251: "dc_sub None 251"
  by (dc_eval dc_nc_0251)

lemma dc_nc_0252: "dc_sub None 252"
  by (dc_eval dc_nc_0252)

lemma dc_nc_0253: "dc_sub None 253"
  by (dc_eval dc_nc_0253)

lemma dc_nc_0254: "dc_sub None 254"
  by (dc_eval dc_nc_0254)

lemma dc_nc_0255: "dc_sub None 255"
  by (dc_eval dc_nc_0255)

lemma upt_nc_015: "[240..<256] = [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]"
  by (simp add: upt_rec)

lemma sec_nc_015: "\<forall>j\<in>{16 * 15..<16 * 15 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 15..<16 * 15 + 16}"
  then have "j \<in> set [240..<256]" unfolding set_upt by simp
  then have "j \<in> set [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]" unfolding upt_nc_015 .
  then show "dc_sub None j" using dc_nc_0240 dc_nc_0241 dc_nc_0242 dc_nc_0243 dc_nc_0244 dc_nc_0245 dc_nc_0246 dc_nc_0247 dc_nc_0248 dc_nc_0249 dc_nc_0250 dc_nc_0251 dc_nc_0252 dc_nc_0253 dc_nc_0254 dc_nc_0255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

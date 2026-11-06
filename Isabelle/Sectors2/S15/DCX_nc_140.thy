theory DCX_nc_140
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_2240: "dc_sub None 2240"
  by (dc_eval dc_nc_2240)

lemma dc_nc_2241: "dc_sub None 2241"
  by (dc_eval dc_nc_2241)

lemma dc_nc_2242: "dc_sub None 2242"
  by (dc_eval dc_nc_2242)

lemma dc_nc_2243: "dc_sub None 2243"
  by (dc_eval dc_nc_2243)

lemma dc_nc_2244: "dc_sub None 2244"
  by (dc_eval dc_nc_2244)

lemma dc_nc_2245: "dc_sub None 2245"
  by (dc_eval dc_nc_2245)

lemma dc_nc_2246: "dc_sub None 2246"
  by (dc_eval dc_nc_2246)

lemma dc_nc_2247: "dc_sub None 2247"
  by (dc_eval dc_nc_2247)

lemma dc_nc_2248: "dc_sub None 2248"
  by (dc_eval dc_nc_2248)

lemma dc_nc_2249: "dc_sub None 2249"
  by (dc_eval dc_nc_2249)

lemma dc_nc_2250: "dc_sub None 2250"
  by (dc_eval dc_nc_2250)

lemma dc_nc_2251: "dc_sub None 2251"
  by (dc_eval dc_nc_2251)

lemma dc_nc_2252: "dc_sub None 2252"
  by (dc_eval dc_nc_2252)

lemma dc_nc_2253: "dc_sub None 2253"
  by (dc_eval dc_nc_2253)

lemma dc_nc_2254: "dc_sub None 2254"
  by (dc_eval dc_nc_2254)

lemma dc_nc_2255: "dc_sub None 2255"
  by (dc_eval dc_nc_2255)

lemma upt_nc_140: "[2240..<2256] = [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]"
  by (simp add: upt_rec)

lemma sec_nc_140: "\<forall>j\<in>{16 * 140..<16 * 140 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 140..<16 * 140 + 16}"
  then have "j \<in> set [2240..<2256]" unfolding set_upt by simp
  then have "j \<in> set [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]" unfolding upt_nc_140 .
  then show "dc_sub None j" using dc_nc_2240 dc_nc_2241 dc_nc_2242 dc_nc_2243 dc_nc_2244 dc_nc_2245 dc_nc_2246 dc_nc_2247 dc_nc_2248 dc_nc_2249 dc_nc_2250 dc_nc_2251 dc_nc_2252 dc_nc_2253 dc_nc_2254 dc_nc_2255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

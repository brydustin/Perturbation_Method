theory GOCX_nc_140
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2240: "goc_sub None 2240"
  by (goc_eval goc_nc_2240)

lemma goc_nc_2241: "goc_sub None 2241"
  by (goc_eval goc_nc_2241)

lemma goc_nc_2242: "goc_sub None 2242"
  by (goc_eval goc_nc_2242)

lemma goc_nc_2243: "goc_sub None 2243"
  by (goc_eval goc_nc_2243)

lemma goc_nc_2244: "goc_sub None 2244"
  by (goc_eval goc_nc_2244)

lemma goc_nc_2245: "goc_sub None 2245"
  by (goc_eval goc_nc_2245)

lemma goc_nc_2246: "goc_sub None 2246"
  by (goc_eval goc_nc_2246)

lemma goc_nc_2247: "goc_sub None 2247"
  by (goc_eval goc_nc_2247)

lemma goc_nc_2248: "goc_sub None 2248"
  by (goc_eval goc_nc_2248)

lemma goc_nc_2249: "goc_sub None 2249"
  by (goc_eval goc_nc_2249)

lemma goc_nc_2250: "goc_sub None 2250"
  by (goc_eval goc_nc_2250)

lemma goc_nc_2251: "goc_sub None 2251"
  by (goc_eval goc_nc_2251)

lemma goc_nc_2252: "goc_sub None 2252"
  by (goc_eval goc_nc_2252)

lemma goc_nc_2253: "goc_sub None 2253"
  by (goc_eval goc_nc_2253)

lemma goc_nc_2254: "goc_sub None 2254"
  by (goc_eval goc_nc_2254)

lemma goc_nc_2255: "goc_sub None 2255"
  by (goc_eval goc_nc_2255)

lemma gupt_nc_140: "[2240..<2256] = [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]"
  by (simp add: upt_rec)

lemma gsec_nc_140: "\<forall>j\<in>{16 * 140..<16 * 140 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 140..<16 * 140 + 16}"
  then have "j \<in> set [2240..<2256]" unfolding set_upt by simp
  then have "j \<in> set [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]" unfolding gupt_nc_140 .
  then show "goc_sub None j" using goc_nc_2240 goc_nc_2241 goc_nc_2242 goc_nc_2243 goc_nc_2244 goc_nc_2245 goc_nc_2246 goc_nc_2247 goc_nc_2248 goc_nc_2249 goc_nc_2250 goc_nc_2251 goc_nc_2252 goc_nc_2253 goc_nc_2254 goc_nc_2255
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

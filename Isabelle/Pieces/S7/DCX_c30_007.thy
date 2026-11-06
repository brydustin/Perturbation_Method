theory DCX_c30_007
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0112: "dc_sub dc_b30 112"
  by (dc_eval dc_c30_0112)

lemma dc_c30_0113: "dc_sub dc_b30 113"
  by (dc_eval dc_c30_0113)

lemma dc_c30_0114: "dc_sub dc_b30 114"
  by (dc_eval dc_c30_0114)

lemma dc_c30_0115: "dc_sub dc_b30 115"
  by (dc_eval dc_c30_0115)

lemma dc_c30_0116: "dc_sub dc_b30 116"
  by (dc_eval dc_c30_0116)

lemma dc_c30_0117: "dc_sub dc_b30 117"
  by (dc_eval dc_c30_0117)

lemma dc_c30_0118: "dc_sub dc_b30 118"
  by (dc_eval dc_c30_0118)

lemma dc_c30_0119: "dc_sub dc_b30 119"
  by (dc_eval dc_c30_0119)

lemma dc_c30_0120: "dc_sub dc_b30 120"
  by (dc_eval dc_c30_0120)

lemma dc_c30_0121: "dc_sub dc_b30 121"
  by (dc_eval dc_c30_0121)

lemma dc_c30_0122: "dc_sub dc_b30 122"
  by (dc_eval dc_c30_0122)

lemma dc_c30_0123: "dc_sub dc_b30 123"
  by (dc_eval dc_c30_0123)

lemma dc_c30_0124: "dc_sub dc_b30 124"
  by (dc_eval dc_c30_0124)

lemma dc_c30_0125: "dc_sub dc_b30 125"
  by (dc_eval dc_c30_0125)

lemma dc_c30_0126: "dc_sub dc_b30 126"
  by (dc_eval dc_c30_0126)

lemma dc_c30_0127: "dc_sub dc_b30 127"
  by (dc_eval dc_c30_0127)

lemma upt_c30_007: "[112..<128] = [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]"
  by (simp add: upt_rec)

lemma sec_c30_007: "\<forall>j\<in>{16 * 7..<16 * 7 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 7..<16 * 7 + 16}"
  then have "j \<in> set [112..<128]" unfolding set_upt by simp
  then have "j \<in> set [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]" unfolding upt_c30_007 .
  then show "dc_sub dc_b30 j" using dc_c30_0112 dc_c30_0113 dc_c30_0114 dc_c30_0115 dc_c30_0116 dc_c30_0117 dc_c30_0118 dc_c30_0119 dc_c30_0120 dc_c30_0121 dc_c30_0122 dc_c30_0123 dc_c30_0124 dc_c30_0125 dc_c30_0126 dc_c30_0127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

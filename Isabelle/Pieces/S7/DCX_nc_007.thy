theory DCX_nc_007
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0112: "dc_sub None 112"
  by (dc_eval dc_nc_0112)

lemma dc_nc_0113: "dc_sub None 113"
  by (dc_eval dc_nc_0113)

lemma dc_nc_0114: "dc_sub None 114"
  by (dc_eval dc_nc_0114)

lemma dc_nc_0115: "dc_sub None 115"
  by (dc_eval dc_nc_0115)

lemma dc_nc_0116: "dc_sub None 116"
  by (dc_eval dc_nc_0116)

lemma dc_nc_0117: "dc_sub None 117"
  by (dc_eval dc_nc_0117)

lemma dc_nc_0118: "dc_sub None 118"
  by (dc_eval dc_nc_0118)

lemma dc_nc_0119: "dc_sub None 119"
  by (dc_eval dc_nc_0119)

lemma dc_nc_0120: "dc_sub None 120"
  by (dc_eval dc_nc_0120)

lemma dc_nc_0121: "dc_sub None 121"
  by (dc_eval dc_nc_0121)

lemma dc_nc_0122: "dc_sub None 122"
  by (dc_eval dc_nc_0122)

lemma dc_nc_0123: "dc_sub None 123"
  by (dc_eval dc_nc_0123)

lemma dc_nc_0124: "dc_sub None 124"
  by (dc_eval dc_nc_0124)

lemma dc_nc_0125: "dc_sub None 125"
  by (dc_eval dc_nc_0125)

lemma dc_nc_0126: "dc_sub None 126"
  by (dc_eval dc_nc_0126)

lemma dc_nc_0127: "dc_sub None 127"
  by (dc_eval dc_nc_0127)

lemma upt_nc_007: "[112..<128] = [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]"
  by (simp add: upt_rec)

lemma sec_nc_007: "\<forall>j\<in>{16 * 7..<16 * 7 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 7..<16 * 7 + 16}"
  then have "j \<in> set [112..<128]" unfolding set_upt by simp
  then have "j \<in> set [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]" unfolding upt_nc_007 .
  then show "dc_sub None j" using dc_nc_0112 dc_nc_0113 dc_nc_0114 dc_nc_0115 dc_nc_0116 dc_nc_0117 dc_nc_0118 dc_nc_0119 dc_nc_0120 dc_nc_0121 dc_nc_0122 dc_nc_0123 dc_nc_0124 dc_nc_0125 dc_nc_0126 dc_nc_0127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

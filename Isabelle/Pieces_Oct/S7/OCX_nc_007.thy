theory OCX_nc_007
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0112: "oc_sub None 112"
  by (oc_eval oc_nc_0112)

lemma oc_nc_0113: "oc_sub None 113"
  by (oc_eval oc_nc_0113)

lemma oc_nc_0114: "oc_sub None 114"
  by (oc_eval oc_nc_0114)

lemma oc_nc_0115: "oc_sub None 115"
  by (oc_eval oc_nc_0115)

lemma oc_nc_0116: "oc_sub None 116"
  by (oc_eval oc_nc_0116)

lemma oc_nc_0117: "oc_sub None 117"
  by (oc_eval oc_nc_0117)

lemma oc_nc_0118: "oc_sub None 118"
  by (oc_eval oc_nc_0118)

lemma oc_nc_0119: "oc_sub None 119"
  by (oc_eval oc_nc_0119)

lemma oc_nc_0120: "oc_sub None 120"
  by (oc_eval oc_nc_0120)

lemma oc_nc_0121: "oc_sub None 121"
  by (oc_eval oc_nc_0121)

lemma oc_nc_0122: "oc_sub None 122"
  by (oc_eval oc_nc_0122)

lemma oc_nc_0123: "oc_sub None 123"
  by (oc_eval oc_nc_0123)

lemma oc_nc_0124: "oc_sub None 124"
  by (oc_eval oc_nc_0124)

lemma oc_nc_0125: "oc_sub None 125"
  by (oc_eval oc_nc_0125)

lemma oc_nc_0126: "oc_sub None 126"
  by (oc_eval oc_nc_0126)

lemma oc_nc_0127: "oc_sub None 127"
  by (oc_eval oc_nc_0127)

lemma upt_nc_007: "[112..<128] = [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]"
  by (simp add: upt_rec)

lemma sec_nc_007: "\<forall>j\<in>{16 * 7..<16 * 7 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 7..<16 * 7 + 16}"
  then have "j \<in> set [112..<128]" unfolding set_upt by simp
  then have "j \<in> set [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]" unfolding upt_nc_007 .
  then show "oc_sub None j" using oc_nc_0112 oc_nc_0113 oc_nc_0114 oc_nc_0115 oc_nc_0116 oc_nc_0117 oc_nc_0118 oc_nc_0119 oc_nc_0120 oc_nc_0121 oc_nc_0122 oc_nc_0123 oc_nc_0124 oc_nc_0125 oc_nc_0126 oc_nc_0127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

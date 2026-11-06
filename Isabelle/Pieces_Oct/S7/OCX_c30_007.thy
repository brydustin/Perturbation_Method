theory OCX_c30_007
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0112: "oc_sub oc_b30 112"
  by (oc_eval oc_c30_0112)

lemma oc_c30_0113: "oc_sub oc_b30 113"
  by (oc_eval oc_c30_0113)

lemma oc_c30_0114: "oc_sub oc_b30 114"
  by (oc_eval oc_c30_0114)

lemma oc_c30_0115: "oc_sub oc_b30 115"
  by (oc_eval oc_c30_0115)

lemma oc_c30_0116: "oc_sub oc_b30 116"
  by (oc_eval oc_c30_0116)

lemma oc_c30_0117: "oc_sub oc_b30 117"
  by (oc_eval oc_c30_0117)

lemma oc_c30_0118: "oc_sub oc_b30 118"
  by (oc_eval oc_c30_0118)

lemma oc_c30_0119: "oc_sub oc_b30 119"
  by (oc_eval oc_c30_0119)

lemma oc_c30_0120: "oc_sub oc_b30 120"
  by (oc_eval oc_c30_0120)

lemma oc_c30_0121: "oc_sub oc_b30 121"
  by (oc_eval oc_c30_0121)

lemma oc_c30_0122: "oc_sub oc_b30 122"
  by (oc_eval oc_c30_0122)

lemma oc_c30_0123: "oc_sub oc_b30 123"
  by (oc_eval oc_c30_0123)

lemma oc_c30_0124: "oc_sub oc_b30 124"
  by (oc_eval oc_c30_0124)

lemma oc_c30_0125: "oc_sub oc_b30 125"
  by (oc_eval oc_c30_0125)

lemma oc_c30_0126: "oc_sub oc_b30 126"
  by (oc_eval oc_c30_0126)

lemma oc_c30_0127: "oc_sub oc_b30 127"
  by (oc_eval oc_c30_0127)

lemma upt_c30_007: "[112..<128] = [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]"
  by (simp add: upt_rec)

lemma sec_c30_007: "\<forall>j\<in>{16 * 7..<16 * 7 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 7..<16 * 7 + 16}"
  then have "j \<in> set [112..<128]" unfolding set_upt by simp
  then have "j \<in> set [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]" unfolding upt_c30_007 .
  then show "oc_sub oc_b30 j" using oc_c30_0112 oc_c30_0113 oc_c30_0114 oc_c30_0115 oc_c30_0116 oc_c30_0117 oc_c30_0118 oc_c30_0119 oc_c30_0120 oc_c30_0121 oc_c30_0122 oc_c30_0123 oc_c30_0124 oc_c30_0125 oc_c30_0126 oc_c30_0127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

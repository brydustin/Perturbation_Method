theory GOCX_nc_007
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0112: "goc_sub None 112"
  by (goc_eval goc_nc_0112)

lemma goc_nc_0113: "goc_sub None 113"
  by (goc_eval goc_nc_0113)

lemma goc_nc_0114: "goc_sub None 114"
  by (goc_eval goc_nc_0114)

lemma goc_nc_0115: "goc_sub None 115"
  by (goc_eval goc_nc_0115)

lemma goc_nc_0116: "goc_sub None 116"
  by (goc_eval goc_nc_0116)

lemma goc_nc_0117: "goc_sub None 117"
  by (goc_eval goc_nc_0117)

lemma goc_nc_0118: "goc_sub None 118"
  by (goc_eval goc_nc_0118)

lemma goc_nc_0119: "goc_sub None 119"
  by (goc_eval goc_nc_0119)

lemma goc_nc_0120: "goc_sub None 120"
  by (goc_eval goc_nc_0120)

lemma goc_nc_0121: "goc_sub None 121"
  by (goc_eval goc_nc_0121)

lemma goc_nc_0122: "goc_sub None 122"
  by (goc_eval goc_nc_0122)

lemma goc_nc_0123: "goc_sub None 123"
  by (goc_eval goc_nc_0123)

lemma goc_nc_0124: "goc_sub None 124"
  by (goc_eval goc_nc_0124)

lemma goc_nc_0125: "goc_sub None 125"
  by (goc_eval goc_nc_0125)

lemma goc_nc_0126: "goc_sub None 126"
  by (goc_eval goc_nc_0126)

lemma goc_nc_0127: "goc_sub None 127"
  by (goc_eval goc_nc_0127)

lemma gupt_nc_007: "[112..<128] = [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]"
  by (simp add: upt_rec)

lemma gsec_nc_007: "\<forall>j\<in>{16 * 7..<16 * 7 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 7..<16 * 7 + 16}"
  then have "j \<in> set [112..<128]" unfolding set_upt by simp
  then have "j \<in> set [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]" unfolding gupt_nc_007 .
  then show "goc_sub None j" using goc_nc_0112 goc_nc_0113 goc_nc_0114 goc_nc_0115 goc_nc_0116 goc_nc_0117 goc_nc_0118 goc_nc_0119 goc_nc_0120 goc_nc_0121 goc_nc_0122 goc_nc_0123 goc_nc_0124 goc_nc_0125 goc_nc_0126 goc_nc_0127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

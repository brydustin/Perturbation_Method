theory GDCX_nc_007
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0112: "gdc_sub None 112"
  by (gdc_eval gdc_nc_0112)

lemma gdc_nc_0113: "gdc_sub None 113"
  by (gdc_eval gdc_nc_0113)

lemma gdc_nc_0114: "gdc_sub None 114"
  by (gdc_eval gdc_nc_0114)

lemma gdc_nc_0115: "gdc_sub None 115"
  by (gdc_eval gdc_nc_0115)

lemma gdc_nc_0116: "gdc_sub None 116"
  by (gdc_eval gdc_nc_0116)

lemma gdc_nc_0117: "gdc_sub None 117"
  by (gdc_eval gdc_nc_0117)

lemma gdc_nc_0118: "gdc_sub None 118"
  by (gdc_eval gdc_nc_0118)

lemma gdc_nc_0119: "gdc_sub None 119"
  by (gdc_eval gdc_nc_0119)

lemma gdc_nc_0120: "gdc_sub None 120"
  by (gdc_eval gdc_nc_0120)

lemma gdc_nc_0121: "gdc_sub None 121"
  by (gdc_eval gdc_nc_0121)

lemma gdc_nc_0122: "gdc_sub None 122"
  by (gdc_eval gdc_nc_0122)

lemma gdc_nc_0123: "gdc_sub None 123"
  by (gdc_eval gdc_nc_0123)

lemma gdc_nc_0124: "gdc_sub None 124"
  by (gdc_eval gdc_nc_0124)

lemma gdc_nc_0125: "gdc_sub None 125"
  by (gdc_eval gdc_nc_0125)

lemma gdc_nc_0126: "gdc_sub None 126"
  by (gdc_eval gdc_nc_0126)

lemma gdc_nc_0127: "gdc_sub None 127"
  by (gdc_eval gdc_nc_0127)

lemma gupt_nc_007: "[112..<128] = [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]"
  by (simp add: upt_rec)

lemma gsec_nc_007: "\<forall>j\<in>{16 * 7..<16 * 7 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 7..<16 * 7 + 16}"
  then have "j \<in> set [112..<128]" unfolding set_upt by simp
  then have "j \<in> set [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]" unfolding gupt_nc_007 .
  then show "gdc_sub None j" using gdc_nc_0112 gdc_nc_0113 gdc_nc_0114 gdc_nc_0115 gdc_nc_0116 gdc_nc_0117 gdc_nc_0118 gdc_nc_0119 gdc_nc_0120 gdc_nc_0121 gdc_nc_0122 gdc_nc_0123 gdc_nc_0124 gdc_nc_0125 gdc_nc_0126 gdc_nc_0127
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

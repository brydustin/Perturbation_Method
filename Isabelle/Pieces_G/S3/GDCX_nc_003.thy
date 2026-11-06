theory GDCX_nc_003
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0048: "gdc_sub None 48"
  by (gdc_eval gdc_nc_0048)

lemma gdc_nc_0049: "gdc_sub None 49"
  by (gdc_eval gdc_nc_0049)

lemma gdc_nc_0050: "gdc_sub None 50"
  by (gdc_eval gdc_nc_0050)

lemma gdc_nc_0051: "gdc_sub None 51"
  by (gdc_eval gdc_nc_0051)

lemma gdc_nc_0052: "gdc_sub None 52"
  by (gdc_eval gdc_nc_0052)

lemma gdc_nc_0053: "gdc_sub None 53"
  by (gdc_eval gdc_nc_0053)

lemma gdc_nc_0054: "gdc_sub None 54"
  by (gdc_eval gdc_nc_0054)

lemma gdc_nc_0055: "gdc_sub None 55"
  by (gdc_eval gdc_nc_0055)

lemma gdc_nc_0056: "gdc_sub None 56"
  by (gdc_eval gdc_nc_0056)

lemma gdc_nc_0057: "gdc_sub None 57"
  by (gdc_eval gdc_nc_0057)

lemma gdc_nc_0058: "gdc_sub None 58"
  by (gdc_eval gdc_nc_0058)

lemma gdc_nc_0059: "gdc_sub None 59"
  by (gdc_eval gdc_nc_0059)

lemma gdc_nc_0060: "gdc_sub None 60"
  by (gdc_eval gdc_nc_0060)

lemma gdc_nc_0061: "gdc_sub None 61"
  by (gdc_eval gdc_nc_0061)

lemma gdc_nc_0062: "gdc_sub None 62"
  by (gdc_eval gdc_nc_0062)

lemma gdc_nc_0063: "gdc_sub None 63"
  by (gdc_eval gdc_nc_0063)

lemma gupt_nc_003: "[48..<64] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]"
  by (simp add: upt_rec)

lemma gsec_nc_003: "\<forall>j\<in>{16 * 3..<16 * 3 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 3..<16 * 3 + 16}"
  then have "j \<in> set [48..<64]" unfolding set_upt by simp
  then have "j \<in> set [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]" unfolding gupt_nc_003 .
  then show "gdc_sub None j" using gdc_nc_0048 gdc_nc_0049 gdc_nc_0050 gdc_nc_0051 gdc_nc_0052 gdc_nc_0053 gdc_nc_0054 gdc_nc_0055 gdc_nc_0056 gdc_nc_0057 gdc_nc_0058 gdc_nc_0059 gdc_nc_0060 gdc_nc_0061 gdc_nc_0062 gdc_nc_0063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

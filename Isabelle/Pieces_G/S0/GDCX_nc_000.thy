theory GDCX_nc_000
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_0000: "gdc_sub None 0"
  by (gdc_eval gdc_nc_0000)

lemma gdc_nc_0001: "gdc_sub None 1"
  by (gdc_eval gdc_nc_0001)

lemma gdc_nc_0002: "gdc_sub None 2"
  by (gdc_eval gdc_nc_0002)

lemma gdc_nc_0003: "gdc_sub None 3"
  by (gdc_eval gdc_nc_0003)

lemma gdc_nc_0004: "gdc_sub None 4"
  by (gdc_eval gdc_nc_0004)

lemma gdc_nc_0005: "gdc_sub None 5"
  by (gdc_eval gdc_nc_0005)

lemma gdc_nc_0006: "gdc_sub None 6"
  by (gdc_eval gdc_nc_0006)

lemma gdc_nc_0007: "gdc_sub None 7"
  by (gdc_eval gdc_nc_0007)

lemma gdc_nc_0008: "gdc_sub None 8"
  by (gdc_eval gdc_nc_0008)

lemma gdc_nc_0009: "gdc_sub None 9"
  by (gdc_eval gdc_nc_0009)

lemma gdc_nc_0010: "gdc_sub None 10"
  by (gdc_eval gdc_nc_0010)

lemma gdc_nc_0011: "gdc_sub None 11"
  by (gdc_eval gdc_nc_0011)

lemma gdc_nc_0012: "gdc_sub None 12"
  by (gdc_eval gdc_nc_0012)

lemma gdc_nc_0013: "gdc_sub None 13"
  by (gdc_eval gdc_nc_0013)

lemma gdc_nc_0014: "gdc_sub None 14"
  by (gdc_eval gdc_nc_0014)

lemma gdc_nc_0015: "gdc_sub None 15"
  by (gdc_eval gdc_nc_0015)

lemma gupt_nc_000: "[0..<16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
  by (simp add: upt_rec)

lemma gsec_nc_000: "\<forall>j\<in>{16 * 0..<16 * 0 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 0..<16 * 0 + 16}"
  then have "j \<in> set [0..<16]" unfolding set_upt by simp
  then have "j \<in> set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]" unfolding gupt_nc_000 .
  then show "gdc_sub None j" using gdc_nc_0000 gdc_nc_0001 gdc_nc_0002 gdc_nc_0003 gdc_nc_0004 gdc_nc_0005 gdc_nc_0006 gdc_nc_0007 gdc_nc_0008 gdc_nc_0009 gdc_nc_0010 gdc_nc_0011 gdc_nc_0012 gdc_nc_0013 gdc_nc_0014 gdc_nc_0015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

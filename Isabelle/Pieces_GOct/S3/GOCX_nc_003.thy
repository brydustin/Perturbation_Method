theory GOCX_nc_003
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0048: "goc_sub None 48"
  by (goc_eval goc_nc_0048)

lemma goc_nc_0049: "goc_sub None 49"
  by (goc_eval goc_nc_0049)

lemma goc_nc_0050: "goc_sub None 50"
  by (goc_eval goc_nc_0050)

lemma goc_nc_0051: "goc_sub None 51"
  by (goc_eval goc_nc_0051)

lemma goc_nc_0052: "goc_sub None 52"
  by (goc_eval goc_nc_0052)

lemma goc_nc_0053: "goc_sub None 53"
  by (goc_eval goc_nc_0053)

lemma goc_nc_0054: "goc_sub None 54"
  by (goc_eval goc_nc_0054)

lemma goc_nc_0055: "goc_sub None 55"
  by (goc_eval goc_nc_0055)

lemma goc_nc_0056: "goc_sub None 56"
  by (goc_eval goc_nc_0056)

lemma goc_nc_0057: "goc_sub None 57"
  by (goc_eval goc_nc_0057)

lemma goc_nc_0058: "goc_sub None 58"
  by (goc_eval goc_nc_0058)

lemma goc_nc_0059: "goc_sub None 59"
  by (goc_eval goc_nc_0059)

lemma goc_nc_0060: "goc_sub None 60"
  by (goc_eval goc_nc_0060)

lemma goc_nc_0061: "goc_sub None 61"
  by (goc_eval goc_nc_0061)

lemma goc_nc_0062: "goc_sub None 62"
  by (goc_eval goc_nc_0062)

lemma goc_nc_0063: "goc_sub None 63"
  by (goc_eval goc_nc_0063)

lemma gupt_nc_003: "[48..<64] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]"
  by (simp add: upt_rec)

lemma gsec_nc_003: "\<forall>j\<in>{16 * 3..<16 * 3 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 3..<16 * 3 + 16}"
  then have "j \<in> set [48..<64]" unfolding set_upt by simp
  then have "j \<in> set [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]" unfolding gupt_nc_003 .
  then show "goc_sub None j" using goc_nc_0048 goc_nc_0049 goc_nc_0050 goc_nc_0051 goc_nc_0052 goc_nc_0053 goc_nc_0054 goc_nc_0055 goc_nc_0056 goc_nc_0057 goc_nc_0058 goc_nc_0059 goc_nc_0060 goc_nc_0061 goc_nc_0062 goc_nc_0063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

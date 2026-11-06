theory OCX_nc_003
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_0048: "oc_sub None 48"
  by (oc_eval oc_nc_0048)

lemma oc_nc_0049: "oc_sub None 49"
  by (oc_eval oc_nc_0049)

lemma oc_nc_0050: "oc_sub None 50"
  by (oc_eval oc_nc_0050)

lemma oc_nc_0051: "oc_sub None 51"
  by (oc_eval oc_nc_0051)

lemma oc_nc_0052: "oc_sub None 52"
  by (oc_eval oc_nc_0052)

lemma oc_nc_0053: "oc_sub None 53"
  by (oc_eval oc_nc_0053)

lemma oc_nc_0054: "oc_sub None 54"
  by (oc_eval oc_nc_0054)

lemma oc_nc_0055: "oc_sub None 55"
  by (oc_eval oc_nc_0055)

lemma oc_nc_0056: "oc_sub None 56"
  by (oc_eval oc_nc_0056)

lemma oc_nc_0057: "oc_sub None 57"
  by (oc_eval oc_nc_0057)

lemma oc_nc_0058: "oc_sub None 58"
  by (oc_eval oc_nc_0058)

lemma oc_nc_0059: "oc_sub None 59"
  by (oc_eval oc_nc_0059)

lemma oc_nc_0060: "oc_sub None 60"
  by (oc_eval oc_nc_0060)

lemma oc_nc_0061: "oc_sub None 61"
  by (oc_eval oc_nc_0061)

lemma oc_nc_0062: "oc_sub None 62"
  by (oc_eval oc_nc_0062)

lemma oc_nc_0063: "oc_sub None 63"
  by (oc_eval oc_nc_0063)

lemma upt_nc_003: "[48..<64] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]"
  by (simp add: upt_rec)

lemma sec_nc_003: "\<forall>j\<in>{16 * 3..<16 * 3 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 3..<16 * 3 + 16}"
  then have "j \<in> set [48..<64]" unfolding set_upt by simp
  then have "j \<in> set [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]" unfolding upt_nc_003 .
  then show "oc_sub None j" using oc_nc_0048 oc_nc_0049 oc_nc_0050 oc_nc_0051 oc_nc_0052 oc_nc_0053 oc_nc_0054 oc_nc_0055 oc_nc_0056 oc_nc_0057 oc_nc_0058 oc_nc_0059 oc_nc_0060 oc_nc_0061 oc_nc_0062 oc_nc_0063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

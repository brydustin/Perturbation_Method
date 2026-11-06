theory OCX_c30_003
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_0048: "oc_sub oc_b30 48"
  by (oc_eval oc_c30_0048)

lemma oc_c30_0049: "oc_sub oc_b30 49"
  by (oc_eval oc_c30_0049)

lemma oc_c30_0050: "oc_sub oc_b30 50"
  by (oc_eval oc_c30_0050)

lemma oc_c30_0051: "oc_sub oc_b30 51"
  by (oc_eval oc_c30_0051)

lemma oc_c30_0052: "oc_sub oc_b30 52"
  by (oc_eval oc_c30_0052)

lemma oc_c30_0053: "oc_sub oc_b30 53"
  by (oc_eval oc_c30_0053)

lemma oc_c30_0054: "oc_sub oc_b30 54"
  by (oc_eval oc_c30_0054)

lemma oc_c30_0055: "oc_sub oc_b30 55"
  by (oc_eval oc_c30_0055)

lemma oc_c30_0056: "oc_sub oc_b30 56"
  by (oc_eval oc_c30_0056)

lemma oc_c30_0057: "oc_sub oc_b30 57"
  by (oc_eval oc_c30_0057)

lemma oc_c30_0058: "oc_sub oc_b30 58"
  by (oc_eval oc_c30_0058)

lemma oc_c30_0059: "oc_sub oc_b30 59"
  by (oc_eval oc_c30_0059)

lemma oc_c30_0060: "oc_sub oc_b30 60"
  by (oc_eval oc_c30_0060)

lemma oc_c30_0061: "oc_sub oc_b30 61"
  by (oc_eval oc_c30_0061)

lemma oc_c30_0062: "oc_sub oc_b30 62"
  by (oc_eval oc_c30_0062)

lemma oc_c30_0063: "oc_sub oc_b30 63"
  by (oc_eval oc_c30_0063)

lemma upt_c30_003: "[48..<64] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]"
  by (simp add: upt_rec)

lemma sec_c30_003: "\<forall>j\<in>{16 * 3..<16 * 3 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 3..<16 * 3 + 16}"
  then have "j \<in> set [48..<64]" unfolding set_upt by simp
  then have "j \<in> set [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]" unfolding upt_c30_003 .
  then show "oc_sub oc_b30 j" using oc_c30_0048 oc_c30_0049 oc_c30_0050 oc_c30_0051 oc_c30_0052 oc_c30_0053 oc_c30_0054 oc_c30_0055 oc_c30_0056 oc_c30_0057 oc_c30_0058 oc_c30_0059 oc_c30_0060 oc_c30_0061 oc_c30_0062 oc_c30_0063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

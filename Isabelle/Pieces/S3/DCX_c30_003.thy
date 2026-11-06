theory DCX_c30_003
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0048: "dc_sub dc_b30 48"
  by (dc_eval dc_c30_0048)

lemma dc_c30_0049: "dc_sub dc_b30 49"
  by (dc_eval dc_c30_0049)

lemma dc_c30_0050: "dc_sub dc_b30 50"
  by (dc_eval dc_c30_0050)

lemma dc_c30_0051: "dc_sub dc_b30 51"
  by (dc_eval dc_c30_0051)

lemma dc_c30_0052: "dc_sub dc_b30 52"
  by (dc_eval dc_c30_0052)

lemma dc_c30_0053: "dc_sub dc_b30 53"
  by (dc_eval dc_c30_0053)

lemma dc_c30_0054: "dc_sub dc_b30 54"
  by (dc_eval dc_c30_0054)

lemma dc_c30_0055: "dc_sub dc_b30 55"
  by (dc_eval dc_c30_0055)

lemma dc_c30_0056: "dc_sub dc_b30 56"
  by (dc_eval dc_c30_0056)

lemma dc_c30_0057: "dc_sub dc_b30 57"
  by (dc_eval dc_c30_0057)

lemma dc_c30_0058: "dc_sub dc_b30 58"
  by (dc_eval dc_c30_0058)

lemma dc_c30_0059: "dc_sub dc_b30 59"
  by (dc_eval dc_c30_0059)

lemma dc_c30_0060: "dc_sub dc_b30 60"
  by (dc_eval dc_c30_0060)

lemma dc_c30_0061: "dc_sub dc_b30 61"
  by (dc_eval dc_c30_0061)

lemma dc_c30_0062: "dc_sub dc_b30 62"
  by (dc_eval dc_c30_0062)

lemma dc_c30_0063: "dc_sub dc_b30 63"
  by (dc_eval dc_c30_0063)

lemma upt_c30_003: "[48..<64] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]"
  by (simp add: upt_rec)

lemma sec_c30_003: "\<forall>j\<in>{16 * 3..<16 * 3 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 3..<16 * 3 + 16}"
  then have "j \<in> set [48..<64]" unfolding set_upt by simp
  then have "j \<in> set [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]" unfolding upt_c30_003 .
  then show "dc_sub dc_b30 j" using dc_c30_0048 dc_c30_0049 dc_c30_0050 dc_c30_0051 dc_c30_0052 dc_c30_0053 dc_c30_0054 dc_c30_0055 dc_c30_0056 dc_c30_0057 dc_c30_0058 dc_c30_0059 dc_c30_0060 dc_c30_0061 dc_c30_0062 dc_c30_0063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

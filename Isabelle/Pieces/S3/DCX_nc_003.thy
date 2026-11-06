theory DCX_nc_003
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0048: "dc_sub None 48"
  by (dc_eval dc_nc_0048)

lemma dc_nc_0049: "dc_sub None 49"
  by (dc_eval dc_nc_0049)

lemma dc_nc_0050: "dc_sub None 50"
  by (dc_eval dc_nc_0050)

lemma dc_nc_0051: "dc_sub None 51"
  by (dc_eval dc_nc_0051)

lemma dc_nc_0052: "dc_sub None 52"
  by (dc_eval dc_nc_0052)

lemma dc_nc_0053: "dc_sub None 53"
  by (dc_eval dc_nc_0053)

lemma dc_nc_0054: "dc_sub None 54"
  by (dc_eval dc_nc_0054)

lemma dc_nc_0055: "dc_sub None 55"
  by (dc_eval dc_nc_0055)

lemma dc_nc_0056: "dc_sub None 56"
  by (dc_eval dc_nc_0056)

lemma dc_nc_0057: "dc_sub None 57"
  by (dc_eval dc_nc_0057)

lemma dc_nc_0058: "dc_sub None 58"
  by (dc_eval dc_nc_0058)

lemma dc_nc_0059: "dc_sub None 59"
  by (dc_eval dc_nc_0059)

lemma dc_nc_0060: "dc_sub None 60"
  by (dc_eval dc_nc_0060)

lemma dc_nc_0061: "dc_sub None 61"
  by (dc_eval dc_nc_0061)

lemma dc_nc_0062: "dc_sub None 62"
  by (dc_eval dc_nc_0062)

lemma dc_nc_0063: "dc_sub None 63"
  by (dc_eval dc_nc_0063)

lemma upt_nc_003: "[48..<64] = [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]"
  by (simp add: upt_rec)

lemma sec_nc_003: "\<forall>j\<in>{16 * 3..<16 * 3 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 3..<16 * 3 + 16}"
  then have "j \<in> set [48..<64]" unfolding set_upt by simp
  then have "j \<in> set [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]" unfolding upt_nc_003 .
  then show "dc_sub None j" using dc_nc_0048 dc_nc_0049 dc_nc_0050 dc_nc_0051 dc_nc_0052 dc_nc_0053 dc_nc_0054 dc_nc_0055 dc_nc_0056 dc_nc_0057 dc_nc_0058 dc_nc_0059 dc_nc_0060 dc_nc_0061 dc_nc_0062 dc_nc_0063
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

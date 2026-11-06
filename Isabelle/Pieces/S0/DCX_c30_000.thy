theory DCX_c30_000
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_0000: "dc_sub dc_b30 0"
  by (dc_eval dc_c30_0000)

lemma dc_c30_0001: "dc_sub dc_b30 1"
  by (dc_eval dc_c30_0001)

lemma dc_c30_0002: "dc_sub dc_b30 2"
  by (dc_eval dc_c30_0002)

lemma dc_c30_0003: "dc_sub dc_b30 3"
  by (dc_eval dc_c30_0003)

lemma dc_c30_0004: "dc_sub dc_b30 4"
  by (dc_eval dc_c30_0004)

lemma dc_c30_0005: "dc_sub dc_b30 5"
  by (dc_eval dc_c30_0005)

lemma dc_c30_0006: "dc_sub dc_b30 6"
  by (dc_eval dc_c30_0006)

lemma dc_c30_0007: "dc_sub dc_b30 7"
  by (dc_eval dc_c30_0007)

lemma dc_c30_0008: "dc_sub dc_b30 8"
  by (dc_eval dc_c30_0008)

lemma dc_c30_0009: "dc_sub dc_b30 9"
  by (dc_eval dc_c30_0009)

lemma dc_c30_0010: "dc_sub dc_b30 10"
  by (dc_eval dc_c30_0010)

lemma dc_c30_0011: "dc_sub dc_b30 11"
  by (dc_eval dc_c30_0011)

lemma dc_c30_0012: "dc_sub dc_b30 12"
  by (dc_eval dc_c30_0012)

lemma dc_c30_0013: "dc_sub dc_b30 13"
  by (dc_eval dc_c30_0013)

lemma dc_c30_0014: "dc_sub dc_b30 14"
  by (dc_eval dc_c30_0014)

lemma dc_c30_0015: "dc_sub dc_b30 15"
  by (dc_eval dc_c30_0015)

lemma upt_c30_000: "[0..<16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
  by (simp add: upt_rec)

lemma sec_c30_000: "\<forall>j\<in>{16 * 0..<16 * 0 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 0..<16 * 0 + 16}"
  then have "j \<in> set [0..<16]" unfolding set_upt by simp
  then have "j \<in> set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]" unfolding upt_c30_000 .
  then show "dc_sub dc_b30 j" using dc_c30_0000 dc_c30_0001 dc_c30_0002 dc_c30_0003 dc_c30_0004 dc_c30_0005 dc_c30_0006 dc_c30_0007 dc_c30_0008 dc_c30_0009 dc_c30_0010 dc_c30_0011 dc_c30_0012 dc_c30_0013 dc_c30_0014 dc_c30_0015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

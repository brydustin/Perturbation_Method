theory DCX_nc_000
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_0000: "dc_sub None 0"
  by (dc_eval dc_nc_0000)

lemma dc_nc_0001: "dc_sub None 1"
  by (dc_eval dc_nc_0001)

lemma dc_nc_0002: "dc_sub None 2"
  by (dc_eval dc_nc_0002)

lemma dc_nc_0003: "dc_sub None 3"
  by (dc_eval dc_nc_0003)

lemma dc_nc_0004: "dc_sub None 4"
  by (dc_eval dc_nc_0004)

lemma dc_nc_0005: "dc_sub None 5"
  by (dc_eval dc_nc_0005)

lemma dc_nc_0006: "dc_sub None 6"
  by (dc_eval dc_nc_0006)

lemma dc_nc_0007: "dc_sub None 7"
  by (dc_eval dc_nc_0007)

lemma dc_nc_0008: "dc_sub None 8"
  by (dc_eval dc_nc_0008)

lemma dc_nc_0009: "dc_sub None 9"
  by (dc_eval dc_nc_0009)

lemma dc_nc_0010: "dc_sub None 10"
  by (dc_eval dc_nc_0010)

lemma dc_nc_0011: "dc_sub None 11"
  by (dc_eval dc_nc_0011)

lemma dc_nc_0012: "dc_sub None 12"
  by (dc_eval dc_nc_0012)

lemma dc_nc_0013: "dc_sub None 13"
  by (dc_eval dc_nc_0013)

lemma dc_nc_0014: "dc_sub None 14"
  by (dc_eval dc_nc_0014)

lemma dc_nc_0015: "dc_sub None 15"
  by (dc_eval dc_nc_0015)

lemma upt_nc_000: "[0..<16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
  by (simp add: upt_rec)

lemma sec_nc_000: "\<forall>j\<in>{16 * 0..<16 * 0 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 0..<16 * 0 + 16}"
  then have "j \<in> set [0..<16]" unfolding set_upt by simp
  then have "j \<in> set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]" unfolding upt_nc_000 .
  then show "dc_sub None j" using dc_nc_0000 dc_nc_0001 dc_nc_0002 dc_nc_0003 dc_nc_0004 dc_nc_0005 dc_nc_0006 dc_nc_0007 dc_nc_0008 dc_nc_0009 dc_nc_0010 dc_nc_0011 dc_nc_0012 dc_nc_0013 dc_nc_0014 dc_nc_0015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

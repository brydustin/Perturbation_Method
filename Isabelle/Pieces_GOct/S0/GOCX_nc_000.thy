theory GOCX_nc_000
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_0000: "goc_sub None 0"
  by (goc_eval goc_nc_0000)

lemma goc_nc_0001: "goc_sub None 1"
  by (goc_eval goc_nc_0001)

lemma goc_nc_0002: "goc_sub None 2"
  by (goc_eval goc_nc_0002)

lemma goc_nc_0003: "goc_sub None 3"
  by (goc_eval goc_nc_0003)

lemma goc_nc_0004: "goc_sub None 4"
  by (goc_eval goc_nc_0004)

lemma goc_nc_0005: "goc_sub None 5"
  by (goc_eval goc_nc_0005)

lemma goc_nc_0006: "goc_sub None 6"
  by (goc_eval goc_nc_0006)

lemma goc_nc_0007: "goc_sub None 7"
  by (goc_eval goc_nc_0007)

lemma goc_nc_0008: "goc_sub None 8"
  by (goc_eval goc_nc_0008)

lemma goc_nc_0009: "goc_sub None 9"
  by (goc_eval goc_nc_0009)

lemma goc_nc_0010: "goc_sub None 10"
  by (goc_eval goc_nc_0010)

lemma goc_nc_0011: "goc_sub None 11"
  by (goc_eval goc_nc_0011)

lemma goc_nc_0012: "goc_sub None 12"
  by (goc_eval goc_nc_0012)

lemma goc_nc_0013: "goc_sub None 13"
  by (goc_eval goc_nc_0013)

lemma goc_nc_0014: "goc_sub None 14"
  by (goc_eval goc_nc_0014)

lemma goc_nc_0015: "goc_sub None 15"
  by (goc_eval goc_nc_0015)

lemma gupt_nc_000: "[0..<16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]"
  by (simp add: upt_rec)

lemma gsec_nc_000: "\<forall>j\<in>{16 * 0..<16 * 0 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 0..<16 * 0 + 16}"
  then have "j \<in> set [0..<16]" unfolding set_upt by simp
  then have "j \<in> set [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]" unfolding gupt_nc_000 .
  then show "goc_sub None j" using goc_nc_0000 goc_nc_0001 goc_nc_0002 goc_nc_0003 goc_nc_0004 goc_nc_0005 goc_nc_0006 goc_nc_0007 goc_nc_0008 goc_nc_0009 goc_nc_0010 goc_nc_0011 goc_nc_0012 goc_nc_0013 goc_nc_0014 goc_nc_0015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

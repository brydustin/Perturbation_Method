theory GOCX_nc_123
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1968: "goc_sub None 1968"
  by (goc_eval goc_nc_1968)

lemma goc_nc_1969: "goc_sub None 1969"
  by (goc_eval goc_nc_1969)

lemma goc_nc_1970: "goc_sub None 1970"
  by (goc_eval goc_nc_1970)

lemma goc_nc_1971: "goc_sub None 1971"
  by (goc_eval goc_nc_1971)

lemma goc_nc_1972: "goc_sub None 1972"
  by (goc_eval goc_nc_1972)

lemma goc_nc_1973: "goc_sub None 1973"
  by (goc_eval goc_nc_1973)

lemma goc_nc_1974: "goc_sub None 1974"
  by (goc_eval goc_nc_1974)

lemma goc_nc_1975: "goc_sub None 1975"
  by (goc_eval goc_nc_1975)

lemma goc_nc_1976: "goc_sub None 1976"
  by (goc_eval goc_nc_1976)

lemma goc_nc_1977: "goc_sub None 1977"
  by (goc_eval goc_nc_1977)

lemma goc_nc_1978: "goc_sub None 1978"
  by (goc_eval goc_nc_1978)

lemma goc_nc_1979: "goc_sub None 1979"
  by (goc_eval goc_nc_1979)

lemma goc_nc_1980: "goc_sub None 1980"
  by (goc_eval goc_nc_1980)

lemma goc_nc_1981: "goc_sub None 1981"
  by (goc_eval goc_nc_1981)

lemma goc_nc_1982: "goc_sub None 1982"
  by (goc_eval goc_nc_1982)

lemma goc_nc_1983: "goc_sub None 1983"
  by (goc_eval goc_nc_1983)

lemma gupt_nc_123: "[1968..<1984] = [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]"
  by (simp add: upt_rec)

lemma gsec_nc_123: "\<forall>j\<in>{16 * 123..<16 * 123 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 123..<16 * 123 + 16}"
  then have "j \<in> set [1968..<1984]" unfolding set_upt by simp
  then have "j \<in> set [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]" unfolding gupt_nc_123 .
  then show "goc_sub None j" using goc_nc_1968 goc_nc_1969 goc_nc_1970 goc_nc_1971 goc_nc_1972 goc_nc_1973 goc_nc_1974 goc_nc_1975 goc_nc_1976 goc_nc_1977 goc_nc_1978 goc_nc_1979 goc_nc_1980 goc_nc_1981 goc_nc_1982 goc_nc_1983
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

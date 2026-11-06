theory GDCX_nc_123
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1968: "gdc_sub None 1968"
  by (gdc_eval gdc_nc_1968)

lemma gdc_nc_1969: "gdc_sub None 1969"
  by (gdc_eval gdc_nc_1969)

lemma gdc_nc_1970: "gdc_sub None 1970"
  by (gdc_eval gdc_nc_1970)

lemma gdc_nc_1971: "gdc_sub None 1971"
  by (gdc_eval gdc_nc_1971)

lemma gdc_nc_1972: "gdc_sub None 1972"
  by (gdc_eval gdc_nc_1972)

lemma gdc_nc_1973: "gdc_sub None 1973"
  by (gdc_eval gdc_nc_1973)

lemma gdc_nc_1974: "gdc_sub None 1974"
  by (gdc_eval gdc_nc_1974)

lemma gdc_nc_1975: "gdc_sub None 1975"
  by (gdc_eval gdc_nc_1975)

lemma gdc_nc_1976: "gdc_sub None 1976"
  by (gdc_eval gdc_nc_1976)

lemma gdc_nc_1977: "gdc_sub None 1977"
  by (gdc_eval gdc_nc_1977)

lemma gdc_nc_1978: "gdc_sub None 1978"
  by (gdc_eval gdc_nc_1978)

lemma gdc_nc_1979: "gdc_sub None 1979"
  by (gdc_eval gdc_nc_1979)

lemma gdc_nc_1980: "gdc_sub None 1980"
  by (gdc_eval gdc_nc_1980)

lemma gdc_nc_1981: "gdc_sub None 1981"
  by (gdc_eval gdc_nc_1981)

lemma gdc_nc_1982: "gdc_sub None 1982"
  by (gdc_eval gdc_nc_1982)

lemma gdc_nc_1983: "gdc_sub None 1983"
  by (gdc_eval gdc_nc_1983)

lemma gupt_nc_123: "[1968..<1984] = [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]"
  by (simp add: upt_rec)

lemma gsec_nc_123: "\<forall>j\<in>{16 * 123..<16 * 123 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 123..<16 * 123 + 16}"
  then have "j \<in> set [1968..<1984]" unfolding set_upt by simp
  then have "j \<in> set [1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983]" unfolding gupt_nc_123 .
  then show "gdc_sub None j" using gdc_nc_1968 gdc_nc_1969 gdc_nc_1970 gdc_nc_1971 gdc_nc_1972 gdc_nc_1973 gdc_nc_1974 gdc_nc_1975 gdc_nc_1976 gdc_nc_1977 gdc_nc_1978 gdc_nc_1979 gdc_nc_1980 gdc_nc_1981 gdc_nc_1982 gdc_nc_1983
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

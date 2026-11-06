theory DCX_nc_124
  imports "DC_Tables.DC_Tables"
begin

lemma dc_nc_1984: "dc_sub None 1984"
  by (dc_eval dc_nc_1984)

lemma dc_nc_1985: "dc_sub None 1985"
  by (dc_eval dc_nc_1985)

lemma dc_nc_1986: "dc_sub None 1986"
  by (dc_eval dc_nc_1986)

lemma dc_nc_1987: "dc_sub None 1987"
  by (dc_eval dc_nc_1987)

lemma dc_nc_1988: "dc_sub None 1988"
  by (dc_eval dc_nc_1988)

lemma dc_nc_1989: "dc_sub None 1989"
  by (dc_eval dc_nc_1989)

lemma dc_nc_1990: "dc_sub None 1990"
  by (dc_eval dc_nc_1990)

lemma dc_nc_1991: "dc_sub None 1991"
  by (dc_eval dc_nc_1991)

lemma dc_nc_1992: "dc_sub None 1992"
  by (dc_eval dc_nc_1992)

lemma dc_nc_1993: "dc_sub None 1993"
  by (dc_eval dc_nc_1993)

lemma dc_nc_1994: "dc_sub None 1994"
  by (dc_eval dc_nc_1994)

lemma dc_nc_1995: "dc_sub None 1995"
  by (dc_eval dc_nc_1995)

lemma dc_nc_1996: "dc_sub None 1996"
  by (dc_eval dc_nc_1996)

lemma dc_nc_1997: "dc_sub None 1997"
  by (dc_eval dc_nc_1997)

lemma dc_nc_1998: "dc_sub None 1998"
  by (dc_eval dc_nc_1998)

lemma dc_nc_1999: "dc_sub None 1999"
  by (dc_eval dc_nc_1999)

lemma upt_nc_124: "[1984..<2000] = [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]"
  by (simp add: upt_rec)

lemma sec_nc_124: "\<forall>j\<in>{16 * 124..<16 * 124 + 16}. dc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 124..<16 * 124 + 16}"
  then have "j \<in> set [1984..<2000]" unfolding set_upt by simp
  then have "j \<in> set [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]" unfolding upt_nc_124 .
  then show "dc_sub None j" using dc_nc_1984 dc_nc_1985 dc_nc_1986 dc_nc_1987 dc_nc_1988 dc_nc_1989 dc_nc_1990 dc_nc_1991 dc_nc_1992 dc_nc_1993 dc_nc_1994 dc_nc_1995 dc_nc_1996 dc_nc_1997 dc_nc_1998 dc_nc_1999
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory OCX_nc_124
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_1984: "oc_sub None 1984"
  by (oc_eval oc_nc_1984)

lemma oc_nc_1985: "oc_sub None 1985"
  by (oc_eval oc_nc_1985)

lemma oc_nc_1986: "oc_sub None 1986"
  by (oc_eval oc_nc_1986)

lemma oc_nc_1987: "oc_sub None 1987"
  by (oc_eval oc_nc_1987)

lemma oc_nc_1988: "oc_sub None 1988"
  by (oc_eval oc_nc_1988)

lemma oc_nc_1989: "oc_sub None 1989"
  by (oc_eval oc_nc_1989)

lemma oc_nc_1990: "oc_sub None 1990"
  by (oc_eval oc_nc_1990)

lemma oc_nc_1991: "oc_sub None 1991"
  by (oc_eval oc_nc_1991)

lemma oc_nc_1992: "oc_sub None 1992"
  by (oc_eval oc_nc_1992)

lemma oc_nc_1993: "oc_sub None 1993"
  by (oc_eval oc_nc_1993)

lemma oc_nc_1994: "oc_sub None 1994"
  by (oc_eval oc_nc_1994)

lemma oc_nc_1995: "oc_sub None 1995"
  by (oc_eval oc_nc_1995)

lemma oc_nc_1996: "oc_sub None 1996"
  by (oc_eval oc_nc_1996)

lemma oc_nc_1997: "oc_sub None 1997"
  by (oc_eval oc_nc_1997)

lemma oc_nc_1998: "oc_sub None 1998"
  by (oc_eval oc_nc_1998)

lemma oc_nc_1999: "oc_sub None 1999"
  by (oc_eval oc_nc_1999)

lemma upt_nc_124: "[1984..<2000] = [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]"
  by (simp add: upt_rec)

lemma sec_nc_124: "\<forall>j\<in>{16 * 124..<16 * 124 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 124..<16 * 124 + 16}"
  then have "j \<in> set [1984..<2000]" unfolding set_upt by simp
  then have "j \<in> set [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]" unfolding upt_nc_124 .
  then show "oc_sub None j" using oc_nc_1984 oc_nc_1985 oc_nc_1986 oc_nc_1987 oc_nc_1988 oc_nc_1989 oc_nc_1990 oc_nc_1991 oc_nc_1992 oc_nc_1993 oc_nc_1994 oc_nc_1995 oc_nc_1996 oc_nc_1997 oc_nc_1998 oc_nc_1999
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory OCX_c30_124
  imports "OC_Tables.OC_Tables"
begin

lemma oc_c30_1984: "oc_sub oc_b30 1984"
  by (oc_eval oc_c30_1984)

lemma oc_c30_1985: "oc_sub oc_b30 1985"
  by (oc_eval oc_c30_1985)

lemma oc_c30_1986: "oc_sub oc_b30 1986"
  by (oc_eval oc_c30_1986)

lemma oc_c30_1987: "oc_sub oc_b30 1987"
  by (oc_eval oc_c30_1987)

lemma oc_c30_1988: "oc_sub oc_b30 1988"
  by (oc_eval oc_c30_1988)

lemma oc_c30_1989: "oc_sub oc_b30 1989"
  by (oc_eval oc_c30_1989)

lemma oc_c30_1990: "oc_sub oc_b30 1990"
  by (oc_eval oc_c30_1990)

lemma oc_c30_1991: "oc_sub oc_b30 1991"
  by (oc_eval oc_c30_1991)

lemma oc_c30_1992: "oc_sub oc_b30 1992"
  by (oc_eval oc_c30_1992)

lemma oc_c30_1993: "oc_sub oc_b30 1993"
  by (oc_eval oc_c30_1993)

lemma oc_c30_1994: "oc_sub oc_b30 1994"
  by (oc_eval oc_c30_1994)

lemma oc_c30_1995: "oc_sub oc_b30 1995"
  by (oc_eval oc_c30_1995)

lemma oc_c30_1996: "oc_sub oc_b30 1996"
  by (oc_eval oc_c30_1996)

lemma oc_c30_1997: "oc_sub oc_b30 1997"
  by (oc_eval oc_c30_1997)

lemma oc_c30_1998: "oc_sub oc_b30 1998"
  by (oc_eval oc_c30_1998)

lemma oc_c30_1999: "oc_sub oc_b30 1999"
  by (oc_eval oc_c30_1999)

lemma upt_c30_124: "[1984..<2000] = [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]"
  by (simp add: upt_rec)

lemma sec_c30_124: "\<forall>j\<in>{16 * 124..<16 * 124 + 16}. oc_sub oc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 124..<16 * 124 + 16}"
  then have "j \<in> set [1984..<2000]" unfolding set_upt by simp
  then have "j \<in> set [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]" unfolding upt_c30_124 .
  then show "oc_sub oc_b30 j" using oc_c30_1984 oc_c30_1985 oc_c30_1986 oc_c30_1987 oc_c30_1988 oc_c30_1989 oc_c30_1990 oc_c30_1991 oc_c30_1992 oc_c30_1993 oc_c30_1994 oc_c30_1995 oc_c30_1996 oc_c30_1997 oc_c30_1998 oc_c30_1999
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

theory DCX_c30_124
  imports "DC_Tables.DC_Tables"
begin

lemma dc_c30_1984: "dc_sub dc_b30 1984"
  by (dc_eval dc_c30_1984)

lemma dc_c30_1985: "dc_sub dc_b30 1985"
  by (dc_eval dc_c30_1985)

lemma dc_c30_1986: "dc_sub dc_b30 1986"
  by (dc_eval dc_c30_1986)

lemma dc_c30_1987: "dc_sub dc_b30 1987"
  by (dc_eval dc_c30_1987)

lemma dc_c30_1988: "dc_sub dc_b30 1988"
  by (dc_eval dc_c30_1988)

lemma dc_c30_1989: "dc_sub dc_b30 1989"
  by (dc_eval dc_c30_1989)

lemma dc_c30_1990: "dc_sub dc_b30 1990"
  by (dc_eval dc_c30_1990)

lemma dc_c30_1991: "dc_sub dc_b30 1991"
  by (dc_eval dc_c30_1991)

lemma dc_c30_1992: "dc_sub dc_b30 1992"
  by (dc_eval dc_c30_1992)

lemma dc_c30_1993: "dc_sub dc_b30 1993"
  by (dc_eval dc_c30_1993)

lemma dc_c30_1994: "dc_sub dc_b30 1994"
  by (dc_eval dc_c30_1994)

lemma dc_c30_1995: "dc_sub dc_b30 1995"
  by (dc_eval dc_c30_1995)

lemma dc_c30_1996: "dc_sub dc_b30 1996"
  by (dc_eval dc_c30_1996)

lemma dc_c30_1997: "dc_sub dc_b30 1997"
  by (dc_eval dc_c30_1997)

lemma dc_c30_1998: "dc_sub dc_b30 1998"
  by (dc_eval dc_c30_1998)

lemma dc_c30_1999: "dc_sub dc_b30 1999"
  by (dc_eval dc_c30_1999)

lemma upt_c30_124: "[1984..<2000] = [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]"
  by (simp add: upt_rec)

lemma sec_c30_124: "\<forall>j\<in>{16 * 124..<16 * 124 + 16}. dc_sub dc_b30 j"
proof
  fix j :: nat assume "j \<in> {16 * 124..<16 * 124 + 16}"
  then have "j \<in> set [1984..<2000]" unfolding set_upt by simp
  then have "j \<in> set [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]" unfolding upt_c30_124 .
  then show "dc_sub dc_b30 j" using dc_c30_1984 dc_c30_1985 dc_c30_1986 dc_c30_1987 dc_c30_1988 dc_c30_1989 dc_c30_1990 dc_c30_1991 dc_c30_1992 dc_c30_1993 dc_c30_1994 dc_c30_1995 dc_c30_1996 dc_c30_1997 dc_c30_1998 dc_c30_1999
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

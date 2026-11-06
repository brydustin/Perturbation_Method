theory GOCX_nc_124
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_1984: "goc_sub None 1984"
  by (goc_eval goc_nc_1984)

lemma goc_nc_1985: "goc_sub None 1985"
  by (goc_eval goc_nc_1985)

lemma goc_nc_1986: "goc_sub None 1986"
  by (goc_eval goc_nc_1986)

lemma goc_nc_1987: "goc_sub None 1987"
  by (goc_eval goc_nc_1987)

lemma goc_nc_1988: "goc_sub None 1988"
  by (goc_eval goc_nc_1988)

lemma goc_nc_1989: "goc_sub None 1989"
  by (goc_eval goc_nc_1989)

lemma goc_nc_1990: "goc_sub None 1990"
  by (goc_eval goc_nc_1990)

lemma goc_nc_1991: "goc_sub None 1991"
  by (goc_eval goc_nc_1991)

lemma goc_nc_1992: "goc_sub None 1992"
  by (goc_eval goc_nc_1992)

lemma goc_nc_1993: "goc_sub None 1993"
  by (goc_eval goc_nc_1993)

lemma goc_nc_1994: "goc_sub None 1994"
  by (goc_eval goc_nc_1994)

lemma goc_nc_1995: "goc_sub None 1995"
  by (goc_eval goc_nc_1995)

lemma goc_nc_1996: "goc_sub None 1996"
  by (goc_eval goc_nc_1996)

lemma goc_nc_1997: "goc_sub None 1997"
  by (goc_eval goc_nc_1997)

lemma goc_nc_1998: "goc_sub None 1998"
  by (goc_eval goc_nc_1998)

lemma goc_nc_1999: "goc_sub None 1999"
  by (goc_eval goc_nc_1999)

lemma gupt_nc_124: "[1984..<2000] = [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]"
  by (simp add: upt_rec)

lemma gsec_nc_124: "\<forall>j\<in>{16 * 124..<16 * 124 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 124..<16 * 124 + 16}"
  then have "j \<in> set [1984..<2000]" unfolding set_upt by simp
  then have "j \<in> set [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]" unfolding gupt_nc_124 .
  then show "goc_sub None j" using goc_nc_1984 goc_nc_1985 goc_nc_1986 goc_nc_1987 goc_nc_1988 goc_nc_1989 goc_nc_1990 goc_nc_1991 goc_nc_1992 goc_nc_1993 goc_nc_1994 goc_nc_1995 goc_nc_1996 goc_nc_1997 goc_nc_1998 goc_nc_1999
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

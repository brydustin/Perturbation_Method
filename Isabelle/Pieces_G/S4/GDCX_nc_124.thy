theory GDCX_nc_124
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_1984: "gdc_sub None 1984"
  by (gdc_eval gdc_nc_1984)

lemma gdc_nc_1985: "gdc_sub None 1985"
  by (gdc_eval gdc_nc_1985)

lemma gdc_nc_1986: "gdc_sub None 1986"
  by (gdc_eval gdc_nc_1986)

lemma gdc_nc_1987: "gdc_sub None 1987"
  by (gdc_eval gdc_nc_1987)

lemma gdc_nc_1988: "gdc_sub None 1988"
  by (gdc_eval gdc_nc_1988)

lemma gdc_nc_1989: "gdc_sub None 1989"
  by (gdc_eval gdc_nc_1989)

lemma gdc_nc_1990: "gdc_sub None 1990"
  by (gdc_eval gdc_nc_1990)

lemma gdc_nc_1991: "gdc_sub None 1991"
  by (gdc_eval gdc_nc_1991)

lemma gdc_nc_1992: "gdc_sub None 1992"
  by (gdc_eval gdc_nc_1992)

lemma gdc_nc_1993: "gdc_sub None 1993"
  by (gdc_eval gdc_nc_1993)

lemma gdc_nc_1994: "gdc_sub None 1994"
  by (gdc_eval gdc_nc_1994)

lemma gdc_nc_1995: "gdc_sub None 1995"
  by (gdc_eval gdc_nc_1995)

lemma gdc_nc_1996: "gdc_sub None 1996"
  by (gdc_eval gdc_nc_1996)

lemma gdc_nc_1997: "gdc_sub None 1997"
  by (gdc_eval gdc_nc_1997)

lemma gdc_nc_1998: "gdc_sub None 1998"
  by (gdc_eval gdc_nc_1998)

lemma gdc_nc_1999: "gdc_sub None 1999"
  by (gdc_eval gdc_nc_1999)

lemma gupt_nc_124: "[1984..<2000] = [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]"
  by (simp add: upt_rec)

lemma gsec_nc_124: "\<forall>j\<in>{16 * 124..<16 * 124 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 124..<16 * 124 + 16}"
  then have "j \<in> set [1984..<2000]" unfolding set_upt by simp
  then have "j \<in> set [1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999]" unfolding gupt_nc_124 .
  then show "gdc_sub None j" using gdc_nc_1984 gdc_nc_1985 gdc_nc_1986 gdc_nc_1987 gdc_nc_1988 gdc_nc_1989 gdc_nc_1990 gdc_nc_1991 gdc_nc_1992 gdc_nc_1993 gdc_nc_1994 gdc_nc_1995 gdc_nc_1996 gdc_nc_1997 gdc_nc_1998 gdc_nc_1999
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

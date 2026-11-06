theory GOCX_nc_125
  imports "GOC_Tables.GOC_Tables"
begin

lemma goc_nc_2000: "goc_sub None 2000"
  by (goc_eval goc_nc_2000)

lemma goc_nc_2001: "goc_sub None 2001"
  by (goc_eval goc_nc_2001)

lemma goc_nc_2002: "goc_sub None 2002"
  by (goc_eval goc_nc_2002)

lemma goc_nc_2003: "goc_sub None 2003"
  by (goc_eval goc_nc_2003)

lemma goc_nc_2004: "goc_sub None 2004"
  by (goc_eval goc_nc_2004)

lemma goc_nc_2005: "goc_sub None 2005"
  by (goc_eval goc_nc_2005)

lemma goc_nc_2006: "goc_sub None 2006"
  by (goc_eval goc_nc_2006)

lemma goc_nc_2007: "goc_sub None 2007"
  by (goc_eval goc_nc_2007)

lemma goc_nc_2008: "goc_sub None 2008"
  by (goc_eval goc_nc_2008)

lemma goc_nc_2009: "goc_sub None 2009"
  by (goc_eval goc_nc_2009)

lemma goc_nc_2010: "goc_sub None 2010"
  by (goc_eval goc_nc_2010)

lemma goc_nc_2011: "goc_sub None 2011"
  by (goc_eval goc_nc_2011)

lemma goc_nc_2012: "goc_sub None 2012"
  by (goc_eval goc_nc_2012)

lemma goc_nc_2013: "goc_sub None 2013"
  by (goc_eval goc_nc_2013)

lemma goc_nc_2014: "goc_sub None 2014"
  by (goc_eval goc_nc_2014)

lemma goc_nc_2015: "goc_sub None 2015"
  by (goc_eval goc_nc_2015)

lemma gupt_nc_125: "[2000..<2016] = [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]"
  by (simp add: upt_rec)

lemma gsec_nc_125: "\<forall>j\<in>{16 * 125..<16 * 125 + 16}. goc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 125..<16 * 125 + 16}"
  then have "j \<in> set [2000..<2016]" unfolding set_upt by simp
  then have "j \<in> set [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]" unfolding gupt_nc_125 .
  then show "goc_sub None j" using goc_nc_2000 goc_nc_2001 goc_nc_2002 goc_nc_2003 goc_nc_2004 goc_nc_2005 goc_nc_2006 goc_nc_2007 goc_nc_2008 goc_nc_2009 goc_nc_2010 goc_nc_2011 goc_nc_2012 goc_nc_2013 goc_nc_2014 goc_nc_2015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

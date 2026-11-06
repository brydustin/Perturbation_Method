theory GDCX_nc_125
  imports "GDC_Tables.GDC_Tables"
begin

lemma gdc_nc_2000: "gdc_sub None 2000"
  by (gdc_eval gdc_nc_2000)

lemma gdc_nc_2001: "gdc_sub None 2001"
  by (gdc_eval gdc_nc_2001)

lemma gdc_nc_2002: "gdc_sub None 2002"
  by (gdc_eval gdc_nc_2002)

lemma gdc_nc_2003: "gdc_sub None 2003"
  by (gdc_eval gdc_nc_2003)

lemma gdc_nc_2004: "gdc_sub None 2004"
  by (gdc_eval gdc_nc_2004)

lemma gdc_nc_2005: "gdc_sub None 2005"
  by (gdc_eval gdc_nc_2005)

lemma gdc_nc_2006: "gdc_sub None 2006"
  by (gdc_eval gdc_nc_2006)

lemma gdc_nc_2007: "gdc_sub None 2007"
  by (gdc_eval gdc_nc_2007)

lemma gdc_nc_2008: "gdc_sub None 2008"
  by (gdc_eval gdc_nc_2008)

lemma gdc_nc_2009: "gdc_sub None 2009"
  by (gdc_eval gdc_nc_2009)

lemma gdc_nc_2010: "gdc_sub None 2010"
  by (gdc_eval gdc_nc_2010)

lemma gdc_nc_2011: "gdc_sub None 2011"
  by (gdc_eval gdc_nc_2011)

lemma gdc_nc_2012: "gdc_sub None 2012"
  by (gdc_eval gdc_nc_2012)

lemma gdc_nc_2013: "gdc_sub None 2013"
  by (gdc_eval gdc_nc_2013)

lemma gdc_nc_2014: "gdc_sub None 2014"
  by (gdc_eval gdc_nc_2014)

lemma gdc_nc_2015: "gdc_sub None 2015"
  by (gdc_eval gdc_nc_2015)

lemma gupt_nc_125: "[2000..<2016] = [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]"
  by (simp add: upt_rec)

lemma gsec_nc_125: "\<forall>j\<in>{16 * 125..<16 * 125 + 16}. gdc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 125..<16 * 125 + 16}"
  then have "j \<in> set [2000..<2016]" unfolding set_upt by simp
  then have "j \<in> set [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]" unfolding gupt_nc_125 .
  then show "gdc_sub None j" using gdc_nc_2000 gdc_nc_2001 gdc_nc_2002 gdc_nc_2003 gdc_nc_2004 gdc_nc_2005 gdc_nc_2006 gdc_nc_2007 gdc_nc_2008 gdc_nc_2009 gdc_nc_2010 gdc_nc_2011 gdc_nc_2012 gdc_nc_2013 gdc_nc_2014 gdc_nc_2015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

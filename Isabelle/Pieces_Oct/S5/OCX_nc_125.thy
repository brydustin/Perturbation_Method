theory OCX_nc_125
  imports "OC_Tables.OC_Tables"
begin

lemma oc_nc_2000: "oc_sub None 2000"
  by (oc_eval oc_nc_2000)

lemma oc_nc_2001: "oc_sub None 2001"
  by (oc_eval oc_nc_2001)

lemma oc_nc_2002: "oc_sub None 2002"
  by (oc_eval oc_nc_2002)

lemma oc_nc_2003: "oc_sub None 2003"
  by (oc_eval oc_nc_2003)

lemma oc_nc_2004: "oc_sub None 2004"
  by (oc_eval oc_nc_2004)

lemma oc_nc_2005: "oc_sub None 2005"
  by (oc_eval oc_nc_2005)

lemma oc_nc_2006: "oc_sub None 2006"
  by (oc_eval oc_nc_2006)

lemma oc_nc_2007: "oc_sub None 2007"
  by (oc_eval oc_nc_2007)

lemma oc_nc_2008: "oc_sub None 2008"
  by (oc_eval oc_nc_2008)

lemma oc_nc_2009: "oc_sub None 2009"
  by (oc_eval oc_nc_2009)

lemma oc_nc_2010: "oc_sub None 2010"
  by (oc_eval oc_nc_2010)

lemma oc_nc_2011: "oc_sub None 2011"
  by (oc_eval oc_nc_2011)

lemma oc_nc_2012: "oc_sub None 2012"
  by (oc_eval oc_nc_2012)

lemma oc_nc_2013: "oc_sub None 2013"
  by (oc_eval oc_nc_2013)

lemma oc_nc_2014: "oc_sub None 2014"
  by (oc_eval oc_nc_2014)

lemma oc_nc_2015: "oc_sub None 2015"
  by (oc_eval oc_nc_2015)

lemma upt_nc_125: "[2000..<2016] = [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]"
  by (simp add: upt_rec)

lemma sec_nc_125: "\<forall>j\<in>{16 * 125..<16 * 125 + 16}. oc_sub None j"
proof
  fix j :: nat assume "j \<in> {16 * 125..<16 * 125 + 16}"
  then have "j \<in> set [2000..<2016]" unfolding set_upt by simp
  then have "j \<in> set [2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015]" unfolding upt_nc_125 .
  then show "oc_sub None j" using oc_nc_2000 oc_nc_2001 oc_nc_2002 oc_nc_2003 oc_nc_2004 oc_nc_2005 oc_nc_2006 oc_nc_2007 oc_nc_2008 oc_nc_2009 oc_nc_2010 oc_nc_2011 oc_nc_2012 oc_nc_2013 oc_nc_2014 oc_nc_2015
    by (simp only: set_simps insert_iff empty_iff) (elim disjE FalseE; hypsubst; assumption)
qed

end

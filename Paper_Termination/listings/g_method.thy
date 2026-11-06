definition is_fpeak :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_fpeak p N c m \<longleftrightarrow> sq p N c m \<ge> sq p N c (prev_idx m) \<and> sq p N c m \<ge> sq p N c (next_idx m)
     \<and> (sq p N c m > sq p N c (prev_idx m) \<or> sq p N c m > sq p N c (next_idx m))"

definition fpeaks :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat set" where
  "fpeaks p N c = {m. m < M \<and> is_fpeak p N c m}"

definition fmains :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "fmains p N c t = {m \<in> fpeaks p N c. \<forall>q \<in> fpeaks p N c. cdist (grid m) t \<le> cdist (grid q) t}"

definition geligible :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat \<Rightarrow> complex)
    \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat set" where
  "geligible p N dl band c t m0 = {m \<in> fpeaks p N c. m \<noteq> m0 \<and> m \<noteq> prev_idx m0 \<and> m \<noteq> next_idx m0
      \<and> sq p N c m > sqmax p N c / 100 - dl \<and> in_band band t m}"

definition gelig :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat)
    \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "gelig p N dl band tm c t = geligible p N dl band c t (tm (fmains p N c t))"

primrec grun :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat)
    \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "grun p N dl band tm ts t 0 = c0 p t"
| "grun p N dl band tm ts t (Suc n) =
     (if gelig p N dl band tm (grun p N dl band tm ts t n) t = {} then grun p N dl band tm ts t n
      else corr p N (ts (sel p N (grun p N dl band tm ts t n) (gelig p N dl band tm (grun p N dl band tm ts t n) t)))
             (grun p N dl band tm ts t n))"

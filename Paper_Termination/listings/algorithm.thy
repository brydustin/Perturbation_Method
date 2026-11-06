definition sqmax :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real" where
  "sqmax p N c = Max ((sq p N c) ` {..<M})"

definition peaks :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat set" where
  "peaks p N c = {m. m < M \<and> is_peak p N c m}"

definition mains :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "mains p N c t = {m \<in> peaks p N c. \<forall>q \<in> peaks p N c. cdist (grid m) t \<le> cdist (grid q) t}"

definition in_band :: "real option \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "in_band band t m \<longleftrightarrow> (case band of None \<Rightarrow> True | Some \<Delta> \<Rightarrow> cdist (grid m) t > \<Delta>)"

definition eligible :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat set" where
  "eligible p N band c t m0 = {m \<in> peaks p N c. m \<noteq> m0 \<and> sq p N c m > sqmax p N c / 100 \<and> in_band band t m}"

definition sel :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> nat set \<Rightarrow> nat set" where
  "sel p N c E = {s \<in> E. \<forall>m \<in> E. sq p N c m \<le> sq p N c s}"

definition tie_rule :: "(nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> bool" where
  "tie_rule tm ts \<longleftrightarrow> (\<forall>S. S \<noteq> {} \<and> finite S \<longrightarrow> tm S \<in> S) \<and> (\<forall>S. S \<noteq> {} \<and> finite S \<longrightarrow> ts S \<in> S)"

definition elig :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> real \<Rightarrow> nat set" where
  "elig p N band tm c t = eligible p N band c t (tm (mains p N c t))"

primrec run :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "run p N band tm ts t 0 = c0 p t"
| "run p N band tm ts t (Suc n) =
     (if elig p N band tm (run p N band tm ts t n) t = {} then run p N band tm ts t n
      else corr p N (ts (sel p N (run p N band tm ts t n) (elig p N band tm (run p N band tm ts t n) t))) (run p N band tm ts t n))"

definition stops_within :: "(nat \<Rightarrow> real \<times> real) \<Rightarrow> nat \<Rightarrow> real option \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> (nat set \<Rightarrow> nat) \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> bool" where
  "stops_within p N band tm ts t D \<longleftrightarrow> (\<exists>n \<le> D. elig p N band tm (run p N band tm ts t n) t = {})"

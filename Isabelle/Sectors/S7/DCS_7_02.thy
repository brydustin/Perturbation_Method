theory DCS_7_02
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_120: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 120) (-8)) (Float (int 120 + 1) (-8))"
  by eval

lemma dc_nc_120: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 120) (-8)) (Float (int 120 + 1) (-8))"
  by eval

lemma dc_c30_121: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 121) (-8)) (Float (int 121 + 1) (-8))"
  by eval

lemma dc_nc_121: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 121) (-8)) (Float (int 121 + 1) (-8))"
  by eval

lemma dc_c30_122: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 122) (-8)) (Float (int 122 + 1) (-8))"
  by eval

lemma dc_nc_122: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 122) (-8)) (Float (int 122 + 1) (-8))"
  by eval

lemma dc_c30_123: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 123) (-8)) (Float (int 123 + 1) (-8))"
  by eval

lemma dc_nc_123: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 123) (-8)) (Float (int 123 + 1) (-8))"
  by eval

end

theory DCS_8_03
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_140: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 140) (-8)) (Float (int 140 + 1) (-8))"
  by eval

lemma dc_nc_140: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 140) (-8)) (Float (int 140 + 1) (-8))"
  by eval

lemma dc_c30_141: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 141) (-8)) (Float (int 141 + 1) (-8))"
  by eval

lemma dc_nc_141: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 141) (-8)) (Float (int 141 + 1) (-8))"
  by eval

lemma dc_c30_142: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 142) (-8)) (Float (int 142 + 1) (-8))"
  by eval

lemma dc_nc_142: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 142) (-8)) (Float (int 142 + 1) (-8))"
  by eval

lemma dc_c30_143: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 143) (-8)) (Float (int 143 + 1) (-8))"
  by eval

lemma dc_nc_143: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 143) (-8)) (Float (int 143 + 1) (-8))"
  by eval

end

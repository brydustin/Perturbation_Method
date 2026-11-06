theory DCS_8_01
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_132: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 132) (-8)) (Float (int 132 + 1) (-8))"
  by eval

lemma dc_nc_132: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 132) (-8)) (Float (int 132 + 1) (-8))"
  by eval

lemma dc_c30_133: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 133) (-8)) (Float (int 133 + 1) (-8))"
  by eval

lemma dc_nc_133: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 133) (-8)) (Float (int 133 + 1) (-8))"
  by eval

lemma dc_c30_134: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 134) (-8)) (Float (int 134 + 1) (-8))"
  by eval

lemma dc_nc_134: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 134) (-8)) (Float (int 134 + 1) (-8))"
  by eval

lemma dc_c30_135: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 135) (-8)) (Float (int 135 + 1) (-8))"
  by eval

lemma dc_nc_135: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 135) (-8)) (Float (int 135 + 1) (-8))"
  by eval

end

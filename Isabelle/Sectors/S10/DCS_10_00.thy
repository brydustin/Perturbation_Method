theory DCS_10_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_160: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 160) (-8)) (Float (int 160 + 1) (-8))"
  by eval

lemma dc_nc_160: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 160) (-8)) (Float (int 160 + 1) (-8))"
  by eval

lemma dc_c30_161: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 161) (-8)) (Float (int 161 + 1) (-8))"
  by eval

lemma dc_nc_161: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 161) (-8)) (Float (int 161 + 1) (-8))"
  by eval

lemma dc_c30_162: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 162) (-8)) (Float (int 162 + 1) (-8))"
  by eval

lemma dc_nc_162: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 162) (-8)) (Float (int 162 + 1) (-8))"
  by eval

lemma dc_c30_163: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 163) (-8)) (Float (int 163 + 1) (-8))"
  by eval

lemma dc_nc_163: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 163) (-8)) (Float (int 163 + 1) (-8))"
  by eval

end

theory DCS_8_00
  imports "Perturbative_Termination.Double_Cross" "Perturbative_Termination.Fast_Code"
begin

lemma dc_c30_128: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 128) (-8)) (Float (int 128 + 1) (-8))"
  by eval

lemma dc_nc_128: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 128) (-8)) (Float (int 128 + 1) (-8))"
  by eval

lemma dc_c30_129: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 129) (-8)) (Float (int 129 + 1) (-8))"
  by eval

lemma dc_nc_129: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 129) (-8)) (Float (int 129 + 1) (-8))"
  by eval

lemma dc_c30_130: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 130) (-8)) (Float (int 130 + 1) (-8))"
  by eval

lemma dc_nc_130: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 130) (-8)) (Float (int 130 + 1) (-8))"
  by eval

lemma dc_c30_131: "check_sector 53 dc_q 9 inv9_ivl (Some (band30 53)) 20 (Float 1 (-26)) 100 (Float (int 131) (-8)) (Float (int 131 + 1) (-8))"
  by eval

lemma dc_nc_131: "check_sector 53 dc_q 9 inv9_ivl (None) 20 (Float 1 (-26)) 100 (Float (int 131) (-8)) (Float (int 131 + 1) (-8))"
  by eval

end

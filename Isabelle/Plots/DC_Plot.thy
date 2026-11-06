theory DC_Plot
  imports Perturbative_Termination.Double_Cross Perturbative_Termination.Fast_Code
begin

text \<open>Polar plots of the double cross, drawn with plain characters in the output panel.  Pattern values and
  corrections come from the verified interval code (midpoints); peak choice is done in ML.\<close>

definition me :: "float \<Rightarrow> integer \<times> integer" where
  "me x = (integer_of_int (mantissa x), integer_of_int (exponent x))"

definition pl_kl :: "civ list list" where "pl_kl = kernelL 53 dc_q 9"

definition pl_step :: "civ list list \<Rightarrow> integer \<Rightarrow> civ list list" where
  "pl_step rl s = stepL 53 9 inv9_ivl pl_kl rl (nat_of_integer s)"

definition pl_sq :: "civ list list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> (integer \<times> integer) list" where
  "pl_sq rl tm te = map (\<lambda>I. me ((lower I + upper I) * Float 1 (-1)))
     (sqL 53 9 rl (c0L 53 dc_q 9 (interval_of (Float (int_of_integer tm) (int_of_integer te)))))"

ML \<open>
structure Polar =
struct
  val M = 1000
  val twopi = 2.0 * Math.pi
  fun grid m = twopi * real m / real M
  fun cdist a b = let val d = Real.rem (Real.abs (a - b), twopi) in Real.min (d, twopi - d) end
  fun toR (m, e) = Real.fromLargeInt m * Math.pow (2.0, real e)

  (* the method on midpoints: main lobe, eligible peaks, largest one *)
  fun peaks sq = List.filter (fn m =>
      let val a = Array.sub (sq, (m + M - 1) mod M) and b = Array.sub (sq, (m + 1) mod M)
      in Array.sub (sq, m) > a andalso Array.sub (sq, m) > b end) (List.tabulate (M, I))
  fun choose sq t band =
    let
      val ps = peaks sq
      val mx = Array.foldl Real.max 0.0 sq
      val d0 = List.foldl (fn (m, d) => Real.min (cdist (grid m) t, d)) 10.0 ps
      val m0 = the (List.find (fn m => Real.== (cdist (grid m) t, d0)) ps)
      val el = List.filter (fn m => m <> m0 andalso Array.sub (sq, m) > mx / 100.0
                                     andalso cdist (grid m) t > band) ps
    in case el of [] => NONE
       | _ => SOME (List.foldl (fn (m, s) => if Array.sub (sq, m) > Array.sub (sq, s) then m else s)
                               (hd el) el)
    end

  (* character canvas: one character per cell, cells twice as tall as wide *)
  val W = 85 and H = 43
  val cx = 42.0 and cy = 21.0 and R = 38.0
  fun canvas () = Array.tabulate (W * H, fn _ => 0)
  val glyph = Vector.fromList [#" ", #".", #":", #"*", #"x"]
  fun set cv p (x, y) =
    let val xi = Real.round x and yi = Real.round y in
      if xi < 0 orelse yi < 0 orelse xi >= W orelse yi >= H then () else
      let val i = yi * W + xi in if Array.sub (cv, i) < p then Array.update (cv, i, p) else () end
    end
  fun pt r a = (cx + r * Math.cos a, cy - 0.5 * r * Math.sin a)
  fun line cv p (x0, y0) (x1, y1) =
    let val n = Int.max (1, Real.ceil (Real.max (Real.abs (x1 - x0), 2.0 * Real.abs (y1 - y0))))
    in List.app (fn k => let val s = real k / real n in set cv p (x0 + s * (x1 - x0), y0 + s * (y1 - y0)) end)
         (List.tabulate (n + 1, I)) end
  fun ring cv r n = List.app (fn k => set cv 1 (pt r (twopi * real k / real n))) (List.tabulate (n, I))
  fun ray cv a = List.app (fn k => set cv 2 (pt (R * real k / 40.0) a)) (List.tabulate (41, fn k => k))
  fun render cv = List.tabulate (H, fn r =>
      String.implode (List.tabulate (W, fn c => Vector.sub (glyph, Array.sub (cv, r * W + c)))))

  val range = 40.0
  fun level mx v = if v <= 0.0 then ~range else Real.max (~range, 10.0 * Math.log10 (v / mx))
  fun rad mx v = R * (level mx v + range) / range
  fun draw sq t band nulls =
    let
      val cv = canvas ()
      val mx = Array.foldl Real.max 0.0 sq
      val _ = ring cv R 120
      val _ = ring cv (R * 0.5) 60
      val _ = (ray cv t; ray cv (t + band); ray cv (t - band))
      val ps = List.tabulate (M + 1, fn m => pt (rad mx (Array.sub (sq, m mod M))) (grid m))
      val _ = ListPair.app (fn (a, b) => line cv 3 a b) (ps, tl ps)
      val _ = List.app (fn s => set cv 4 (pt (R + 2.0) (grid s))) nulls
    in render cv end

  (* largest peak outside the band other than the main lobe: what the stopping test looks at *)
  fun sidelobe sq t band =
    let val mx = Array.foldl Real.max 0.0 sq
        val ps = peaks sq
        val d0 = List.foldl (fn (m, d) => Real.min (cdist (grid m) t, d)) 10.0 ps
        val out = List.filter (fn m => cdist (grid m) t > band andalso not (Real.== (cdist (grid m) t, d0))) ps
    in level mx (List.foldl (fn (m, v) => Real.max (Array.sub (sq, m), v)) 0.0 out) end

  fun deg a = Real.fmt (StringCvt.FIX (SOME 1)) (a * 180.0 / Math.pi)
  fun db v = String.translate (fn #"~" => "-" | c => String.str c) (Real.fmt (StringCvt.FIX (SOME 1)) v)
end
\<close>

ML \<open>
local
  open Polar
  (* edit the focus here (degrees); band 30 deg *)
  val focus_deg = 17.9
  val (tm, te) = (Real.round (focus_deg * Math.pi / 180.0 * 1073741824.0), ~30)
  val t = real tm * Math.pow (2.0, real te)
  val band = Math.pi / 6.0
  fun sqs rl = Array.fromList (map toR (@{code pl_sq} rl tm te))
  fun go rl k nulls frames =
    let val sq = sqs rl
        val frames' = (k, sq, rev nulls) :: frames
    in case (if k >= 25 then NONE else choose sq t band) of
         NONE => (k, rev frames')
       | SOME s => (writeln ("correction " ^ Int.toString (k + 1) ^ " at " ^ deg (grid s) ^ " deg, "
                              ^ db (level (Array.foldl Real.max 0.0 sq) (Array.sub (sq, s))) ^ " dB");
                    go (@{code pl_step} rl s) (k + 1) (s :: nulls) frames')
    end
  val timer = Timing.start ()
  val (n, frames) = go @{code pl_kl} 0 [] []
  fun show (k, sq, nulls) =
    writeln (cat_lines (
      ("Double cross, focus " ^ deg t ^ " deg, band +-30 deg, after " ^ Int.toString k ^ " corrections" ^
       "   (largest peak outside band: " ^ db (sidelobe sq t band) ^ " dB)") ::
      "* pattern;  . rings: outer 0 dB, inner -20 dB (stop threshold), centre -40 dB;  : focus and band edges;  x corrected angles" ::
      draw sq t band nulls))
in
  val _ = show (hd frames)
  val _ = show (List.last frames)
  val _ = writeln ("stopped after " ^ Int.toString n ^ " corrections; " ^ Timing.message (Timing.result timer))
end
\<close>

end

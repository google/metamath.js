include "wa.mm"
include "simp-6r.mm"
include "adantr.mm"

theorem simp-7r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si


  assert |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    wa
    wta
    wa
    wet
    wa
    wze
    wa
    wps
    wsi
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    simp-6r
    adantr
end

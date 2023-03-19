include "wa.mm"
include "simp-8r.mm"
include "adantr.mm"

theorem simp-9r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu


  assert |- ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps )

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
    wsi
    wa
    wrh
    wa
    wps
    wmu
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wsi
    wrh
    simp-8r
    adantr
end

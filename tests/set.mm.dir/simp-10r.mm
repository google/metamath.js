include "wa.mm"
include "simp-9r.mm"
include "adantr.mm"

theorem simp-10r
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
  let wla: wff la


  assert |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps )

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
    wmu
    wa
    wps
    wla
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wsi
    wrh
    wmu
    simp-9r
    adantr
end

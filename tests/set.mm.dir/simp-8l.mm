include "wa.mm"
include "simp-7l.mm"
include "adantr.mm"

theorem simp-8l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh


  assert |- ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ph )

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
    wph
    wrh
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wsi
    simp-7l
    adantr
end

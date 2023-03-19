include "wa.mm"
include "ad6antr.mm"
include "adantr.mm"

theorem ad7antr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) -> ps )

  proof
    wph
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
    wps
    wrh
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wsi
    ad2ant.1
    ad6antr
    adantr
end

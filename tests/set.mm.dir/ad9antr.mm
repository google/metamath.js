include "wa.mm"
include "ad8antr.mm"
include "adantr.mm"

theorem ad9antr
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
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps )

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
    ad2ant.1
    ad8antr
    adantr
end

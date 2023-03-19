include "wa.mm"
include "ad9antr.mm"
include "adantr.mm"

theorem ad10antr
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
  let wka: wff ka
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) -> ps )

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
    wla
    wa
    wps
    wka
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
    wla
    ad2ant.1
    ad9antr
    adantr
end

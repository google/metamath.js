include "wa.mm"
include "ad8antlr.mm"
include "adantr.mm"

theorem ad9antlr
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


  assert |- ( ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ps )

  proof
    wch
    wph
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
    ad8antlr
    adantr
end

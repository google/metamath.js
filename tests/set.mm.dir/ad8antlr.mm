include "wa.mm"
include "ad7antlr.mm"
include "adantr.mm"

theorem ad8antlr
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
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) -> ps )

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
    ad2ant.1
    ad7antlr
    adantr
end

include "wa.mm"
include "ad5antlr.mm"
include "adantr.mm"

theorem ad6antlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps )

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
    wps
    wsi
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    ad2ant.1
    ad5antlr
    adantr
end

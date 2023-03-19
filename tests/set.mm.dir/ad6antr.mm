include "wa.mm"
include "ad5antr.mm"
include "adantr.mm"

theorem ad6antr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) /\ si ) -> ps )

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
    ad5antr
    adantr
end

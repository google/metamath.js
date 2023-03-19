include "wa.mm"
include "ad4antr.mm"
include "adantr.mm"

theorem ad5antr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps )

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
    wps
    wze
    wph
    wps
    wch
    wth
    wta
    wet
    ad2ant.1
    ad4antr
    adantr
end

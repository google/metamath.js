include "w3a.mm"
include "wi.mm"
include "com52l.mm"
include "3imp.mm"
include "com3l.mm"

theorem imp5p
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3imp5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ph -> ( ps -> ( ( ch /\ th /\ ta ) -> et ) ) )

  proof
    wch
    wth
    wta
    w3a
    wph
    wps
    wet
    wch
    wth
    wta
    wph
    wps
    wet
    wi
    wi
    wph
    wps
    wch
    wth
    wta
    wet
    3imp5.1
    com52l
    3imp
    com3l
end

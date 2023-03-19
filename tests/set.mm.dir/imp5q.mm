include "wa.mm"
include "wi.mm"
include "imp.mm"
include "3impd.mm"

theorem imp5q
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume 3imp5.1: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )


  assert |- ( ( ph /\ ps ) -> ( ( ch /\ th /\ ta ) -> et ) )

  proof
    wph
    wps
    wa
    wch
    wth
    wta
    wet
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    wi
    3imp5.1
    imp
    3impd
end

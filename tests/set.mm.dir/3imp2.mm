include "w3a.mm"
include "3impd.mm"
include "imp.mm"

theorem 3imp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3imp1.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )

  proof
    wph
    wps
    wch
    wth
    w3a
    wta
    wph
    wps
    wch
    wth
    wta
    3imp1.1
    3impd
    imp
end

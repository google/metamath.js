include "w3a.mm"
include "wi.mm"
include "com4l.mm"
include "3imp.mm"
include "com12.mm"

theorem 3impd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3imp1.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ph -> ( ( ps /\ ch /\ th ) -> ta ) )

  proof
    wps
    wch
    wth
    w3a
    wph
    wta
    wps
    wch
    wth
    wph
    wta
    wi
    wph
    wps
    wch
    wth
    wta
    3imp1.1
    com4l
    3imp
    com12
end

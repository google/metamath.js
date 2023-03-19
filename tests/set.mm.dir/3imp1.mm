include "w3a.mm"
include "wi.mm"
include "3imp.mm"
include "imp.mm"

theorem 3imp1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3imp1.1: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    wi
    3imp1.1
    3imp
    imp
end

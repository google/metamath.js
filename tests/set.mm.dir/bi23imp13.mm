include "wi.mm"
include "biimpd.mm"
include "3imp.mm"

theorem bi23imp13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi23imp13.1: |- ( ph -> ( ps <-> ( ch -> th ) ) )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    bi23imp13.1
    biimpd
    3imp
end

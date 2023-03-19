include "wi.mm"
include "biimpi.mm"
include "3imp.mm"

theorem bi13imp23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bi13imp23.1: |- ( ph <-> ( ps -> ( ch -> th ) ) )


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
    wi
    bi13imp23.1
    biimpi
    3imp
end

include "wi.mm"
include "ex.mm"
include "imp32.mm"

theorem impr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume impr.1: |- ( ( ph /\ ps ) -> ( ch -> th ) )


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> th )

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
    impr.1
    ex
    imp32
end

include "wi.mm"
include "expd.mm"
include "imp.mm"

theorem expdimp
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume expd.1: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ( ph /\ ps ) -> ( ch -> th ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wph
    wps
    wch
    wth
    expd.1
    expd
    imp
end

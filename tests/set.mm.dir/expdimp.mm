include "wi.mm"
include "expd.mm"
include "imp.mm"

theorem expdimp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
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

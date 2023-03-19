include "expd.mm"
include "3imp.mm"

theorem 3impib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3impib.1: |- ( ph -> ( ( ps /\ ch ) -> th ) )


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
    3impib.1
    expd
    3imp
end

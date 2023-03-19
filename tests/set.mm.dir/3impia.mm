include "wi.mm"
include "ex.mm"
include "3imp.mm"

theorem 3impia
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3impia.1: |- ( ( ph /\ ps ) -> ( ch -> th ) )


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
    3impia.1
    ex
    3imp
end

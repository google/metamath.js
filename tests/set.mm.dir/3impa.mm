include "exp31.mm"
include "3imp.mm"

theorem 3impa
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3impa.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


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
    3impa.1
    exp31
    3imp
end

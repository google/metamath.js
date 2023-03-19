include "3exp.mm"
include "com23.mm"
include "3imp.mm"

theorem 3com23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ch /\ ps ) -> th )

  proof
    wph
    wch
    wps
    wth
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    3exp.1
    3exp
    com23
    3imp
end

include "com3l.mm"
include "3imp.mm"

theorem 3imp231
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3imp.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ( ps /\ ch /\ ph ) -> th )

  proof
    wps
    wch
    wph
    wth
    wph
    wps
    wch
    wth
    3imp.1
    com3l
    3imp
end

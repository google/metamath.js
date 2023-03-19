include "com13.mm"
include "3imp.mm"

theorem 3imp31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3imp.1: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ( ch /\ ps /\ ph ) -> th )

  proof
    wch
    wps
    wph
    wth
    wph
    wps
    wch
    wth
    3imp.1
    com13
    3imp
end

include "a1d.mm"
include "jcad.mm"

theorem jctird
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jctird.1: |- ( ph -> ( ps -> ch ) )
  assume jctird.2: |- ( ph -> th )


  assert |- ( ph -> ( ps -> ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    jctird.1
    wph
    wth
    wps
    jctird.2
    a1d
    jcad
end

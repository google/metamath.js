include "wa.mm"
include "pm3.2.mm"
include "syl6c.mm"

theorem jcad
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jcad.1: |- ( ph -> ( ps -> ch ) )
  assume jcad.2: |- ( ph -> ( ps -> th ) )


  assert |- ( ph -> ( ps -> ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wch
    wth
    wa
    jcad.1
    jcad.2
    wch
    wth
    pm3.2
    syl6c
end

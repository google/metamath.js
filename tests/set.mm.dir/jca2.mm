include "wi.mm"
include "a1i.mm"
include "jcad.mm"

theorem jca2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jca2.1: |- ( ph -> ( ps -> ch ) )
  assume jca2.2: |- ( ps -> th )


  assert |- ( ph -> ( ps -> ( ch /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    jca2.1
    wps
    wth
    wi
    wph
    jca2.2
    a1i
    jcad
end

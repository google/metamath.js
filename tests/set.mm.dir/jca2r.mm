include "wi.mm"
include "a1i.mm"
include "jcad.mm"

theorem jca2r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jca2r.1: |- ( ph -> ( ps -> ch ) )
  assume jca2r.2: |- ( ps -> th )


  assert |- ( ph -> ( ps -> ( th /\ ch ) ) )

  proof
    wph
    wps
    wth
    wch
    wps
    wth
    wi
    wph
    jca2r.2
    a1i
    jca2r.1
    jcad
end

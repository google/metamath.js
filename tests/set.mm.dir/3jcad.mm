include "w3a.mm"
include "wa.mm"
include "imp.mm"
include "3jca.mm"
include "ex.mm"

theorem 3jcad
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3jcad.1: |- ( ph -> ( ps -> ch ) )
  assume 3jcad.2: |- ( ph -> ( ps -> th ) )
  assume 3jcad.3: |- ( ph -> ( ps -> ta ) )


  assert |- ( ph -> ( ps -> ( ch /\ th /\ ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    w3a
    wph
    wps
    wa
    wch
    wth
    wta
    wph
    wps
    wch
    3jcad.1
    imp
    wph
    wps
    wth
    3jcad.2
    imp
    wph
    wps
    wta
    3jcad.3
    imp
    3jca
    ex
end

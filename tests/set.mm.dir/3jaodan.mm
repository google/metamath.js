include "w3o.mm"
include "ex.mm"
include "3jaod.mm"
include "imp.mm"

theorem 3jaodan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3jaodan.1: |- ( ( ph /\ ps ) -> ch )
  assume 3jaodan.2: |- ( ( ph /\ th ) -> ch )
  assume 3jaodan.3: |- ( ( ph /\ ta ) -> ch )


  assert |- ( ( ph /\ ( ps \/ th \/ ta ) ) -> ch )

  proof
    wph
    wps
    wth
    wta
    w3o
    wch
    wph
    wps
    wch
    wth
    wta
    wph
    wps
    wch
    3jaodan.1
    ex
    wph
    wth
    wch
    3jaodan.2
    ex
    wph
    wta
    wch
    3jaodan.3
    ex
    3jaod
    imp
end

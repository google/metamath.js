include "w3o.mm"
include "wi.mm"
include "ex.mm"
include "3jaoi.mm"
include "imp.mm"

theorem 3jaoian
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3jaoian.1: |- ( ( ph /\ ps ) -> ch )
  assume 3jaoian.2: |- ( ( th /\ ps ) -> ch )
  assume 3jaoian.3: |- ( ( ta /\ ps ) -> ch )


  assert |- ( ( ( ph \/ th \/ ta ) /\ ps ) -> ch )

  proof
    wph
    wth
    wta
    w3o
    wps
    wch
    wph
    wps
    wch
    wi
    wth
    wta
    wph
    wps
    wch
    3jaoian.1
    ex
    wth
    wps
    wch
    3jaoian.2
    ex
    wta
    wps
    wch
    3jaoian.3
    ex
    3jaoi
    imp
end

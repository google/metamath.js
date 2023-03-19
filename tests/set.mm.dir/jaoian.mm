include "wo.mm"
include "wi.mm"
include "ex.mm"
include "jaoi.mm"
include "imp.mm"

theorem jaoian
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jaoian.1: |- ( ( ph /\ ps ) -> ch )
  assume jaoian.2: |- ( ( th /\ ps ) -> ch )


  assert |- ( ( ( ph \/ th ) /\ ps ) -> ch )

  proof
    wph
    wth
    wo
    wps
    wch
    wph
    wps
    wch
    wi
    wth
    wph
    wps
    wch
    jaoian.1
    ex
    wth
    wps
    wch
    jaoian.2
    ex
    jaoi
    imp
end

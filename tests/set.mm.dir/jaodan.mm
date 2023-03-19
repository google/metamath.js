include "wo.mm"
include "ex.mm"
include "jaod.mm"
include "imp.mm"

theorem jaodan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jaodan.1: |- ( ( ph /\ ps ) -> ch )
  assume jaodan.2: |- ( ( ph /\ th ) -> ch )


  assert |- ( ( ph /\ ( ps \/ th ) ) -> ch )

  proof
    wph
    wps
    wth
    wo
    wch
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    jaodan.1
    ex
    wph
    wth
    wch
    jaodan.2
    ex
    jaod
    imp
end

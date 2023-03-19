include "wo.mm"
include "jaodan.mm"
include "mpdan.mm"

theorem mpjaodan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jaodan.1: |- ( ( ph /\ ps ) -> ch )
  assume jaodan.2: |- ( ( ph /\ th ) -> ch )
  assume jaodan.3: |- ( ph -> ( ps \/ th ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wth
    wo
    wch
    jaodan.3
    wph
    wps
    wch
    wth
    jaodan.1
    jaodan.2
    jaodan
    mpdan
end

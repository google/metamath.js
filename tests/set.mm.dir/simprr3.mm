include "w3a.mm"
include "wa.mm"
include "simpr3.mm"
include "adantl.mm"

theorem simprr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wch
    wta
    wth
    wph
    wps
    wch
    simpr3
    adantl
end

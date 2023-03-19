include "w3a.mm"
include "wa.mm"
include "simpr2.mm"
include "adantl.mm"

theorem simprr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wps
    wta
    wth
    wph
    wps
    wch
    simpr2
    adantl
end

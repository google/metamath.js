include "w3a.mm"
include "wa.mm"
include "simpr1.mm"
include "adantl.mm"

theorem simprr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ph )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wph
    wta
    wth
    wph
    wps
    wch
    simpr1
    adantl
end

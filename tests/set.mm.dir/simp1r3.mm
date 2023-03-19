include "w3a.mm"
include "wa.mm"
include "simpr3.mm"
include "3ad2ant1.mm"

theorem simp1r3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta /\ et ) -> ch )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wta
    wch
    wet
    wth
    wph
    wps
    wch
    simpr3
    3ad2ant1
end

include "w3a.mm"
include "wa.mm"
include "simpr3.mm"
include "3ad2ant3.mm"

theorem simp3r3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ch )

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
    3ad2ant3
end

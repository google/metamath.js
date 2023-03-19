include "w3a.mm"
include "wa.mm"
include "simpr2.mm"
include "3ad2ant3.mm"

theorem simp3r2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ et /\ ( th /\ ( ph /\ ps /\ ch ) ) ) -> ps )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wta
    wps
    wet
    wth
    wph
    wps
    wch
    simpr2
    3ad2ant3
end

include "w3a.mm"
include "wa.mm"
include "simpr1.mm"
include "3ad2ant2.mm"

theorem simp2r1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ ( th /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ph )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wta
    wph
    wet
    wth
    wph
    wps
    wch
    simpr1
    3ad2ant2
end

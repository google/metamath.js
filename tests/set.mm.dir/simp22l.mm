include "wa.mm"
include "w3a.mm"
include "simp2l.mm"
include "3ad2ant2.mm"

theorem simp22l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) /\ et ) -> ph )

  proof
    wch
    wph
    wps
    wa
    wth
    w3a
    wta
    wph
    wet
    wch
    wph
    wps
    wth
    simp2l
    3ad2ant2
end

include "wa.mm"
include "w3a.mm"
include "simp3l.mm"
include "3ad2ant2.mm"

theorem simp23l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ph )

  proof
    wch
    wth
    wph
    wps
    wa
    w3a
    wta
    wph
    wet
    wch
    wth
    wph
    wps
    simp3l
    3ad2ant2
end

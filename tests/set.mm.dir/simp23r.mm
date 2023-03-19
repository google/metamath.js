include "wa.mm"
include "w3a.mm"
include "simp3r.mm"
include "3ad2ant2.mm"

theorem simp23r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) /\ et ) -> ps )

  proof
    wch
    wth
    wph
    wps
    wa
    w3a
    wta
    wps
    wet
    wch
    wth
    wph
    wps
    simp3r
    3ad2ant2
end

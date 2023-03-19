include "wa.mm"
include "w3a.mm"
include "simp3r.mm"
include "3ad2ant1.mm"

theorem simp13r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta /\ et ) -> ps )

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
    3ad2ant1
end

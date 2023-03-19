include "wa.mm"
include "w3a.mm"
include "simp3r.mm"
include "3ad2ant3.mm"

theorem simp33r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ et /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps )

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
    3ad2ant3
end

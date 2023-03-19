include "wa.mm"
include "w3a.mm"
include "simp2r.mm"
include "3ad2ant3.mm"

theorem simp32r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ et /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ps )

  proof
    wch
    wph
    wps
    wa
    wth
    w3a
    wta
    wps
    wet
    wch
    wph
    wps
    wth
    simp2r
    3ad2ant3
end

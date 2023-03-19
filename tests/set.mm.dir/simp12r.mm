include "wa.mm"
include "w3a.mm"
include "simp2r.mm"
include "3ad2ant1.mm"

theorem simp12r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta /\ et ) -> ps )

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
    3ad2ant1
end

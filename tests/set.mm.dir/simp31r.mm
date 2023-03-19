include "wa.mm"
include "w3a.mm"
include "simp1r.mm"
include "3ad2ant3.mm"

theorem simp31r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ta /\ et /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wth
    w3a
    wta
    wps
    wet
    wph
    wps
    wch
    wth
    simp1r
    3ad2ant3
end

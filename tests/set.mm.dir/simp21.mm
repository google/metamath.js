include "w3a.mm"
include "simp1.mm"
include "3ad2ant2.mm"

theorem simp21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ps )

  proof
    wps
    wch
    wth
    w3a
    wph
    wps
    wta
    wps
    wch
    wth
    simp1
    3ad2ant2
end

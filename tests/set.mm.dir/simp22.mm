include "w3a.mm"
include "simp2.mm"
include "3ad2ant2.mm"

theorem simp22
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> ch )

  proof
    wps
    wch
    wth
    w3a
    wph
    wch
    wta
    wps
    wch
    wth
    simp2
    3ad2ant2
end

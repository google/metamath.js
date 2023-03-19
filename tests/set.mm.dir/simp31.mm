include "w3a.mm"
include "simp1.mm"
include "3ad2ant3.mm"

theorem simp31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ch )

  proof
    wch
    wth
    wta
    w3a
    wph
    wch
    wps
    wch
    wth
    wta
    simp1
    3ad2ant3
end

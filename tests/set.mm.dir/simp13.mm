include "w3a.mm"
include "simp3.mm"
include "3ad2ant1.mm"

theorem simp13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wth
    wch
    wta
    wph
    wps
    wch
    simp3
    3ad2ant1
end

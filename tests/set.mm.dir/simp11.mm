include "w3a.mm"
include "simp1.mm"
include "3ad2ant1.mm"

theorem simp11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) -> ph )

  proof
    wph
    wps
    wch
    w3a
    wth
    wph
    wta
    wph
    wps
    wch
    simp1
    3ad2ant1
end

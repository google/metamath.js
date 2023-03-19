include "w3a.mm"
include "simp2.mm"
include "3ad2ant3.mm"

theorem simp32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> th )

  proof
    wch
    wth
    wta
    w3a
    wph
    wth
    wps
    wch
    wth
    wta
    simp2
    3ad2ant3
end

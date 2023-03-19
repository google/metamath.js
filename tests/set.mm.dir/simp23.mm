include "w3a.mm"
include "simp3.mm"
include "3ad2ant2.mm"

theorem simp23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) /\ ta ) -> th )

  proof
    wps
    wch
    wth
    w3a
    wph
    wth
    wta
    wps
    wch
    wth
    simp3
    3ad2ant2
end

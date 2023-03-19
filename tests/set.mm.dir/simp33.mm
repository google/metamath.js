include "w3a.mm"
include "simp3.mm"
include "3ad2ant3.mm"

theorem simp33
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph /\ ps /\ ( ch /\ th /\ ta ) ) -> ta )

  proof
    wch
    wth
    wta
    w3a
    wph
    wta
    wps
    wch
    wth
    wta
    simp3
    3ad2ant3
end

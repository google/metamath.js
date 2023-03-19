include "w3a.mm"
include "simp13.mm"
include "3ad2ant1.mm"

theorem simp113
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    w3a
    wet
    wch
    wze
    wph
    wps
    wch
    wth
    wta
    simp13
    3ad2ant1
end

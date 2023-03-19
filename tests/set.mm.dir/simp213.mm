include "w3a.mm"
include "simp13.mm"
include "3ad2ant2.mm"

theorem simp213
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ ze ) -> ch )

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
    3ad2ant2
end

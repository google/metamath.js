include "w3a.mm"
include "simp22.mm"
include "3ad2ant2.mm"

theorem simp222
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ ze ) -> ps )

  proof
    wth
    wph
    wps
    wch
    w3a
    wta
    w3a
    wet
    wps
    wze
    wth
    wph
    wps
    wch
    wta
    simp22
    3ad2ant2
end

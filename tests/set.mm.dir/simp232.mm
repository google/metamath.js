include "w3a.mm"
include "simp32.mm"
include "3ad2ant2.mm"

theorem simp232
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ ze ) -> ps )

  proof
    wth
    wta
    wph
    wps
    wch
    w3a
    w3a
    wet
    wps
    wze
    wth
    wta
    wph
    wps
    wch
    simp32
    3ad2ant2
end

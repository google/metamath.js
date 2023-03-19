include "w3a.mm"
include "simp12.mm"
include "3ad2ant1.mm"

theorem simp112
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et /\ ze ) -> ps )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    w3a
    wet
    wps
    wze
    wph
    wps
    wch
    wth
    wta
    simp12
    3ad2ant1
end

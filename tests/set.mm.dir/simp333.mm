include "w3a.mm"
include "simp33.mm"
include "3ad2ant3.mm"

theorem simp333
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( et /\ ze /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch )

  proof
    wth
    wta
    wph
    wps
    wch
    w3a
    w3a
    wet
    wch
    wze
    wth
    wta
    wph
    wps
    wch
    simp33
    3ad2ant3
end

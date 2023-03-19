include "w3a.mm"
include "simp23.mm"
include "3ad2ant3.mm"

theorem simp323
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( et /\ ze /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch )

  proof
    wth
    wph
    wps
    wch
    w3a
    wta
    w3a
    wet
    wch
    wze
    wth
    wph
    wps
    wch
    wta
    simp23
    3ad2ant3
end

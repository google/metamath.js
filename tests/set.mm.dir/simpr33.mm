include "w3a.mm"
include "simp33.mm"
include "adantl.mm"

theorem simpr33
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ch )

  proof
    wth
    wta
    wph
    wps
    wch
    w3a
    w3a
    wch
    wet
    wth
    wta
    wph
    wps
    wch
    simp33
    adantl
end

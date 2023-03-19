include "w3a.mm"
include "simp23.mm"
include "adantl.mm"

theorem simpr23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( et /\ ( th /\ ( ph /\ ps /\ ch ) /\ ta ) ) -> ch )

  proof
    wth
    wph
    wps
    wch
    w3a
    wta
    w3a
    wch
    wet
    wth
    wph
    wps
    wch
    wta
    simp23
    adantl
end

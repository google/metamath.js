include "w3a.mm"
include "simp13.mm"
include "adantl.mm"

theorem simpr13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( et /\ ( ( ph /\ ps /\ ch ) /\ th /\ ta ) ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    w3a
    wch
    wet
    wph
    wps
    wch
    wth
    wta
    simp13
    adantl
end

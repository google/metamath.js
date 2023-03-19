include "w3a.mm"
include "simp31.mm"
include "adantl.mm"

theorem simpr31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ph )

  proof
    wth
    wta
    wph
    wps
    wch
    w3a
    w3a
    wph
    wet
    wth
    wta
    wph
    wps
    wch
    simp31
    adantl
end

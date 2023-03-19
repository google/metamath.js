include "w3a.mm"
include "simp32.mm"
include "adantl.mm"

theorem simpr32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( et /\ ( th /\ ta /\ ( ph /\ ps /\ ch ) ) ) -> ps )

  proof
    wth
    wta
    wph
    wps
    wch
    w3a
    w3a
    wps
    wet
    wth
    wta
    wph
    wps
    wch
    simp32
    adantl
end

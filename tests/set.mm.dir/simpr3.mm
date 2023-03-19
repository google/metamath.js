include "w3a.mm"
include "simp3.mm"
include "adantl.mm"

theorem simpr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> th )

  proof
    wps
    wch
    wth
    w3a
    wth
    wph
    wps
    wch
    wth
    simp3
    adantl
end

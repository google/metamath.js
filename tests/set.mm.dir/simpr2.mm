include "w3a.mm"
include "simp2.mm"
include "adantl.mm"

theorem simpr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ch )

  proof
    wps
    wch
    wth
    w3a
    wch
    wph
    wps
    wch
    wth
    simp2
    adantl
end

include "w3a.mm"
include "simp1.mm"
include "adantl.mm"

theorem simpr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ps )

  proof
    wps
    wch
    wth
    w3a
    wps
    wph
    wps
    wch
    wth
    simp1
    adantl
end

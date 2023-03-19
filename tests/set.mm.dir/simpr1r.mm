include "wa.mm"
include "w3a.mm"
include "simp1r.mm"
include "adantl.mm"

theorem simpr1r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wth
    w3a
    wps
    wta
    wph
    wps
    wch
    wth
    simp1r
    adantl
end

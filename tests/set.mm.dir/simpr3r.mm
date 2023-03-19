include "wa.mm"
include "w3a.mm"
include "simp3r.mm"
include "adantl.mm"

theorem simpr3r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ps )

  proof
    wch
    wth
    wph
    wps
    wa
    w3a
    wps
    wta
    wch
    wth
    wph
    wps
    simp3r
    adantl
end

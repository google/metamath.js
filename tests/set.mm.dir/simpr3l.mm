include "wa.mm"
include "w3a.mm"
include "simp3l.mm"
include "adantl.mm"

theorem simpr3l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ch /\ th /\ ( ph /\ ps ) ) ) -> ph )

  proof
    wch
    wth
    wph
    wps
    wa
    w3a
    wph
    wta
    wch
    wth
    wph
    wps
    simp3l
    adantl
end

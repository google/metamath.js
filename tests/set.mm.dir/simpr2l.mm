include "wa.mm"
include "w3a.mm"
include "simp2l.mm"
include "adantl.mm"

theorem simpr2l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ch /\ ( ph /\ ps ) /\ th ) ) -> ph )

  proof
    wch
    wph
    wps
    wa
    wth
    w3a
    wph
    wta
    wch
    wph
    wps
    wth
    simp2l
    adantl
end

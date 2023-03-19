include "wa.mm"
include "w3a.mm"
include "simp1l.mm"
include "adantl.mm"

theorem simpr1l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ( ph /\ ps ) /\ ch /\ th ) ) -> ph )

  proof
    wph
    wps
    wa
    wch
    wth
    w3a
    wph
    wta
    wph
    wps
    wch
    wth
    simp1l
    adantl
end

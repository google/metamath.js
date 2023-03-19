include "wa.mm"
include "simprr.mm"
include "3ad2ant3.mm"

theorem simp3rr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( th /\ ta /\ ( ch /\ ( ph /\ ps ) ) ) -> ps )

  proof
    wch
    wph
    wps
    wa
    wa
    wth
    wps
    wta
    wch
    wph
    wps
    simprr
    3ad2ant3
end
